//! Small, ordered rewrite rules with a bounded local fixed point.
//!
//! Entry facts are invalidated by writes. Loop bodies retain only invariant
//! facts. Each successful rewrite restarts rule selection; a recognizer can
//! therefore rely on shapes established by earlier, independent rules.

use std::{collections::HashMap, fmt::Write};

use super::{
    arithmetic::{Bindings, Context, Kind, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, Program, VariableId, field_address},
    shapes::{self, LoopAnalysis},
};

#[derive(Debug, Clone, Copy)]
pub struct Options {
    /// Allow rewrites that rely on assumptions about otherwise unknown values.
    pub allow_assumptions: bool,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            allow_assumptions: true,
        }
    }
}

#[derive(Debug)]
pub struct Rewrite {
    pub offset: usize,
    pub rule: &'static str,
}

#[derive(Debug, Default)]
pub struct Report {
    pub before: Vec<LoopAnalysis>,
    pub rewrites: Vec<Rewrite>,
    pub remaining: Vec<LoopAnalysis>,
    pub budget_exhausted: bool,
}

#[derive(Clone, Default)]
struct Facts {
    conditions: Vec<Value>,
    /// A variable last loaded from an address that has not since been written.
    loaded_from: HashMap<VariableId, IRExpr>,
}

fn access(address: &IRExpr) -> Option<(&IRExpr, usize, usize)> {
    let IRExpr::MemoryAddress {
        address,
        size: Some(size),
    } = address
    else {
        return None;
    };
    let (base, offset) = field_address(address)?;
    Some((base, offset, offset.checked_add(*size)?))
}

fn disjoint_accesses(left: &IRExpr, right: &IRExpr) -> bool {
    let (Some((left_base, left_start, left_end)), Some((right_base, right_start, right_end))) =
        (access(left), access(right))
    else {
        return false;
    };
    left_base == right_base && (left_end <= right_start || right_end <= left_start)
}

fn writes_disjoint(instr: &IRInst, address: &IRExpr) -> bool {
    match instr {
        IRInst::Assign {
            dest: IRExpr::Deref(written),
            ..
        }
        | IRInst::CompoundAssign {
            dest: IRExpr::Deref(written),
            ..
        } => disjoint_accesses(address, written),
        IRInst::StoreVariable {
            address: written, ..
        } => disjoint_accesses(address, written),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .all(|instr| writes_disjoint(instr, address)),
        IRInst::While { body, .. } => body
            .iter()
            .all(|(_, instr)| writes_disjoint(instr, address)),
        _ => {
            let mut effects = Effects::default();
            effects.instruction(instr);
            !effects.memory_write && !effects.unknown_write
        }
    }
}

impl Facts {
    fn assume(&mut self, expression: &IRExpr, truth: bool, context: &Context) {
        if repeatable(expression) {
            let value = context.value(expression);
            self.conditions
                .push(if truth { value } else { value.negated() });
        }
    }

    fn invalidate(&mut self, effects: &Effects, writes_disjoint: impl Fn(&IRExpr) -> bool) {
        if effects.unknown_write {
            self.conditions.clear();
            self.loaded_from.clear();
            return;
        }
        self.conditions
            .retain(|fact| !effects.writes.iter().any(|variable| fact.reads(*variable)));
        self.loaded_from.retain(|variable, address| {
            (!effects.memory_write || writes_disjoint(address))
                && !effects.writes.contains(variable)
                && !effects
                    .writes
                    .iter()
                    .any(|written| Effects::of_expression(address).reads.contains(written))
        });
    }

    fn observe(&mut self, instr: &IRInst) {
        let loaded = match instr {
            IRInst::AssignVariable {
                variable,
                value: IRExpr::Deref(address),
            }
            | IRInst::DeclareAndAssignVariable {
                variable,
                value: IRExpr::Deref(address),
                ..
            }
            | IRInst::Assign {
                dest: IRExpr::Variable(variable),
                src: IRExpr::Deref(address),
            } => Some((*variable, address.as_ref())),
            IRInst::LoadVariable { variable, address } => Some((*variable, address)),
            _ => None,
        };
        if let Some((variable, address)) = loaded
            && repeatable(address)
            && !Effects::of_expression(address).reads.contains(&variable)
        {
            self.loaded_from.insert(variable, address.clone());
        }
    }

    fn destination_contains(&self, destination: &IRExpr, dividend: &IRExpr) -> bool {
        match (destination, dividend) {
            (IRExpr::Variable(destination), IRExpr::Variable(dividend)) => destination == dividend,
            (IRExpr::Deref(address), IRExpr::Variable(variable)) => {
                self.loaded_from.get(variable) == Some(address.as_ref())
            }
            _ => false,
        }
    }

    fn is_zero(&self, value: &Value) -> Option<bool> {
        if let Kind::Constant(constant) = value.kind {
            return Some(constant == 0);
        }
        self.conditions.iter().find_map(|fact| {
            let Kind::Binary { kind, lhs, rhs } = &fact.kind else {
                return None;
            };
            if (lhs.as_ref() == value && matches!(rhs.kind, Kind::Constant(0)))
                || (rhs.as_ref() == value && matches!(lhs.kind, Kind::Constant(0)))
            {
                match kind {
                    IRBinOpKind::Eq => Some(true),
                    IRBinOpKind::Ne => Some(false),
                    _ => None,
                }
            } else {
                None
            }
        })
    }
}

struct Rule {
    name: &'static str,
    apply: fn(&mut IRInst, usize, &Context, &Facts, &Options) -> Option<usize>,
}

const RULES: &[Rule] = &[
    Rule {
        name: "boolean-branch-to-return",
        apply: recover_boolean_return,
    },
    Rule {
        name: "guarded-do-to-while",
        apply: rotate_guarded_loop,
    },
    Rule {
        name: "repeated-subtraction-to-remainder",
        apply: recover_remainder,
    },
    Rule {
        name: "eliminate-guarded-modulo",
        apply: eliminate_guarded_modulo,
    },
    Rule {
        name: "compound-assignment",
        apply: recover_compound_assignment,
    },
    Rule {
        name: "de-morgan",
        apply: simplify_boolean_chains,
    },
];

fn simplify_boolean_expression(expr: &mut IRExpr) -> bool {
    let mut changed = match expr {
        IRExpr::BinOp { lhs, rhs, .. } => {
            let left_changed = simplify_boolean_expression(lhs);
            let right_changed = simplify_boolean_expression(rhs);
            left_changed || right_changed
        }
        IRExpr::Deref(inner)
        | IRExpr::MemoryAddress { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => simplify_boolean_expression(inner),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => false,
    };
    if let Some(replacement) = shapes::de_morgan(expr) {
        *expr = replacement;
        changed = true;
    }
    changed
}

fn simplify_boolean_chains(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let changed = match instr {
        IRInst::Assign { dest, src } => {
            let dest_changed = simplify_boolean_expression(dest);
            let src_changed = simplify_boolean_expression(src);
            dest_changed || src_changed
        }
        IRInst::CompoundAssign { dest, value, .. } => {
            let dest_changed = simplify_boolean_expression(dest);
            let value_changed = simplify_boolean_expression(value);
            dest_changed || value_changed
        }
        IRInst::Return(Some(value))
        | IRInst::DeclareAndAssignVariable { value, .. }
        | IRInst::AssignVariable { value, .. }
        | IRInst::Jump(value)
        | IRInst::LoadVariable { address: value, .. }
        | IRInst::StoreVariable { address: value, .. } => simplify_boolean_expression(value),
        IRInst::If { condition, .. } => simplify_boolean_expression(condition),
        IRInst::While { condition, .. } => {
            let (LoopCondition::Before { expression, .. }
            | LoopCondition::After { expression, .. }) = condition;
            simplify_boolean_expression(expression)
        }
        IRInst::CallSynthetic { arguments, .. } => {
            arguments.iter_mut().fold(false, |changed, argument| {
                simplify_boolean_expression(argument) || changed
            })
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => false,
    };
    changed.then_some(offset)
}

fn recover_boolean_return(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let value = shapes::boolean_return(instr)?;
    *instr = IRInst::Return(Some(value));
    Some(offset)
}

fn eliminate_guarded_modulo(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let shape = shapes::guarded_modulo(instr, context)?;
    if !facts.destination_contains(&shape.destination, &shape.dividend) {
        return None;
    }
    // On the skipped path dividend < stride, so the stride is nonzero and
    // dividend % stride is dividend. The destination already holds it.
    *instr = shape.replacement;
    Some(offset)
}

fn recover_compound_assignment(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let shape = shapes::compound_assignment(instr)?;
    *instr = IRInst::CompoundAssign {
        dest: shape.dest,
        kind: shape.kind,
        value: shape.value,
    };
    Some(offset)
}

fn rotate_guarded_loop(
    instr: &mut IRInst,
    _offset: usize,
    context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let IRInst::If {
        condition,
        then_branch,
        else_branch,
    } = instr
    else {
        return None;
    };
    if !repeatable(condition) {
        return None;
    }
    fn branch(branch: &mut [IRInst], guard: &Value, context: &Context) -> Option<usize> {
        let mut bindings = Bindings::new();
        for instr in branch {
            match instr {
                // Only a prefix of fresh local declarations may separate the
                // guard from the loop. Capture their values at the declaration.
                IRInst::DeclareAndAssignVariable {
                    variable, value, ..
                } if repeatable(value) => {
                    if guard.reads(*variable)
                        || bindings.values().any(|value| value.reads(*variable))
                    {
                        return None;
                    }
                    let value = context.with_bindings(value, &bindings);
                    let destination = context.value(&IRExpr::Variable(*variable));
                    if destination.bits != value.bits {
                        return None;
                    }
                    bindings.insert(*variable, value);
                }
                IRInst::While {
                    label: None,
                    condition,
                    body,
                    entry_offset,
                } => {
                    let LoopCondition::After { offset, expression } = condition else {
                        return None;
                    };
                    if !repeatable(expression)
                        || context.with_bindings(expression, &bindings) != *guard
                    {
                        return None;
                    }
                    // Continue in earlier tiers can bypass a trailing check.
                    // Nested control flow requires a separate rotation proof.
                    let mut effects = Effects::default();
                    for (_, instr) in body {
                        effects.instruction(instr);
                    }
                    if effects.control {
                        return None;
                    }
                    *condition = LoopCondition::Before {
                        offset: *offset,
                        expression: expression.clone(),
                    };
                    return Some(*entry_offset);
                }
                _ => return None,
            }
        }
        None
    }
    let guard = context.value(condition);
    branch(then_branch, &guard, context).or_else(|| branch(else_branch, &guard.negated(), context))
}

fn recover_remainder(
    instr: &mut IRInst,
    _offset: usize,
    context: &Context,
    facts: &Facts,
    options: &Options,
) -> Option<usize> {
    let analysis = shapes::analyze(instr, context)?;
    let shape = analysis.subtraction?;
    if !shape.blockers.is_empty() {
        return None;
    }
    match facts.is_zero(&shape.stride) {
        Some(true) => return None,
        None if !options.allow_assumptions => return None,
        _ => {}
    }
    // A zero stride makes this matched loop nonterminating. Recover the
    // operation for terminating executions, where the stride is nonzero.
    *instr = IRInst::AssignVariable {
        variable: shape.accumulator,
        value: IRExpr::BinOp {
            kind: IRBinOpKind::UnsignedMod,
            lhs: Box::new(IRExpr::Variable(shape.accumulator)),
            rhs: Box::new(shape.stride_source),
        },
    };
    Some(analysis.offset)
}

const MAX_REWRITES: usize = 256;
const MAX_LOCAL_ROUNDS: usize = 16;

trait InstructionSlot {
    fn instruction(&self) -> &IRInst;
    fn instruction_mut(&mut self) -> &mut IRInst;
    fn offset(&self, fallback: usize) -> usize;
}

impl InstructionSlot for IRInst {
    fn instruction(&self) -> &IRInst {
        self
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        self
    }

    fn offset(&self, fallback: usize) -> usize {
        fallback
    }
}

impl InstructionSlot for (usize, IRInst) {
    fn instruction(&self) -> &IRInst {
        &self.1
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        &mut self.1
    }

    fn offset(&self, _fallback: usize) -> usize {
        self.0
    }
}

#[derive(Default)]
struct VariableUses {
    reads: usize,
    writes: usize,
}

fn add_uses(effects: &Effects, uses: &mut HashMap<VariableId, VariableUses>) {
    for variable in &effects.reads {
        uses.entry(*variable).or_default().reads += 1;
    }
    for variable in &effects.writes {
        uses.entry(*variable).or_default().writes += 1;
    }
}

fn collect_uses(instr: &IRInst, uses: &mut HashMap<VariableId, VariableUses>) {
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            add_uses(&Effects::of_expression(condition), uses);
            for instr in then_branch.iter().chain(else_branch) {
                collect_uses(instr, uses);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            let (LoopCondition::Before { expression, .. }
            | LoopCondition::After { expression, .. }) = condition;
            add_uses(&Effects::of_expression(expression), uses);
            for (_, instr) in body {
                collect_uses(instr, uses);
            }
        }
        _ => {
            let mut effects = Effects::default();
            effects.instruction(instr);
            add_uses(&effects, uses);
        }
    }
}

fn collapse_temporary_assignments<T: InstructionSlot>(
    instructions: &mut Vec<T>,
    fallback_offset: usize,
    context: &Context,
    uses: &HashMap<VariableId, VariableUses>,
    report: &mut Report,
) {
    for slot in instructions.iter_mut() {
        let offset = slot.offset(fallback_offset);
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                collapse_temporary_assignments(then_branch, offset, context, uses, report);
                collapse_temporary_assignments(else_branch, offset, context, uses, report);
            }
            IRInst::While { body, .. } => {
                collapse_temporary_assignments(body, offset, context, uses, report);
            }
            _ => {}
        }
    }
    let mut index = 0;
    while index + 2 < instructions.len() {
        if report.rewrites.len() >= MAX_REWRITES {
            report.budget_exhausted = true;
            return;
        }
        let shape = shapes::temporary_binary_assignment(
            instructions[index].instruction(),
            instructions[index + 1].instruction(),
            instructions[index + 2].instruction(),
            context,
        );
        if let Some(shape) = shape
            && matches!(
                uses.get(&shape.temporary),
                Some(VariableUses {
                    reads: 2,
                    writes: 2,
                })
            )
        {
            let offset = instructions[index + 2].offset(fallback_offset);
            *instructions[index + 2].instruction_mut() = shape.replacement;
            instructions.drain(index..index + 2);
            report.rewrites.push(Rewrite {
                offset,
                rule: "temporary-binary-to-assignment",
            });
        } else {
            index += 1;
        }
    }
}

fn sequence<'a>(
    instructions: impl Iterator<Item = (usize, &'a mut IRInst)>,
    context: &Context,
    mut facts: Facts,
    options: &Options,
    report: &mut Report,
) {
    for (offset, instr) in instructions {
        rewrite(instr, offset, context, &facts, options, report);
        let mut effects = Effects::default();
        effects.instruction(instr);
        facts.invalidate(&effects, |address| writes_disjoint(instr, address));
        facts.observe(instr);
    }
}

fn rewrite_local(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    options: &Options,
    report: &mut Report,
) {
    for round in 0..MAX_LOCAL_ROUNDS {
        if report.rewrites.len() >= MAX_REWRITES {
            report.budget_exhausted = true;
            return;
        }
        let mut changed = false;
        for rule in RULES {
            if let Some(offset) = (rule.apply)(instr, offset, context, facts, options) {
                report.rewrites.push(Rewrite {
                    offset,
                    rule: rule.name,
                });
                changed = true;
                break;
            }
        }
        if !changed {
            break;
        }
        if round + 1 == MAX_LOCAL_ROUNDS {
            report.budget_exhausted = true;
        }
    }
}

fn rewrite(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    options: &Options,
    report: &mut Report,
) {
    rewrite_local(instr, offset, context, facts, options, report);
    let before_children = report.rewrites.len();
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut then_facts = facts.clone();
            then_facts.assume(condition, true, context);
            let mut else_facts = facts.clone();
            else_facts.assume(condition, false, context);
            sequence(
                then_branch.iter_mut().map(|instr| (offset, instr)),
                context,
                then_facts,
                options,
                report,
            );
            sequence(
                else_branch.iter_mut().map(|instr| (offset, instr)),
                context,
                else_facts,
                options,
                report,
            );
        }
        IRInst::While { body, .. } => {
            let mut effects = Effects::default();
            for (_, instr) in body.iter() {
                effects.instruction(instr);
            }
            let mut invariants = facts.clone();
            invariants.invalidate(&effects, |address| {
                body.iter()
                    .all(|(_, instr)| writes_disjoint(instr, address))
            });
            sequence(
                body.iter_mut().map(|(offset, instr)| (*offset, instr)),
                context,
                invariants,
                options,
                report,
            );
        }
        _ => {}
    }
    // A child loop can become a modulo assignment under its surrounding
    // guard. Revisit that guard once its child rewrites are visible.
    if report.rewrites.len() > before_children {
        rewrite_local(instr, offset, context, facts, options, report);
    }
}

fn collect(instr: &IRInst, context: &Context, output: &mut Vec<LoopAnalysis>) {
    if let Some(analysis) = shapes::analyze(instr, context) {
        output.push(analysis);
    }
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                collect(instr, context, output);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                collect(instr, context, output);
            }
        }
        _ => {}
    }
}

pub fn run(program: &mut Program) -> Report {
    run_with_options(program, Options::default())
}

pub fn run_with_options(program: &mut Program, options: Options) -> Report {
    let mut report = Report::default();
    for function in &mut program.functions {
        let context = Context::from_function(function);
        for (_, instr) in &function.body {
            collect(instr, &context, &mut report.before);
        }
        sequence(
            function
                .body
                .iter_mut()
                .map(|(offset, instr)| (*offset, instr)),
            &context,
            Facts::default(),
            &options,
            &mut report,
        );
        let mut uses = HashMap::new();
        for (_, instr) in &function.body {
            collect_uses(instr, &mut uses);
        }
        collapse_temporary_assignments(
            &mut function.body,
            function.entry_offset,
            &context,
            &uses,
            &mut report,
        );
        // Collapsing a temporary can expose the modulo assignment directly
        // inside its guard, so run the local rules on the resulting IR.
        sequence(
            function
                .body
                .iter_mut()
                .map(|(offset, instr)| (*offset, instr)),
            &context,
            Facts::default(),
            &options,
            &mut report,
        );
        for (_, instr) in &function.body {
            collect(instr, &context, &mut report.remaining);
        }
    }
    report
}

impl Report {
    pub fn render(&self) -> String {
        let mut output = String::from("// Tier 6 arithmetic analysis (bit-vector sums)\n");
        for (heading, loops) in [("input", &self.before), ("remaining", &self.remaining)] {
            for analysis in loops {
                writeln!(
                    output,
                    "// {heading} loop 0x{:x}: {}",
                    analysis.offset, analysis.check
                )
                .unwrap();
                for (variable, value) in &analysis.updates {
                    writeln!(output, "//   v{}' = {}", variable.id, value).unwrap();
                }
                if let Some(shape) = &analysis.subtraction {
                    writeln!(
                        output,
                        "//   repeated subtraction: v{}, stride {}, u{}",
                        shape.accumulator.id, shape.stride, shape.bits
                    )
                    .unwrap();
                    for blocker in &shape.blockers {
                        writeln!(output, "//   blocked: {blocker}").unwrap();
                    }
                    if shape.blockers.is_empty() {
                        writeln!(output, "//   unknown strides require allow_assumptions").unwrap();
                    }
                } else {
                    writeln!(output, "//   no registered arithmetic shape").unwrap();
                }
            }
        }
        for rewrite in &self.rewrites {
            writeln!(
                output,
                "// rewrite at 0x{:x}: {}",
                rewrite.offset, rewrite.rule
            )
            .unwrap();
        }
        if self.budget_exhausted {
            writeln!(
                output,
                "// rewrite budget exhausted; unmatched code retained"
            )
            .unwrap();
        }
        output
    }
}
