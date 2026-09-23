//! Small, ordered rewrite rules with a bounded local fixed point.
//!
//! Entry facts are invalidated by writes. Loop bodies retain only invariant
//! facts. Each successful rewrite restarts rule selection; a recognizer can
//! therefore rely on shapes established by earlier, independent rules.

use std::fmt::Write;

use super::{
    arithmetic::{Bindings, Context, Kind, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, Program},
    shapes::{self, LoopAnalysis},
};

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
struct Facts(Vec<Value>);

impl Facts {
    fn assume(&mut self, expression: &IRExpr, truth: bool, context: &Context) {
        if repeatable(expression) {
            let value = context.value(expression);
            self.0.push(if truth { value } else { value.negated() });
        }
    }

    fn invalidate(&mut self, effects: &Effects) {
        if effects.unknown_write {
            self.0.clear();
            return;
        }
        self.0
            .retain(|fact| !effects.writes.iter().any(|variable| fact.reads(*variable)));
    }

    fn is_zero(&self, value: &Value) -> Option<bool> {
        if let Kind::Constant(constant) = value.kind {
            return Some(constant == 0);
        }
        self.0.iter().find_map(|fact| {
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
    apply: fn(&mut IRInst, usize, &Context, &Facts) -> Option<usize>,
}

const RULES: &[Rule] = &[
    Rule {
        name: "guarded-do-to-while",
        apply: rotate_guarded_loop,
    },
    Rule {
        name: "repeated-subtraction-to-remainder",
        apply: recover_remainder,
    },
    Rule {
        name: "compound-assignment",
        apply: recover_compound_assignment,
    },
];

fn recover_compound_assignment(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
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
) -> Option<usize> {
    let analysis = shapes::analyze(instr, context)?;
    let shape = analysis.subtraction?;
    if !shape.blockers.is_empty() || facts.is_zero(&shape.stride) == Some(true) {
        return None;
    }
    let replacement = IRInst::AssignVariable {
        variable: shape.accumulator,
        value: IRExpr::BinOp {
            kind: IRBinOpKind::UnsignedMod,
            lhs: Box::new(IRExpr::Variable(shape.accumulator)),
            rhs: Box::new(shape.stride_source.clone()),
        },
    };
    if facts.is_zero(&shape.stride) == Some(false) {
        *instr = replacement;
    } else {
        // x >= 0 makes the original zero-stride loop nonterminating. Preserve
        // it explicitly instead of introducing a divide-by-zero trap or exit.
        let original = std::mem::replace(instr, IRInst::End);
        *instr = IRInst::If {
            condition: IRExpr::BinOp {
                kind: IRBinOpKind::Ne,
                lhs: Box::new(shape.stride_source),
                rhs: Box::new(match shape.bits {
                    8 => IRExpr::CU8(0),
                    16 | 32 => IRExpr::CU32(0),
                    _ => IRExpr::CU64(0),
                }),
            },
            then_branch: vec![replacement],
            else_branch: vec![original],
        };
    }
    Some(analysis.offset)
}

const MAX_REWRITES: usize = 256;
const MAX_LOCAL_ROUNDS: usize = 16;

fn sequence<'a>(
    instructions: impl Iterator<Item = (usize, &'a mut IRInst)>,
    context: &Context,
    mut facts: Facts,
    report: &mut Report,
) {
    for (offset, instr) in instructions {
        rewrite(instr, offset, context, &facts, report);
        let mut effects = Effects::default();
        effects.instruction(instr);
        facts.invalidate(&effects);
    }
}

fn rewrite(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    report: &mut Report,
) {
    for round in 0..MAX_LOCAL_ROUNDS {
        if report.rewrites.len() >= MAX_REWRITES {
            report.budget_exhausted = true;
            return;
        }
        let mut changed = false;
        for rule in RULES {
            if let Some(offset) = (rule.apply)(instr, offset, context, facts) {
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
                report,
            );
            sequence(
                else_branch.iter_mut().map(|instr| (offset, instr)),
                context,
                else_facts,
                report,
            );
        }
        IRInst::While { body, .. } => {
            let mut effects = Effects::default();
            for (_, instr) in body.iter() {
                effects.instruction(instr);
            }
            let mut invariants = facts.clone();
            invariants.invalidate(&effects);
            sequence(
                body.iter_mut().map(|(offset, instr)| (*offset, instr)),
                context,
                invariants,
                report,
            );
        }
        _ => {}
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
                        writeln!(
                            output,
                            "//   requires a nonzero stride; zero paths retain the loop"
                        )
                        .unwrap();
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
