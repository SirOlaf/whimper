//! Merge reachable synthetic functions using their complete control-flow graph.
//!
//! Tail calls become parallel assignments to destination-local slots. Linear
//! CFG edges are eliminated to a fixed point, then postdominators keep shared
//! tails outside branch arms. Only paths without a shared continuation need
//! copies; back edges become loops, including irreducible, multi-entry cycles.

use std::collections::{HashMap, HashSet};

use super::cfg::{Cfg, NodeId, Transfer};
use super::ir::{
    IRExpr, IRInst, LoopId, Parameter, Program, SyntheticFunction, SyntheticFunctionId, VariableId,
    VariableType,
};

#[derive(Default)]
struct Slots {
    next: usize,
    variables: HashMap<VariableId, VariableId>,
    declarations: Vec<(usize, IRInst)>,
}

impl Slots {
    fn fresh(&mut self, offset: usize, ty: VariableType) -> VariableId {
        let variable = VariableId {
            owner: SyntheticFunctionId { id: 0 },
            id: self.next,
        };
        self.next += 1;
        self.declarations
            .push((offset, IRInst::DeclareVariable { variable, ty }));
        variable
    }

    fn local(&mut self, source: VariableId, offset: usize, ty: VariableType) -> VariableId {
        if let Some(&variable) = self.variables.get(&source) {
            return variable;
        }
        let variable = self.fresh(offset, ty);
        self.variables.insert(source, variable);
        variable
    }

    fn collect(&mut self, offset: usize, instr: &IRInst) {
        match instr {
            IRInst::DeclareVariable { variable, ty } => {
                self.local(*variable, offset, *ty);
            }
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                for instr in then_branch.iter().chain(else_branch) {
                    self.collect(offset, instr);
                }
            }
            IRInst::Loop { body, .. } => {
                for (offset, instr) in body {
                    self.collect(*offset, instr);
                }
            }
            _ => {}
        }
    }

    fn expression(&self, expr: &mut IRExpr, natives: &HashMap<usize, VariableId>) {
        visit_expression(expr, &mut |expr| match expr {
            IRExpr::Variable(variable) => *variable = self.variables[variable],
            IRExpr::Argument(ordinal) => *expr = IRExpr::Variable(natives[ordinal]),
            _ => {}
        });
    }

    fn sequence(
        &mut self,
        body: Vec<(usize, IRInst)>,
        natives: &HashMap<usize, VariableId>,
        parameters: &[Vec<(VariableId, iced_x86::Register)>],
    ) -> Vec<(usize, IRInst)> {
        let mut result = Vec::new();
        for (offset, mut instr) in body {
            match &mut instr {
                IRInst::DeclareVariable { .. } => continue,
                IRInst::Assign { dest, src } => {
                    self.expression(dest, natives);
                    self.expression(src, natives);
                }
                IRInst::AssignVariable { variable, value } => {
                    *variable = self.variables[variable];
                    self.expression(value, natives);
                }
                IRInst::LoadVariable { variable, address }
                | IRInst::StoreVariable { address, variable } => {
                    *variable = self.variables[variable];
                    self.expression(address, natives);
                }
                IRInst::Return(Some(value)) | IRInst::Jump(value) => {
                    self.expression(value, natives)
                }
                IRInst::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    self.expression(condition, natives);
                    for branch in [then_branch, else_branch] {
                        *branch = self
                            .sequence(
                                std::mem::take(branch)
                                    .into_iter()
                                    .map(|instr| (offset, instr))
                                    .collect(),
                                natives,
                                parameters,
                            )
                            .into_iter()
                            .map(|(_, instr)| instr)
                            .collect();
                    }
                }
                IRInst::Loop { body, .. } => {
                    *body = self.sequence(std::mem::take(body), natives, parameters);
                }
                IRInst::CallSynthetic {
                    function,
                    arguments,
                } => {
                    assert_eq!(arguments.len(), parameters[function.id].len());
                    let mut assignments = Vec::new();
                    for (mut value, &(variable, register)) in std::mem::take(arguments)
                        .into_iter()
                        .zip(&parameters[function.id])
                    {
                        self.expression(&mut value, natives);
                        if !matches!(value, IRExpr::Variable(found) if found == variable) {
                            assignments.push((variable, register, value));
                        }
                    }
                    let destinations: HashSet<_> =
                        assignments.iter().map(|(var, _, _)| *var).collect();
                    let needs_staging = assignments.iter().any(|(variable, _, value)| {
                        let mut reads = HashSet::new();
                        expression_variables(value, &mut reads);
                        reads
                            .iter()
                            .any(|read| read != variable && destinations.contains(read))
                    });
                    // Evaluate every RHS before changing parameter slots. In
                    // particular, f(b, a) must not become a = b; b = a.
                    if needs_staging {
                        for (_, register, value) in &mut assignments {
                            let temporary =
                                self.fresh(offset, VariableType::Unknown(Some(register.size())));
                            result.push((
                                offset,
                                IRInst::AssignVariable {
                                    variable: temporary,
                                    value: value.clone(),
                                },
                            ));
                            *value = IRExpr::Variable(temporary);
                        }
                    }
                    result.extend(assignments.into_iter().map(|(variable, _, value)| {
                        (offset, IRInst::AssignVariable { variable, value })
                    }));
                }
                IRInst::Return(None)
                | IRInst::Break
                | IRInst::Continue
                | IRInst::ContinueLoop(_)
                | IRInst::End => {}
            }
            result.push((offset, instr));
        }
        result
    }
}

fn visit_expression(expr: &mut IRExpr, visit: &mut impl FnMut(&mut IRExpr)) {
    match expr {
        IRExpr::BinOp { lhs, rhs, .. } => {
            visit_expression(lhs, visit);
            visit_expression(rhs, visit);
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => visit_expression(inner, visit),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Data(_)
        | IRExpr::Bool(_) => {}
    }
    visit(expr);
}

fn expression_variables(expr: &IRExpr, variables: &mut HashSet<VariableId>) {
    // Reuse the exhaustive expression walk; this is analysis only.
    visit_expression(&mut expr.clone(), &mut |expr| {
        if let IRExpr::Variable(variable) = expr {
            variables.insert(*variable);
        }
    });
}

fn instruction_variables(instr: &IRInst, variables: &mut HashSet<VariableId>) {
    match instr {
        IRInst::Assign { dest, src } => {
            expression_variables(dest, variables);
            expression_variables(src, variables);
        }
        IRInst::AssignVariable { variable, value } => {
            variables.insert(*variable);
            expression_variables(value, variables);
        }
        IRInst::LoadVariable { variable, address }
        | IRInst::StoreVariable { address, variable } => {
            variables.insert(*variable);
            expression_variables(address, variables);
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => expression_variables(value, variables),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_variables(condition, variables);
            for instr in then_branch.iter().chain(else_branch) {
                instruction_variables(instr, variables);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                instruction_variables(instr, variables);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                expression_variables(argument, variables);
            }
        }
        IRInst::DeclareVariable { .. }
        | IRInst::Return(None)
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => {}
    }
}

struct Inliner<'a> {
    cfg: &'a Cfg,
    joins: Vec<Option<NodeId>>,
    active: Vec<Option<LoopId>>,
    back_edges: HashSet<LoopId>,
    next_loop: usize,
}

fn terminates(body: &[(usize, IRInst)]) -> bool {
    fn terminal(instr: &IRInst) -> bool {
        match instr {
            IRInst::Return(_)
            | IRInst::Jump(_)
            | IRInst::End
            | IRInst::Break
            | IRInst::Continue
            | IRInst::ContinueLoop(_) => true,
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                then_branch.last().is_some_and(terminal) && else_branch.last().is_some_and(terminal)
            }
            _ => false,
        }
    }
    body.last().is_some_and(|(_, instr)| terminal(instr))
}

// Track transfers to this loop without confusing nested-loop breaks with its
// exits. Labeled continues can still reach this loop from a nested loop.
fn loop_transfers(instr: &IRInst, label: LoopId, nested: bool) -> (bool, bool) {
    match instr {
        IRInst::Break => (!nested, false),
        IRInst::Continue => (false, !nested),
        IRInst::ContinueLoop(target) => (false, *target == label),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .map(|instr| loop_transfers(instr, label, nested))
            .fold((false, false), |(a, b), (c, d)| (a || c, b || d)),
        IRInst::Loop { body, .. } => body
            .iter()
            .map(|(_, instr)| loop_transfers(instr, label, true))
            .fold((false, false), |(a, b), (c, d)| (a || c, b || d)),
        _ => (false, false),
    }
}

fn hoist_loop_tail(body: &mut Vec<(usize, IRInst)>, label: LoopId) -> Vec<(usize, IRInst)> {
    let repeats = |instr: &IRInst| {
        matches!(instr, IRInst::Continue)
            || matches!(instr, IRInst::ContinueLoop(target) if *target == label)
    };
    let Some(index) = body.iter().rposition(|(_, instr)| match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            (else_branch.is_empty() && then_branch.last().is_some_and(&repeats))
                || (then_branch.is_empty() && else_branch.last().is_some_and(&repeats))
        }
        _ => false,
    }) else {
        return Vec::new();
    };

    let trailing_break = matches!(body.last(), Some((_, IRInst::Break)));
    let tail_end = body.len() - usize::from(trailing_break);
    // An earlier break used to bypass the tail. Likewise, a tail which jumps
    // back to this loop cannot be moved outside its scope. Keep both unchanged.
    if body[..=index]
        .iter()
        .any(|(_, instr)| loop_transfers(instr, label, false).0)
        || body[index + 1..tail_end]
            .iter()
            .any(|(_, instr)| loop_transfers(instr, label, false) != (false, false))
    {
        return Vec::new();
    }

    let mut tail = body.split_off(index + 1);
    if trailing_break {
        tail.pop();
    }
    let IRInst::If {
        condition,
        mut then_branch,
        mut else_branch,
    } = std::mem::replace(&mut body[index].1, IRInst::Break)
    else {
        unreachable!()
    };
    let (condition, updates) = if else_branch.is_empty() {
        then_branch.pop();
        let inverted = match condition {
            IRExpr::Not(inner) => *inner,
            condition => IRExpr::Not(Box::new(condition)),
        };
        (inverted, then_branch)
    } else {
        else_branch.pop();
        (condition, else_branch)
    };
    // The repeat path now falls through the loop body. Keep any parameter
    // updates on that path, and execute the exit tail only after the break.
    body[index].1 = IRInst::If {
        condition,
        then_branch: vec![IRInst::Break],
        else_branch: updates,
    };
    tail
}

impl Inliner<'_> {
    fn region(&mut self, id: NodeId, stop: Option<NodeId>) -> Vec<(usize, IRInst)> {
        if Some(id) == stop {
            return Vec::new();
        }
        let node = &self.cfg.nodes[id];
        if let Some(label) = self.active[id] {
            self.back_edges.insert(label);
            return vec![(node.offset, IRInst::ContinueLoop(label))];
        }
        let label = LoopId { id: self.next_loop };
        self.next_loop += 1;
        self.active[id] = Some(label);
        let mut body = node.body.clone();
        match &node.transfer {
            Transfer::Goto(target) => body.extend(self.region(*target, stop)),
            Transfer::Exit(instr) => body.push((node.offset, instr.clone())),
            Transfer::Branch {
                condition,
                then_node,
                else_node,
            } => {
                // An active header is a back edge, not a forward continuation.
                let join = self.joins[id].filter(|&join| self.active[join].is_none());
                let boundary = join.or(stop);
                let mut then_branch: Vec<_> = self
                    .region(*then_node, boundary)
                    .into_iter()
                    .map(|(_, instr)| instr)
                    .collect();
                let mut else_branch: Vec<_> = self
                    .region(*else_node, boundary)
                    .into_iter()
                    .map(|(_, instr)| instr)
                    .collect();
                let mut condition = condition.clone();
                let mut reads_memory = false;
                visit_expression(&mut condition, &mut |expr| {
                    reads_memory |= matches!(expr, IRExpr::Deref(_) | IRExpr::Data(_));
                });
                // An empty conditional has no effect unless evaluating its
                // condition performs a memory read. Retain those reads.
                if !then_branch.is_empty() || !else_branch.is_empty() || reads_memory {
                    if then_branch.is_empty() && !else_branch.is_empty() {
                        std::mem::swap(&mut then_branch, &mut else_branch);
                        condition = match condition {
                            IRExpr::Not(inner) => *inner,
                            condition => IRExpr::Not(Box::new(condition)),
                        };
                    }
                    body.push((
                        node.offset,
                        IRInst::If {
                            condition,
                            then_branch,
                            else_branch,
                        },
                    ));
                }
                if let Some(join) = join {
                    body.extend(self.region(join, stop));
                }
            }
        }
        self.active[id] = None;
        if self.back_edges.remove(&label) {
            // A path which reaches this region's continuation exits the loop;
            // explicit back edges continue it. Labeled continues preserve outer
            // transfers when node splitting exposes nested/irreducible cycles.
            if !terminates(&body) {
                body.push((node.offset, IRInst::Break));
            }
            let tail = hoist_loop_tail(&mut body, label);
            let needs_label = body
                .iter()
                .any(|(_, instr)| loop_transfers(instr, label, false).1);
            let entry_offset = body.first().map_or(node.offset, |(offset, _)| *offset);
            let mut result = vec![(
                entry_offset,
                IRInst::Loop {
                    label: needs_label.then_some(label),
                    entry_offset,
                    body,
                },
            )];
            result.extend(tail);
            result
        } else {
            body
        }
    }
}

pub fn tr(mut program: Program) -> Program {
    let Some(entry) = program.entry else {
        return program;
    };
    let entry_offset = program.functions[entry.id].entry_offset;
    let mut slots = Slots::default();
    let mut parameters = Vec::new();
    let mut native_slots = Vec::new();
    let mut signature = program.functions[entry.id].parameters.clone();
    let mut initializers = Vec::new();
    for (id, function) in program.functions.iter().enumerate() {
        let mut bindings = Vec::new();
        let mut natives = HashMap::new();
        for parameter in &function.parameters {
            let (variable, register) = match parameter {
                Parameter::Slot { variable, register } => (
                    slots.local(
                        *variable,
                        function.entry_offset,
                        VariableType::Register(*register),
                    ),
                    *register,
                ),
                Parameter::Native { ordinal, register } => {
                    let variable =
                        slots.fresh(function.entry_offset, VariableType::Register(*register));
                    natives.insert(*ordinal, variable);
                    if id == entry.id {
                        initializers.push((
                            entry_offset,
                            IRInst::AssignVariable {
                                variable,
                                value: IRExpr::Argument(*ordinal),
                            },
                        ));
                    }
                    (variable, *register)
                }
            };
            bindings.push((variable, register));
        }
        for (offset, instr) in &function.body {
            slots.collect(*offset, instr);
        }
        parameters.push(bindings);
        native_slots.push(natives);
    }
    let mut signature_slots = HashSet::new();
    for parameter in &mut signature {
        if let Parameter::Slot { variable, .. } = parameter {
            *variable = slots.variables[variable];
            signature_slots.insert(*variable);
        }
    }
    for (id, function) in program.functions.iter_mut().enumerate() {
        function.body = slots.sequence(
            std::mem::take(&mut function.body),
            &native_slots[id],
            &parameters,
        );
    }
    let entry_address = program.entry_address;
    let data = program.data.clone();
    let mut cfg = Cfg::build(program);
    cfg.eliminate_branches();
    let mut inliner = Inliner {
        joins: cfg.postdominators(),
        active: vec![None; cfg.nodes.len()],
        back_edges: HashSet::new(),
        next_loop: 0,
        cfg: &cfg,
    };
    let mut body = inliner.region(cfg.entry, None);
    let mut used = HashSet::new();
    for (_, instr) in &body {
        instruction_variables(instr, &mut used);
    }
    initializers.retain(|(_, instr)| matches!(instr, IRInst::AssignVariable { variable, .. } if used.contains(variable)));
    slots.declarations.retain(|(_, instr)| matches!(instr,
        IRInst::DeclareVariable { variable, .. } if used.contains(variable) && !signature_slots.contains(variable)));
    slots.declarations.append(&mut initializers);
    slots.declarations.append(&mut body);
    Program {
        entry_address,
        entry: Some(SyntheticFunctionId { id: 0 }),
        data,
        functions: vec![SyntheticFunction {
            entry_offset,
            parameters: signature,
            body: slots.declarations,
        }],
    }
}
