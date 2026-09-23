//! Give implicit machine returns a likely value from the last RAX-family write.
//!
//! Tier 3 has both the register-slot types and the complete structured control
//! flow. A return is rewritten only when every reachable path agrees on its
//! closest register write; a join of different writes remains implicit.

use std::collections::HashMap;

use iced_x86::Register;

use super::ir::{
    IRExpr, IRInst, LoopId, Parameter, Program, SyntheticFunction, VariableId, VariableType,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Unreachable,
    Unknown,
    Slot(VariableId),
}

impl State {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unreachable, state) | (state, Self::Unreachable) => state,
            (Self::Slot(a), Self::Slot(b)) if a == b => Self::Slot(a),
            _ => Self::Unknown,
        }
    }
}

struct Node {
    successors: Vec<usize>,
    write: Option<VariableId>,
    return_address: Option<usize>,
}

#[derive(Clone, Copy)]
struct LoopTargets {
    label: Option<LoopId>,
    break_to: usize,
    continue_to: usize,
}

struct Flow {
    nodes: Vec<Node>,
}

impl Flow {
    fn push(
        &mut self,
        successors: Vec<usize>,
        write: Option<VariableId>,
        return_address: Option<usize>,
    ) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node {
            successors,
            write,
            return_address,
        });
        id
    }

    fn sequence<'a>(
        &mut self,
        instructions: impl DoubleEndedIterator<Item = &'a IRInst>,
        mut next: usize,
        loops: &[LoopTargets],
        register_slots: &HashMap<VariableId, Register>,
    ) -> usize {
        for instr in instructions.rev() {
            next = self.instruction(instr, next, loops, register_slots);
        }
        next
    }

    fn instruction(
        &mut self,
        instr: &IRInst,
        next: usize,
        loops: &[LoopTargets],
        register_slots: &HashMap<VariableId, Register>,
    ) -> usize {
        match instr {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_entry = self.sequence(then_branch.iter(), next, loops, register_slots);
                let else_entry = self.sequence(else_branch.iter(), next, loops, register_slots);
                self.push(vec![then_entry, else_entry], None, None)
            }
            IRInst::Loop { label, body, .. } => {
                let header = self.push(Vec::new(), None, None);
                let mut nested = loops.to_vec();
                nested.push(LoopTargets {
                    label: *label,
                    break_to: next,
                    continue_to: header,
                });
                let start = self.sequence(
                    body.iter().map(|(_, instr)| instr),
                    header,
                    &nested,
                    register_slots,
                );
                self.nodes[header].successors.push(start);
                header
            }
            IRInst::Break => self.push(
                loops
                    .last()
                    .map_or_else(Vec::new, |target| vec![target.break_to]),
                None,
                None,
            ),
            IRInst::Continue => self.push(
                loops
                    .last()
                    .map_or_else(Vec::new, |target| vec![target.continue_to]),
                None,
                None,
            ),
            IRInst::ContinueLoop(label) => self.push(
                loops
                    .iter()
                    .rev()
                    .find(|target| target.label == Some(*label))
                    .map_or_else(Vec::new, |target| vec![target.continue_to]),
                None,
                None,
            ),
            IRInst::Return(_) => self.push(Vec::new(), None, Some(instr as *const IRInst as usize)),
            IRInst::CallSynthetic { .. } | IRInst::Jump(_) | IRInst::End => {
                self.push(Vec::new(), None, None)
            }
            IRInst::AssignVariable { variable, .. }
            | IRInst::Assign {
                dest: IRExpr::Variable(variable),
                ..
            } if register_slots
                .get(variable)
                .is_some_and(|register| register.full_register() == Register::RAX) =>
            {
                self.push(vec![next], Some(*variable), None)
            }
            _ => self.push(vec![next], None, None),
        }
    }
}

fn collect_register_slots(instr: &IRInst, slots: &mut HashMap<VariableId, Register>) {
    match instr {
        IRInst::DeclareVariable {
            variable,
            ty: VariableType::Register(register),
        } => {
            slots.insert(*variable, *register);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                collect_register_slots(instr, slots);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                collect_register_slots(instr, slots);
            }
        }
        _ => {}
    }
}

fn rewrite(instr: &mut IRInst, returns: &HashMap<usize, VariableId>) {
    // The flow and rewrite traverse the same, unmoved instruction tree. The
    // address is only an identity key; it is never dereferenced as a pointer.
    let address = instr as *mut IRInst as usize;
    match instr {
        IRInst::Return(value @ None) => {
            if let Some(&variable) = returns.get(&address) {
                *value = Some(IRExpr::Variable(variable));
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter_mut().chain(else_branch) {
                rewrite(instr, returns);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                rewrite(instr, returns);
            }
        }
        _ => {}
    }
}

fn rewrite_function(function: &mut SyntheticFunction) {
    let mut register_slots = HashMap::new();
    for parameter in &function.parameters {
        if let Parameter::Slot { variable, register } = parameter {
            register_slots.insert(*variable, *register);
        }
    }
    for (_, instr) in &function.body {
        collect_register_slots(instr, &mut register_slots);
    }

    let mut flow = Flow { nodes: Vec::new() };
    let exit = flow.push(Vec::new(), None, None);
    let entry = flow.sequence(
        function.body.iter().map(|(_, instr)| instr),
        exit,
        &[],
        &register_slots,
    );

    let mut states = vec![State::Unreachable; flow.nodes.len()];
    states[entry] = State::Unknown;
    let mut pending = vec![entry];
    while let Some(node) = pending.pop() {
        let after = flow.nodes[node].write.map_or(states[node], State::Slot);
        for &next in &flow.nodes[node].successors {
            let joined = states[next].join(after);
            if joined != states[next] {
                states[next] = joined;
                pending.push(next);
            }
        }
    }

    let returns: HashMap<_, _> = flow
        .nodes
        .iter()
        .zip(states)
        .filter_map(|(node, state)| match (node.return_address, state) {
            (Some(address), State::Slot(variable)) => Some((address, variable)),
            _ => None,
        })
        .collect();
    for (_, instr) in &mut function.body {
        rewrite(instr, &returns);
    }
}

pub fn tr(mut program: Program) -> Program {
    for function in &mut program.functions {
        rewrite_function(function);
    }
    program
}
