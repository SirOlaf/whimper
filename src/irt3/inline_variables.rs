//! Inline single-use values while their inputs are unchanged.

use std::collections::{HashMap, HashSet};

use super::ir::{IRExpr, IRInst, Parameter, Program, SyntheticFunction, VariableId, VariableType};

// A small access IR keeps the use and write analysis separate from rewriting
// the full tier 3 instruction tree.
enum Access {
    Read(VariableId),
    Write(VariableId),
    WriteMemory,
}

#[derive(Default)]
struct Usage {
    reads: Vec<usize>,
    writes: Vec<usize>,
}

#[derive(Default)]
struct Writes {
    variables: HashSet<VariableId>,
    memory: bool,
}

fn expression_accesses(expr: &IRExpr, accesses: &mut Vec<Access>) {
    match expr {
        IRExpr::Variable(variable) => accesses.push(Access::Read(*variable)),
        IRExpr::BinOp { lhs, rhs, .. } => {
            expression_accesses(lhs, accesses);
            expression_accesses(rhs, accesses);
        }
        IRExpr::Deref(expr)
        | IRExpr::CastUnknownPtr { address: expr, .. }
        | IRExpr::Convert { value: expr, .. }
        | IRExpr::Not(expr) => expression_accesses(expr, accesses),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Bool(_) => {}
    }
}

fn instruction_accesses(instr: &IRInst, accesses: &mut Vec<Access>) {
    match instr {
        IRInst::Assign { dest, src } => {
            expression_accesses(src, accesses);
            if let IRExpr::Variable(variable) = dest {
                accesses.push(Access::Write(*variable));
            } else {
                expression_accesses(dest, accesses);
                accesses.push(Access::WriteMemory);
            }
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => {
            expression_accesses(value, accesses);
        }
        IRInst::AssignVariable { variable, value } => {
            expression_accesses(value, accesses);
            accesses.push(Access::Write(*variable));
        }
        IRInst::LoadVariable { variable, address } => {
            expression_accesses(address, accesses);
            accesses.push(Access::Write(*variable));
        }
        IRInst::StoreVariable { address, variable } => {
            expression_accesses(address, accesses);
            accesses.push(Access::Read(*variable));
            accesses.push(Access::WriteMemory);
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_accesses(condition, accesses);
            for instr in then_branch.iter().chain(else_branch) {
                instruction_accesses(instr, accesses);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                instruction_accesses(instr, accesses);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                expression_accesses(argument, accesses);
            }
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => {}
    }
}

// Record everything whose value must stay unchanged between a definition and
// the instruction using it. A dereference depends on both its address and the
// memory it reads.
fn input_reads(expr: &IRExpr, variables: &mut HashSet<VariableId>, memory: &mut bool) {
    match expr {
        IRExpr::Variable(variable) => {
            variables.insert(*variable);
        }
        IRExpr::Deref(address) => {
            *memory = true;
            input_reads(address, variables, memory);
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            input_reads(lhs, variables, memory);
            input_reads(rhs, variables, memory);
        }
        IRExpr::CastUnknownPtr { address, .. }
        | IRExpr::Convert { value: address, .. }
        | IRExpr::Not(address) => input_reads(address, variables, memory),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Bool(_) => {}
    }
}

fn candidate(function: &SyntheticFunction) -> Option<(VariableId, usize, usize, IRExpr)> {
    let mut usage: HashMap<VariableId, Usage> = HashMap::new();
    let mut writes_by_instruction = Vec::with_capacity(function.body.len());
    for (index, (_, instr)) in function.body.iter().enumerate() {
        let mut accesses = Vec::new();
        instruction_accesses(instr, &mut accesses);
        let mut writes = Writes::default();
        for access in accesses {
            match access {
                Access::Read(variable) => usage.entry(variable).or_default().reads.push(index),
                Access::Write(variable) => {
                    usage.entry(variable).or_default().writes.push(index);
                    writes.variables.insert(variable);
                }
                Access::WriteMemory => writes.memory = true,
            }
        }
        writes_by_instruction.push(writes);
    }

    let parameters: HashSet<_> = function
        .parameters
        .iter()
        .filter_map(|parameter| match parameter {
            Parameter::Slot { variable, .. } => Some(*variable),
            Parameter::Native { .. } => None,
        })
        .collect();
    let bool_slots: HashSet<_> = function
        .body
        .iter()
        .filter_map(|(_, instr)| match instr {
            IRInst::DeclareVariable {
                variable,
                ty: VariableType::Bool,
            } => Some(*variable),
            _ => None,
        })
        .collect();

    for (definition, (_, instr)) in function.body.iter().enumerate() {
        let (variable, value) = match instr {
            IRInst::AssignVariable { variable, value } => (*variable, value.clone()),
            IRInst::LoadVariable { variable, address } => {
                (*variable, IRExpr::Deref(Box::new(address.clone())))
            }
            _ => continue,
        };
        if parameters.contains(&variable) {
            continue;
        }
        let Some(usage) = usage.get(&variable) else {
            continue;
        };
        if usage.reads.len() != 1 || usage.writes != [definition] {
            continue;
        }
        let use_index = usage.reads[0];
        if use_index <= definition {
            continue;
        }
        let condition_use = match &function.body[use_index].1 {
            IRInst::If { condition, .. } => {
                let mut accesses = Vec::new();
                expression_accesses(condition, &mut accesses);
                accesses
                    .iter()
                    .any(|access| matches!(access, Access::Read(found) if *found == variable))
            }
            _ => false,
        };
        let ordinary_value = matches!(
            value,
            IRExpr::BinOp { .. } | IRExpr::Variable(_) | IRExpr::Deref(_)
        );
        // Boolean slots are also safe to fold into their sole If condition,
        // including comparisons, negation, disjunction, and constants.
        if !ordinary_value && !(bool_slots.contains(&variable) && condition_use) {
            continue;
        }

        let mut inputs = HashSet::new();
        let mut reads_memory = false;
        input_reads(&value, &mut inputs, &mut reads_memory);
        // A use in an If condition precedes its arms. A use inside an arm
        // may follow writes in that arm, so include those as possible barriers.
        let in_arm = matches!(function.body[use_index].1, IRInst::If { .. }) && !condition_use;
        let in_loop = matches!(function.body[use_index].1, IRInst::Loop { .. });
        // A snapshot load must not become conditional or repeat in a loop.
        // Pure expressions can move only if the entire region preserves their
        // inputs, including writes on later loop iterations.
        if reads_memory && (in_arm || in_loop) {
            continue;
        }
        let end = if in_arm || in_loop {
            use_index + 1
        } else {
            use_index
        };
        if writes_by_instruction[definition + 1..end]
            .iter()
            .any(|writes| !writes.variables.is_disjoint(&inputs) || (reads_memory && writes.memory))
        {
            continue;
        }
        return Some((variable, definition, use_index, value));
    }
    None
}

fn replace_expression(expr: &mut IRExpr, variable: VariableId, value: &IRExpr) -> bool {
    match expr {
        IRExpr::Variable(found) if *found == variable => {
            *expr = value.clone();
            true
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            replace_expression(lhs, variable, value) | replace_expression(rhs, variable, value)
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => replace_expression(inner, variable, value),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => false,
    }
}

fn replace_instruction(instr: &mut IRInst, variable: VariableId, value: &IRExpr) -> bool {
    match instr {
        IRInst::Assign { dest, src } => {
            let source = replace_expression(src, variable, value);
            if matches!(dest, IRExpr::Variable(_)) {
                source
            } else {
                replace_expression(dest, variable, value) | source
            }
        }
        IRInst::Return(Some(expr)) | IRInst::Jump(expr) => {
            replace_expression(expr, variable, value)
        }
        IRInst::AssignVariable { value: expr, .. } => replace_expression(expr, variable, value),
        IRInst::LoadVariable { address, .. } => replace_expression(address, variable, value),
        IRInst::StoreVariable {
            address,
            variable: stored,
        } => {
            let in_address = replace_expression(address, variable, value);
            if *stored == variable {
                *instr = IRInst::Assign {
                    dest: IRExpr::Deref(Box::new(address.clone())),
                    src: value.clone(),
                };
                true
            } else {
                in_address
            }
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut replaced = replace_expression(condition, variable, value);
            for instr in then_branch.iter_mut().chain(else_branch) {
                replaced |= replace_instruction(instr, variable, value);
            }
            replaced
        }
        IRInst::Loop { body, .. } => {
            let mut replaced = false;
            for (_, instr) in body {
                replaced |= replace_instruction(instr, variable, value);
            }
            replaced
        }
        IRInst::CallSynthetic { arguments, .. } => {
            arguments.iter_mut().fold(false, |found, argument| {
                replace_expression(argument, variable, value) | found
            })
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => false,
    }
}

fn inline_function(function: &mut SyntheticFunction) {
    // Each replacement removes one definition. Rescanning lets loads expose
    // aliases and binary expressions (and vice versa) until none remain.
    while let Some((variable, definition, use_index, value)) = candidate(function) {
        assert!(replace_instruction(
            &mut function.body[use_index].1,
            variable,
            &value
        ));
        function.body.remove(definition);
        function.body.retain(|(_, instr)| {
            !matches!(instr, IRInst::DeclareVariable { variable: declared, .. } if *declared == variable)
        });
    }
}

pub fn tr(mut program: Program) -> Program {
    for function in &mut program.functions {
        inline_function(function);
    }
    program
}
