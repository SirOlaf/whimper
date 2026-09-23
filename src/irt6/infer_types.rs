//! Higher-tier type evidence from recovered operations. Tier 5 cannot infer a
//! zero-terminated string from byte accesses alone.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRExpr, IRInst, Parameter, Program, SyntheticFunctionId, VariableId, VariableType,
};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum Slot {
    Argument(SyntheticFunctionId, usize),
    Variable(VariableId),
}

fn direct_slot(expr: &IRExpr, owner: SyntheticFunctionId) -> Option<Slot> {
    match expr {
        IRExpr::Argument(ordinal) => Some(Slot::Argument(owner, *ordinal)),
        IRExpr::Variable(variable) => Some(Slot::Variable(*variable)),
        _ => None,
    }
}

fn is_byte_sequence(ty: &VariableType) -> bool {
    matches!(ty, VariableType::CString)
        || matches!(ty, VariableType::Vector(element) if element.as_ref() == &VariableType::Integer(8))
}

fn visit(
    instr: &IRInst,
    owner: SyntheticFunctionId,
    program: &Program,
    types: &mut HashMap<Slot, VariableType>,
    edges: &mut Vec<(Slot, Slot)>,
    seeds: &mut HashSet<Slot>,
) {
    let mut copy = |dest: Slot, source: &IRExpr| {
        if let Some(source) = direct_slot(source, owner) {
            edges.push((dest, source));
        }
    };
    match instr {
        IRInst::DeclareVariable { variable, ty } => {
            types.insert(Slot::Variable(*variable), ty.clone());
        }
        IRInst::DeclareAndAssignVariable {
            variable,
            ty,
            value,
        } => {
            types.insert(Slot::Variable(*variable), ty.clone());
            copy(Slot::Variable(*variable), value);
        }
        IRInst::AssignVariable { variable, value }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } => {
            copy(Slot::Variable(*variable), value);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for child in then_branch.iter().chain(else_branch) {
                visit(child, owner, program, types, edges, seeds);
            }
        }
        IRInst::While { body, .. } => {
            for (_, child) in body {
                visit(child, owner, program, types, edges, seeds);
            }
        }
        IRInst::ForEach {
            variable,
            element_type,
            vector,
            body,
            ..
        } => {
            types.insert(Slot::Variable(*variable), element_type.clone());
            if *element_type == VariableType::Integer(8) {
                if let Some(base) = direct_slot(vector, owner) {
                    seeds.insert(base);
                }
            }
            for (_, child) in body {
                visit(child, owner, program, types, edges, seeds);
            }
        }
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            if let Some(callee) = program.functions.get(function.id) {
                for (formal, actual) in callee.parameters.iter().zip(arguments) {
                    let formal = match formal {
                        Parameter::Argument { ordinal, .. } => Slot::Argument(*function, *ordinal),
                        Parameter::Slot { variable, .. } => Slot::Variable(*variable),
                    };
                    if let Some(actual) = direct_slot(actual, owner) {
                        edges.push((formal, actual));
                    }
                }
            }
        }
        _ => {}
    }
}

fn update(instr: &mut IRInst, promoted: &HashSet<Slot>) {
    match instr {
        IRInst::DeclareVariable { variable, ty }
        | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
            if promoted.contains(&Slot::Variable(*variable)) {
                *ty = VariableType::CString;
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for child in then_branch.iter_mut().chain(else_branch) {
                update(child, promoted);
            }
        }
        IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
            for (_, child) in body {
                update(child, promoted);
            }
        }
        _ => {}
    }
}

/// Promote only byte vectors connected to a recovered zero-terminated walk.
/// Direct copies and synthetic call arguments carry the same type constraint.
pub fn run(program: &mut Program) {
    let mut types = HashMap::new();
    for (id, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id };
        for parameter in &function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    types.insert(Slot::Argument(owner, *ordinal), ty.clone());
                }
                Parameter::Slot { variable, ty } => {
                    types.insert(Slot::Variable(*variable), ty.clone());
                }
            }
        }
    }
    let mut edges = Vec::new();
    let mut seeds = HashSet::new();
    for (id, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id };
        for (_, instr) in &function.body {
            visit(instr, owner, program, &mut types, &mut edges, &mut seeds);
        }
    }
    for (slot, ty) in &types {
        if *ty == VariableType::CString {
            seeds.insert(*slot);
        }
    }
    let mut adjacent: HashMap<Slot, Vec<Slot>> = HashMap::new();
    for (left, right) in edges {
        if types.get(&left).is_some_and(is_byte_sequence)
            && types.get(&right).is_some_and(is_byte_sequence)
        {
            adjacent.entry(left).or_default().push(right);
            adjacent.entry(right).or_default().push(left);
        }
    }
    let mut promoted = HashSet::new();
    let mut pending = seeds.into_iter().collect::<Vec<_>>();
    while let Some(slot) = pending.pop() {
        if !types.get(&slot).is_some_and(is_byte_sequence) || !promoted.insert(slot) {
            continue;
        }
        pending.extend(adjacent.get(&slot).into_iter().flatten().copied());
    }
    let changed = promoted
        .iter()
        .any(|slot| types.get(slot) != Some(&VariableType::CString));
    if changed {
        for (id, function) in program.functions.iter_mut().enumerate() {
            let owner = SyntheticFunctionId { id };
            for parameter in &mut function.parameters {
                let (slot, ty) = match parameter {
                    Parameter::Argument { ordinal, ty } => (Slot::Argument(owner, *ordinal), ty),
                    Parameter::Slot { variable, ty } => (Slot::Variable(*variable), ty),
                };
                if promoted.contains(&slot) {
                    *ty = VariableType::CString;
                }
            }
            for (_, instr) in &mut function.body {
                update(instr, &promoted);
            }
        }
    }
}
