//! Propagate constants exposed by control-flow recovery. Loop writes invalidate
//! incoming facts; a constant assignment is removed only when no path reads it.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, IntegerType, LoopCondition, Parameter, Program, VariableId,
    VariableType,
};
use super::variable_flow::Flow;

type Constants = HashMap<VariableId, IRExpr>;

fn mask(size: usize) -> u64 {
    u64::MAX >> (64 - size * 8)
}

fn literal(value: u64, size: usize) -> IRExpr {
    match size {
        1 => IRExpr::CU8(value as u8),
        4 => IRExpr::CU32(value as u32),
        8 => IRExpr::CU64(value),
        2 => IRExpr::Convert {
            value: Box::new(IRExpr::CU32(value as u16 as u32)),
            source: IntegerType {
                size: 4,
                signed: false,
            },
            target: IntegerType {
                size: 2,
                signed: false,
            },
        },
        _ => unreachable!("invalid integer width"),
    }
}

fn constant(expr: &IRExpr) -> Option<(u64, usize)> {
    match expr {
        IRExpr::CU8(value) => Some((*value as u64, 1)),
        IRExpr::CU32(value) => Some((*value as u64, 4)),
        IRExpr::CU64(value) => Some((*value, 8)),
        IRExpr::Bool(value) => Some((u64::from(*value), 1)),
        IRExpr::Convert {
            value,
            source,
            target,
        } => {
            let (value, _) = constant(value)?;
            let value = value & mask(source.size);
            let value = if source.signed && value & (1 << (source.size * 8 - 1)) != 0 {
                value | !mask(source.size)
            } else {
                value
            };
            Some((value & mask(target.size), target.size))
        }
        _ => None,
    }
}

fn expression(expr: &mut IRExpr, known: &Constants) {
    match expr {
        IRExpr::Variable(variable) => {
            if let Some(value) = known.get(variable) {
                *expr = value.clone();
            }
        }
        IRExpr::BinOp { kind, lhs, rhs } => {
            let literal_left = constant(lhs).is_some();
            let literal_right = constant(rhs).is_some();
            expression(lhs, known);
            expression(rhs, known);
            let (Some((a, left_size)), Some((b, right_size))) = (constant(lhs), constant(rhs))
            else {
                return;
            };
            let size = if literal_left
                && !literal_right
                && !matches!(kind, IRBinOpKind::Shl | IRBinOpKind::Shr)
            {
                right_size
            } else {
                left_size
            };
            let a = a & mask(size);
            let right = b & mask(size);
            let value = match kind {
                IRBinOpKind::Add => a.wrapping_add(right),
                IRBinOpKind::Sub => a.wrapping_sub(right),
                IRBinOpKind::Mul => a.wrapping_mul(right),
                IRBinOpKind::Shl => a.wrapping_shl((b & if size == 8 { 63 } else { 31 }) as u32),
                IRBinOpKind::Shr => a.wrapping_shr((b & if size == 8 { 63 } else { 31 }) as u32),
                IRBinOpKind::And => a & right,
                IRBinOpKind::BitOr => a | right,
                comparison => {
                    let value = match comparison {
                        IRBinOpKind::Eq => a == right,
                        IRBinOpKind::Ne => a != right,
                        IRBinOpKind::UnsignedLt => a < right,
                        IRBinOpKind::UnsignedGe => a >= right,
                        IRBinOpKind::SignedGt => {
                            let shift = 64 - size * 8;
                            ((a << shift) as i64 >> shift) > ((right << shift) as i64 >> shift)
                        }
                        IRBinOpKind::Or => a != 0 || b != 0,
                        _ => unreachable!(),
                    };
                    *expr = IRExpr::Bool(value);
                    return;
                }
            };
            *expr = literal(value & mask(size), size);
        }
        IRExpr::Convert { value, .. } => {
            expression(value, known);
            if let Some((value, size)) = constant(expr) {
                *expr = literal(value, size);
            }
        }
        IRExpr::Not(value) => {
            expression(value, known);
            if let IRExpr::Bool(value) = **value {
                *expr = IRExpr::Bool(!value);
            }
        }
        IRExpr::Deref(address) | IRExpr::CastUnknownPtr { address, .. } => {
            expression(address, known)
        }
        _ => {}
    }
}

fn assigned(instr: &IRInst, writes: &mut HashSet<VariableId>) {
    match instr {
        IRInst::AssignVariable { variable, .. }
        | IRInst::DeclareAndAssignVariable { variable, .. }
        | IRInst::LoadVariable { variable, .. }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            ..
        } => {
            writes.insert(*variable);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                assigned(instr, writes);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                assigned(instr, writes);
            }
        }
        _ => {}
    }
}

fn assignment(
    variable: VariableId,
    value: &mut IRExpr,
    known: &mut Constants,
    types: &HashMap<VariableId, VariableType>,
) {
    expression(value, known);
    if let Some((bits, _)) = constant(value) {
        match types.get(&variable) {
            Some(VariableType::Unknown(Some(size))) if matches!(size, 1 | 2 | 4 | 8) => {
                *value = literal(bits, *size)
            }
            Some(VariableType::Bool) => *value = IRExpr::Bool(bits != 0),
            _ => {}
        }
    }
    if constant(value).is_some() {
        known.insert(variable, value.clone());
    } else {
        known.remove(&variable);
    }
}

fn instruction(
    instr: &mut IRInst,
    known: &mut Constants,
    types: &HashMap<VariableId, VariableType>,
) {
    match instr {
        IRInst::AssignVariable { variable, value }
        | IRInst::DeclareAndAssignVariable {
            variable, value, ..
        }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } => assignment(*variable, value, known, types),
        IRInst::Assign { dest, src } => {
            expression(dest, known);
            expression(src, known);
        }
        IRInst::LoadVariable { variable, address } => {
            expression(address, known);
            known.remove(variable);
        }
        IRInst::StoreVariable { variable, address } => {
            expression(address, known);
            if let Some(src) = known.get(variable) {
                *instr = IRInst::Assign {
                    dest: IRExpr::Deref(Box::new(address.clone())),
                    src: src.clone(),
                };
            }
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression(condition, known);
            let mut then_values = known.clone();
            let mut else_values = known.clone();
            for instr in then_branch {
                instruction(instr, &mut then_values, types);
            }
            for instr in else_branch {
                instruction(instr, &mut else_values, types);
            }
            then_values.retain(|variable, value| else_values.get(variable) == Some(value));
            *known = then_values;
        }
        IRInst::While {
            body, condition, ..
        } => {
            let mut writes = HashSet::new();
            for (_, instr) in body.iter() {
                assigned(instr, &mut writes);
            }
            known.retain(|variable, _| !writes.contains(variable));
            let mut local = known.clone();
            if let LoopCondition::Before {
                expression: value, ..
            } = condition
            {
                expression(value, &local);
            }
            for (_, instr) in body {
                instruction(instr, &mut local, types);
            }
            if let LoopCondition::After {
                expression: value, ..
            } = condition
            {
                expression(value, &local);
            }
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => expression(value, known),
        IRInst::CallSynthetic { arguments, .. } => {
            for arg in arguments {
                expression(arg, known);
            }
        }
        _ => {}
    }
}

fn remove_dead(instr: &mut IRInst, dead: &HashSet<usize>) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for branch in [then_branch, else_branch] {
                // Reverse removal preserves the addresses of earlier siblings.
                for index in (0..branch.len()).rev() {
                    if dead.contains(&(&branch[index] as *const IRInst as usize)) {
                        if let IRInst::DeclareAndAssignVariable { variable, ty, .. } = branch[index]
                        {
                            branch[index] = IRInst::DeclareVariable { variable, ty };
                        } else {
                            branch.remove(index);
                        }
                    } else {
                        remove_dead(&mut branch[index], dead);
                    }
                }
            }
        }
        IRInst::While { body, .. } => remove_body(body, dead),
        _ => {}
    }
}

fn remove_body(body: &mut Vec<(usize, IRInst)>, dead: &HashSet<usize>) {
    for index in (0..body.len()).rev() {
        if dead.contains(&(&body[index].1 as *const IRInst as usize)) {
            if let IRInst::DeclareAndAssignVariable { variable, ty, .. } = body[index].1 {
                body[index].1 = IRInst::DeclareVariable { variable, ty };
            } else {
                body.remove(index);
            }
        } else {
            remove_dead(&mut body[index].1, dead);
        }
    }
}

pub(super) fn run(program: &mut Program) {
    for function in &mut program.functions {
        let mut types = HashMap::new();
        for parameter in &function.parameters {
            if let Parameter::Slot { variable, size } = parameter {
                types.insert(*variable, VariableType::Unknown(Some(*size)));
            }
        }
        for (_, instr) in &function.body {
            collect_types(instr, &mut types);
        }
        let mut known = Constants::new();
        for (_, instr) in &mut function.body {
            instruction(instr, &mut known, &types);
        }
        loop {
            let flow = Flow::from_function(function);
            let mut dead = HashSet::new();
            for node in &flow.nodes {
                if !node.operation.pure_write {
                    continue;
                }
                let Some(variable) = node.operation.write else {
                    continue;
                };
                let mut pending = node.successors.clone();
                let mut visited = HashSet::new();
                let mut read = false;
                while let Some(next) = pending.pop() {
                    if !visited.insert(next) {
                        continue;
                    }
                    let next = &flow.nodes[next];
                    if next.operation.reads(variable) {
                        read = true;
                        break;
                    }
                    if next.operation.write != Some(variable) {
                        pending.extend(&next.successors);
                    }
                }
                if !read && let Some(address) = node.instruction {
                    dead.insert(address);
                }
            }
            if dead.is_empty() {
                break;
            }
            remove_body(&mut function.body, &dead);
        }
    }
}

fn collect_types(instr: &IRInst, types: &mut HashMap<VariableId, VariableType>) {
    match instr {
        IRInst::DeclareVariable { variable, ty }
        | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
            types.insert(*variable, *ty);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                collect_types(instr, types);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                collect_types(instr, types);
            }
        }
        _ => {}
    }
}
