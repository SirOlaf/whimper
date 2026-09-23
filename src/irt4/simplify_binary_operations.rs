//! Simplify binary operations and direct negations.

use super::ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, Program};

fn is_zero(expr: &IRExpr) -> bool {
    matches!(expr, IRExpr::CU8(0) | IRExpr::CU32(0) | IRExpr::CU64(0))
}

fn effect_free(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Deref(_) => false,
        IRExpr::BinOp { lhs, rhs, .. } => effect_free(lhs) && effect_free(rhs),
        IRExpr::CastUnknownPtr { address, .. }
        | IRExpr::Convert { value: address, .. }
        | IRExpr::Not(address) => effect_free(address),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => true,
    }
}

fn simplify_expression(expr: &mut IRExpr) {
    match expr {
        IRExpr::BinOp { kind, lhs, rhs } => {
            simplify_expression(lhs);
            simplify_expression(rhs);

            let keep_lhs = match kind {
                IRBinOpKind::Add if is_zero(lhs) => Some(false),
                IRBinOpKind::Add | IRBinOpKind::Sub | IRBinOpKind::Shl if is_zero(rhs) => {
                    Some(true)
                }
                IRBinOpKind::And if lhs == rhs && effect_free(lhs) => Some(true),
                _ => None,
            };
            if let Some(keep_lhs) = keep_lhs {
                let IRExpr::BinOp { lhs, rhs, .. } = std::mem::replace(expr, IRExpr::Bool(false))
                else {
                    unreachable!();
                };
                *expr = if keep_lhs { *lhs } else { *rhs };
            }
        }
        IRExpr::Not(inner) => {
            simplify_expression(inner);
            match inner.as_mut() {
                IRExpr::BinOp { kind, .. } => {
                    let opposite = match kind {
                        IRBinOpKind::Eq => Some(IRBinOpKind::Ne),
                        IRBinOpKind::Ne => Some(IRBinOpKind::Eq),
                        IRBinOpKind::UnsignedLt => Some(IRBinOpKind::UnsignedGe),
                        IRBinOpKind::UnsignedGe => Some(IRBinOpKind::UnsignedLt),
                        _ => None,
                    };
                    if let Some(opposite) = opposite {
                        *kind = opposite;
                        let IRExpr::Not(inner) = std::mem::replace(expr, IRExpr::Bool(false))
                        else {
                            unreachable!();
                        };
                        *expr = *inner;
                    }
                }
                IRExpr::Bool(value) => *expr = IRExpr::Bool(!*value),
                _ => {}
            }
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. } => simplify_expression(inner),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn simplify_instruction(instr: &mut IRInst) {
    match instr {
        IRInst::Assign { dest, src } => {
            simplify_expression(dest);
            simplify_expression(src);
        }
        IRInst::AssignVariable { value, .. }
        | IRInst::DeclareAndAssignVariable { value, .. }
        | IRInst::Return(Some(value))
        | IRInst::Jump(value) => {
            simplify_expression(value);
        }
        IRInst::LoadVariable { address, .. } | IRInst::StoreVariable { address, .. } => {
            simplify_expression(address);
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            simplify_expression(condition);
            for instr in then_branch.iter_mut().chain(else_branch) {
                simplify_instruction(instr);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            match condition {
                LoopCondition::Before { expression, .. }
                | LoopCondition::After { expression, .. } => simplify_expression(expression),
            }
            for (_, instr) in body {
                simplify_instruction(instr);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                simplify_expression(argument);
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

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        for (_, instr) in &mut function.body {
            simplify_instruction(instr);
        }
    }
}
