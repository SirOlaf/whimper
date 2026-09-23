use std::collections::HashSet;

use crate::irt0::ir::NativeFlag;

use super::ir::{IRExpr, IRInst, Program, SyntheticFunction};

fn read_expr(expr: &IRExpr, live: &mut HashSet<NativeFlag>) {
    match expr {
        IRExpr::Flag(flag) => {
            live.insert(flag.clone());
        }
        IRExpr::BinOp { lhs, rhs, .. }
        | IRExpr::Eq(lhs, rhs)
        | IRExpr::UnsignedLt(lhs, rhs)
        | IRExpr::Or(lhs, rhs) => {
            read_expr(lhs, live);
            read_expr(rhs, live);
        }
        IRExpr::Deref(inner) | IRExpr::Not(inner) => read_expr(inner, live),
        IRExpr::Reg(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn read_inst(instr: &IRInst, live: &mut HashSet<NativeFlag>) {
    match instr {
        IRInst::Assign { dest, src } => {
            read_expr(dest, live);
            read_expr(src, live);
        }
        IRInst::Jump(expr) | IRInst::Return(Some(expr)) => read_expr(expr, live),
        IRInst::AssignVariable { value, .. } => read_expr(value, live),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            read_expr(condition, live);
            read_inst(then_branch, live);
            read_inst(else_branch, live);
        }
        IRInst::SetFlagsFrom { .. } | IRInst::ClearFlags { .. } => {
            unreachable!("flag writes are handled by the backward pass")
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::CallSynthetic { .. }
        | IRInst::End => {}
    }
}

fn prune_function(function: &mut SyntheticFunction) {
    let mut live = HashSet::new();
    let mut kept = Vec::new();
    for (offset, instr) in std::mem::take(&mut function.body).into_iter().rev() {
        match instr {
            IRInst::SetFlagsFrom { flags, expr } => {
                let needed = flags.intersection(&live).cloned().collect::<HashSet<_>>();
                live.retain(|flag| !flags.contains(flag));
                if !needed.is_empty() {
                    read_expr(&expr, &mut live);
                    kept.push((
                        offset,
                        IRInst::SetFlagsFrom {
                            flags: needed,
                            expr,
                        },
                    ));
                }
            }
            IRInst::ClearFlags { flags } => {
                let needed = flags.intersection(&live).cloned().collect::<HashSet<_>>();
                live.retain(|flag| !flags.contains(flag));
                if !needed.is_empty() {
                    kept.push((offset, IRInst::ClearFlags { flags: needed }));
                }
            }
            instr => {
                read_inst(&instr, &mut live);
                kept.push((offset, instr));
            }
        }
    }
    kept.reverse();
    function.body = kept;
    function.external_flags = live;
}

fn check_calls(instr: &IRInst, functions: &[SyntheticFunction]) {
    match instr {
        IRInst::CallSynthetic { function } => {
            let callee = &functions[function.id];
            if !callee.external_flags.is_empty() {
                unimplemented!(
                    "synthetic function {} needs external flags {:?}; call arguments are needed",
                    function.id,
                    callee.external_flags
                );
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            check_calls(then_branch, functions);
            check_calls(else_branch, functions);
        }
        _ => {}
    }
}

pub fn tr(mut program: Program) -> Program {
    for function in &mut program.functions {
        prune_function(function);
    }
    for function in &program.functions {
        for (_, instr) in &function.body {
            check_calls(instr, &program.functions);
        }
    }
    program
}
