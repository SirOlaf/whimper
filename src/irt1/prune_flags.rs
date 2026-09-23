use std::collections::HashSet;

use crate::irt0::ir::{IRExpr as IRT0Expr, IRInst as IRT0Inst, NativeFlag};

use super::ir::{IRExpr, IRInst, Program, SyntheticFunction};

fn read_native(expr: &IRT0Expr, live: &mut HashSet<NativeFlag>) {
    match expr {
        IRT0Expr::Flag(flag) => {
            live.insert(flag.clone());
        }
        IRT0Expr::BinOp { lhs, rhs, .. } => {
            read_native(lhs, live);
            read_native(rhs, live);
        }
        IRT0Expr::Deref(inner) => read_native(inner, live),
        _ => {}
    }
}

fn read_expr(expr: &IRExpr, live: &mut HashSet<NativeFlag>) {
    match expr {
        IRExpr::Native(expr) => read_native(expr, live),
        IRExpr::Eq(lhs, rhs) | IRExpr::UnsignedLt(lhs, rhs) | IRExpr::Or(lhs, rhs) => {
            read_expr(lhs, live);
            read_expr(rhs, live);
        }
        IRExpr::Not(inner) => read_expr(inner, live),
        IRExpr::Variable(_) | IRExpr::Bool(_) => {}
    }
}

fn read_linear(instr: &IRT0Inst, live: &mut HashSet<NativeFlag>) {
    match instr {
        IRT0Inst::Asgn { dest, src } => {
            read_native(dest, live);
            read_native(src, live);
        }
        IRT0Inst::If(condition, inner) => {
            read_native(condition, live);
            read_linear(inner, live);
        }
        IRT0Inst::Jmp(expr) | IRT0Inst::Ret(Some(expr)) => read_native(expr, live),
        IRT0Inst::SetFlagsFrom(_, _) | IRT0Inst::ClearFlags(_) => {
            unreachable!("flag writes are handled by the backward pass")
        }
        IRT0Inst::Ret(None) => {}
    }
}

fn read_inst(instr: &IRInst, live: &mut HashSet<NativeFlag>) {
    match instr {
        IRInst::Linear(instr) => read_linear(instr, live),
        IRInst::Jump(expr) => read_native(expr, live),
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
        IRInst::DeclareVariable { .. } | IRInst::CallSynthetic { .. } | IRInst::End => {}
    }
}

fn prune_function(function: &mut SyntheticFunction) {
    let mut live = HashSet::new();
    let mut kept = Vec::new();
    for (offset, instr) in std::mem::take(&mut function.body).into_iter().rev() {
        match instr {
            IRInst::Linear(IRT0Inst::SetFlagsFrom(flags, expr)) => {
                let needed = flags.intersection(&live).cloned().collect::<HashSet<_>>();
                live.retain(|flag| !flags.contains(flag));
                if !needed.is_empty() {
                    read_native(&expr, &mut live);
                    kept.push((offset, IRInst::Linear(IRT0Inst::SetFlagsFrom(needed, expr))));
                }
            }
            IRInst::Linear(IRT0Inst::ClearFlags(flags)) => {
                let needed = flags.intersection(&live).cloned().collect::<HashSet<_>>();
                live.retain(|flag| !flags.contains(flag));
                if !needed.is_empty() {
                    kept.push((offset, IRInst::Linear(IRT0Inst::ClearFlags(needed))));
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
