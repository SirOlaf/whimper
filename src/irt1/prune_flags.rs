use std::collections::HashSet;

use super::ir::{IRExpr, IRInst, NativeFlag, Program, SyntheticFunction};

fn read_expr(expr: &IRExpr, live: &mut HashSet<NativeFlag>) {
    match expr {
        IRExpr::Flag(flag) => {
            live.insert(flag.clone());
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            read_expr(lhs, live);
            read_expr(rhs, live);
        }
        IRExpr::Deref { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::SignExtend { value: inner, .. }
        | IRExpr::Not(inner) => read_expr(inner, live),
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
        IRInst::SetFlagsFrom { .. }
        | IRInst::ClearFlags { .. }
        | IRInst::InvalidateFlags { .. } => {
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
            IRInst::Assign {
                dest: IRExpr::Flag(flag),
                src,
            } => {
                if live.remove(&flag) {
                    read_expr(&src, &mut live);
                    kept.push((
                        offset,
                        IRInst::Assign {
                            dest: IRExpr::Flag(flag),
                            src,
                        },
                    ));
                }
            }
            IRInst::InvalidateFlags { flags } => {
                assert!(
                    flags.is_disjoint(&live),
                    "undefined flags used at 0x{offset:x}"
                );
            }
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
        IRInst::CallSynthetic { function, .. } => {
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

fn require_lowered_expr(expr: &IRExpr, function: usize, offset: usize) {
    match expr {
        IRExpr::Flag(flag) => {
            panic!("tier 1 left {flag:?} in fn_{function} at 0x{offset:x}; lower it before tier 2")
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            require_lowered_expr(lhs, function, offset);
            require_lowered_expr(rhs, function, offset);
        }
        IRExpr::Deref { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::SignExtend { value: inner, .. }
        | IRExpr::Not(inner) => require_lowered_expr(inner, function, offset),
        _ => {}
    }
}

fn require_lowered_inst(instr: &IRInst, function: usize, offset: usize) {
    match instr {
        IRInst::SetFlagsFrom { flags, .. }
        | IRInst::ClearFlags { flags }
        | IRInst::InvalidateFlags { flags } => panic!(
            "tier 1 left native flag writes {flags:?} in fn_{function} at 0x{offset:x}; lower them before tier 2"
        ),
        IRInst::Assign { dest, src } => {
            require_lowered_expr(dest, function, offset);
            require_lowered_expr(src, function, offset);
        }
        IRInst::AssignVariable { value, .. }
        | IRInst::Return(Some(value))
        | IRInst::Jump(value) => require_lowered_expr(value, function, offset),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            require_lowered_expr(condition, function, offset);
            require_lowered_inst(then_branch, function, offset);
            require_lowered_inst(else_branch, function, offset);
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                require_lowered_expr(argument, function, offset);
            }
        }
        IRInst::Return(None) | IRInst::DeclareVariable { .. } | IRInst::End => {}
    }
}

pub fn tr(mut program: Program) -> Program {
    for function in &mut program.functions {
        prune_function(function);
    }
    for (id, function) in program.functions.iter().enumerate() {
        assert!(
            function.external_flags.is_empty(),
            "tier 1 left external flags {:?} in fn_{id}; lower them before tier 2",
            function.external_flags
        );
        for (_, instr) in &function.body {
            check_calls(instr, &program.functions);
        }
        for (offset, instr) in &function.body {
            require_lowered_inst(instr, id, *offset);
        }
    }
    program
}
