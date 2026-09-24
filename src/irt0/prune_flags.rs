//! Conservatively remove flags that are never read in the lifted program.
//! Overwritten writes are removed after tier 1 has established control flow.

use std::collections::HashSet;

use super::ir::{IRExpr, IRInst, NativeFlag, Program};

fn read_expr(expr: &IRExpr, used: &mut HashSet<NativeFlag>) {
    match expr {
        IRExpr::Flag(flag) => {
            used.insert(flag.clone());
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            read_expr(lhs, used);
            read_expr(rhs, used);
        }
        IRExpr::Deref { address: value, .. }
        | IRExpr::ExtractBytes { value, .. }
        | IRExpr::ZeroExtend { value, .. }
        | IRExpr::SignExtend { value, .. } => read_expr(value, used),
        _ => {}
    }
}

fn read_inst(instr: &IRInst, used: &mut HashSet<NativeFlag>) {
    match instr {
        IRInst::Asgn { dest, src } => {
            if !matches!(dest, IRExpr::Flag(_)) {
                read_expr(dest, used);
            }
            read_expr(src, used);
        }
        IRInst::If(condition, inner) => {
            read_expr(condition, used);
            read_inst(inner, used);
        }
        IRInst::Jmp(expr) | IRInst::Ret(Some(expr)) | IRInst::SetFlagsFrom(_, expr) => {
            read_expr(expr, used)
        }
        _ => {}
    }
}

pub fn tr(mut program: Program) -> Program {
    let mut used = HashSet::new();
    for (_, instr) in &program.instructions {
        read_inst(instr, &mut used);
    }
    program.instructions.retain_mut(|(_, instr)| match instr {
        IRInst::SetFlagsFrom(flags, _)
        | IRInst::ClearFlags(flags)
        | IRInst::InvalidateFlags(flags) => {
            flags.retain(|flag| used.contains(flag));
            !flags.is_empty()
        }
        IRInst::Asgn {
            dest: IRExpr::Flag(flag),
            ..
        } => used.contains(flag),
        _ => true,
    });
    program
}
