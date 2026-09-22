use std::collections::HashSet;

use crate::irt0::{self, IRExpr, IRInst, NativeFlag};

enum FlagSource<'a> {
    Instr(&'a IRInst),
    Expr(&'a IRExpr),
}

// Minimal instruction set that lets us safely eliminate some flags before CFG recovery
#[derive(Debug)]
enum FlagIR {
    ReadFlag(NativeFlag),
    WriteFlag(NativeFlag),
    Boundary, // Flag analysis can only cross boundaries after CFG, later pass
}

struct FlagInstr<'a> {
    source: FlagSource<'a>,
    instr: FlagIR,
}

// TODO: Refactor, these can be pure functions
fn gather_flag_ops_from_expr<'a>(x: &'a IRExpr) -> Vec<FlagInstr<'a>> {
    let mut res: Vec<FlagInstr<'a>> = vec![];
    match x {
        IRExpr::Reg(..)
        | IRExpr::Addr(..)
        | IRExpr::CU8(..)
        | IRExpr::CU32(..)
        | IRExpr::CU64(..) => (),
        IRExpr::BinOp { lhs, rhs, .. } => {
            res.extend(gather_flag_ops_from_expr(lhs));
            res.extend(gather_flag_ops_from_expr(rhs));
        }
        IRExpr::Deref(expr) | IRExpr::MSB(expr) | IRExpr::LSB(expr) => {
            res.extend(gather_flag_ops_from_expr(expr));
        }
        IRExpr::Flag(flag) => {
            _ = res.push(FlagInstr {
                source: FlagSource::Expr(x),
                instr: FlagIR::ReadFlag(flag.clone()),
            })
        }
    }
    res
}

fn gather_flag_ops_from_instr<'a>(x: &'a IRInst) -> Vec<FlagInstr<'a>> {
    let mut res: Vec<FlagInstr> = vec![];
    match x {
        IRInst::Jmp(..) | IRInst::Ret(..) => {
            res.push(FlagInstr {
                source: FlagSource::Instr(x),
                instr: FlagIR::Boundary,
            });
        }
        IRInst::SetFlagsFrom(flags, _) | IRInst::ClearFlags(flags) => {
            for flag in flags {
                res.push(FlagInstr {
                    source: FlagSource::Instr(x),
                    instr: FlagIR::WriteFlag(flag.clone()),
                })
            }
        }
        IRInst::Asgn { src, .. } => {
            res.extend(gather_flag_ops_from_expr(src));
        }
        IRInst::If(expr, instr) => {
            res.extend(gather_flag_ops_from_expr(expr));
            res.extend(gather_flag_ops_from_instr(instr));
        }
    }
    res
}

pub fn tr(x: irt0::Program) -> irt0::Program {
    let mut flag_code: Vec<FlagInstr> = vec![];
    for (_, instr) in &x {
        flag_code.extend(gather_flag_ops_from_instr(&instr));
    }

    // Gather info, clean up redundant flags
    let mut used_flags: HashSet<NativeFlag> = HashSet::new(); // Per program
    let mut dirty_flags: HashSet<NativeFlag> = HashSet::new(); // Per boundary
    let mut rev_code: Vec<FlagInstr> = vec![];
    for f in flag_code.into_iter().rev() {
        match f.instr {
            FlagIR::ReadFlag(flag) => {
                used_flags.insert(flag.clone());
                rev_code.push(FlagInstr {
                    source: f.source,
                    instr: FlagIR::ReadFlag(flag),
                })
            }
            FlagIR::WriteFlag(flag) => {
                if !dirty_flags.contains(&flag) {
                    dirty_flags.insert(flag.clone());
                    rev_code.push(FlagInstr {
                        source: f.source,
                        instr: FlagIR::WriteFlag(flag),
                    });
                }
            }
            FlagIR::Boundary => {
                dirty_flags.clear();
                rev_code.push(FlagInstr {
                    source: f.source,
                    instr: FlagIR::Boundary,
                });
            }
        }
    }

    // Clean up unused flags
    let mut flag_code: Vec<FlagInstr> = vec![];
    for f in rev_code.into_iter().rev() {
        match f.instr {
            FlagIR::WriteFlag(flag) => {
                if used_flags.contains(&flag) {
                    flag_code.push(FlagInstr {
                        source: f.source,
                        instr: FlagIR::WriteFlag(flag),
                    });
                }
            }
            FlagIR::ReadFlag(..) | FlagIR::Boundary => {
                flag_code.push(f);
            }
        }
    }

    for f in flag_code {
        match f.source {
            FlagSource::Instr(instr) => {}
            FlagSource::Expr(expr) => {}
        }
    }

    panic!()
}
