use std::{collections::HashSet, iter::Product};

use crate::{
    irt0::{self, IRExpr, IRInst, NativeFlag},
    irt1::prune_flags::FlagIR::WriteFlag,
};

type SourceIdx = usize;

// Minimal instruction set that lets us safely eliminate some flags before CFG recovery
#[derive(Debug)]
enum FlagIR {
    ReadFlag(NativeFlag),
    WriteFlag {
        flag: NativeFlag,
        source_idx: SourceIdx,
    },
    Boundary, // Flag analysis can only cross boundaries after CFG, later pass
}

// TODO: Refactor, these can be pure functions
fn gather_flag_ops_from_expr(x: &IRExpr) -> Vec<FlagIR> {
    let mut res: Vec<FlagIR> = vec![];
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
            _ = res.push(FlagIR::ReadFlag(flag.clone()));
        }
    }
    res
}

fn gather_flag_ops_from_instr(x: &mut IRInst, idx: SourceIdx) -> Vec<FlagIR> {
    let mut res: Vec<FlagIR> = vec![];
    match x {
        IRInst::Jmp(..) | IRInst::Ret(..) => {
            res.push(FlagIR::Boundary);
        }
        IRInst::SetFlagsFrom(flags, _) | IRInst::ClearFlags(flags) => {
            for flag in flags.iter() {
                res.push(FlagIR::WriteFlag {
                    flag: flag.clone(),
                    source_idx: idx,
                });
            }
            flags.clear();
        }
        IRInst::Asgn { src, .. } => {
            res.extend(gather_flag_ops_from_expr(src));
        }
        IRInst::If(expr, instr) => {
            res.extend(gather_flag_ops_from_expr(expr));
            res.extend(gather_flag_ops_from_instr(instr, idx));
        }
    }
    res
}

fn prune_program(program: irt0::Program, flag_code: Vec<FlagIR>) -> irt0::Program {
    // TODO: Clean up, we do not need another two iterators here
    let mut program = program;
    for f in flag_code {
        match f {
            WriteFlag { flag, source_idx } => match &mut program[source_idx].1 {
                IRInst::SetFlagsFrom(flags, _) | IRInst::ClearFlags(flags) => {
                    flags.insert(flag);
                }
                _ => (),
            },
            _ => (),
        }
    }

    let mut res: irt0::Program = vec![];
    for instr in program.into_iter() {
        match &instr.1 {
            IRInst::SetFlagsFrom(flags, _) | IRInst::ClearFlags(flags) => {
                if flags.len() > 0 {
                    res.push(instr);
                }
            }
            _ => res.push(instr),
        }
    }
    res
}

pub fn tr(program: irt0::Program) -> irt0::Program {
    let mut program = program;
    let mut flag_code: Vec<FlagIR> = vec![];
    for (idx, (_, instr)) in program.iter_mut().enumerate() {
        flag_code.extend(gather_flag_ops_from_instr(instr, idx));
    }

    // Gather info, clean up redundant flags. Must be reversed to account for potential jump targets
    let mut used_flags: HashSet<NativeFlag> = HashSet::new(); // Per program
    let mut dirty_flags: HashSet<NativeFlag> = HashSet::new(); // Per boundary
    let mut rev_code: Vec<FlagIR> = vec![];
    for f in flag_code.into_iter().rev() {
        match f {
            FlagIR::ReadFlag(flag) => {
                used_flags.insert(flag.clone());
                rev_code.push(FlagIR::ReadFlag(flag));
            }
            FlagIR::WriteFlag { flag, source_idx } => {
                if !dirty_flags.contains(&flag) {
                    dirty_flags.insert(flag.clone());
                    rev_code.push(FlagIR::WriteFlag {
                        flag,
                        source_idx: source_idx,
                    });
                }
            }
            FlagIR::Boundary => {
                dirty_flags.clear();
                rev_code.push(FlagIR::Boundary);
            }
        }
    }

    // Clean up unused flags
    let mut flag_code: Vec<FlagIR> = vec![];
    for f in rev_code.into_iter().rev() {
        match f {
            FlagIR::WriteFlag { flag, source_idx } => {
                if used_flags.contains(&flag) {
                    flag_code.push(FlagIR::WriteFlag { flag, source_idx });
                }
            }
            FlagIR::ReadFlag(..) | FlagIR::Boundary => {
                flag_code.push(f);
            }
        }
    }

    // Finalize
    prune_program(program, flag_code)
}
