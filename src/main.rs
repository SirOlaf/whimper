use std::collections::HashSet;

use iced_x86::Register;

use crate::irt0::ir::{IRBinOpKind, IRExpr, IRInst, NativeFlag, Program};

mod irt0;
mod irt1;

struct Partition {
    entry_point: usize,
    external_flags: HashSet<NativeFlag>,
}

fn main() {
    const CODE: &[u8] = &[
        0x4c, 0x8b, 0xc1, 0x8b, 0x49, 0x2c, 0x41, 0x03, 0x48, 0x24, 0x41, 0x8b, 0x40, 0x30, 0x41,
        0x01, 0x40, 0x28, 0x4d, 0x8b, 0x48, 0x38, 0x41, 0x8b, 0x40, 0x28, 0x41, 0x89, 0x48, 0x24,
        0x41, 0x8b, 0x11, 0x85, 0xd2, 0x74, 0x1b, 0xc1, 0xe2, 0x10, 0x3b, 0xca, 0x72, 0x14, 0x0f,
        0x1f, 0x40, 0x00, 0x2b, 0xca, 0x41, 0x89, 0x48, 0x24, 0x41, 0x8b, 0x11, 0xc1, 0xe2, 0x10,
        0x3b, 0xca, 0x73, 0xf0, 0x41, 0x8b, 0x48, 0x34, 0x85, 0xc9, 0x74, 0x12, 0xc1, 0xe1, 0x10,
        0x3b, 0xc1, 0x72, 0x0b, 0x90, 0x2b, 0xc1, 0x3b, 0xc1, 0x73, 0xfa, 0x41, 0x89, 0x40, 0x28,
        0x41, 0x8b, 0x40, 0x10, 0xc3,
    ];
    let base_offset = 0x140095be0;

    let irt0program = irt0::lift(CODE, base_offset);

    for p in &irt0program {
        println!("{:?}", p.1);
    }

    let mut partition_entries: HashSet<usize> = HashSet::new();
    partition_entries.insert(base_offset);
    fn try_eval_addr(expr: &IRExpr, offset: &usize) -> usize {
        match expr {
            IRExpr::BinOp { kind, lhs, rhs } => {
                let lhs = try_eval_addr(lhs, offset);
                let rhs = try_eval_addr(rhs, offset);
                match kind {
                    IRBinOpKind::Add => lhs + rhs,
                    _ => panic!("Unimplemented: {:?}", kind),
                }
            }
            IRExpr::Reg(reg) => match reg {
                Register::RIP => *offset,
                _ => panic!("Unimplemented: {:?}", reg),
            },
            IRExpr::CU64(c) => (*c).try_into().unwrap(),
            _ => panic!("Unimplemented: {:?}", expr),
        }
    }

    fn handle_instruction(entries: &mut HashSet<usize>, offset: &usize, instr: &IRInst) {
        match instr {
            IRInst::If(_, inner) => {
                handle_instruction(entries, offset, inner);
            }
            IRInst::Jmp(expr) => {
                let target = try_eval_addr(expr, offset);
                entries.insert(target);
            }
            _ => (),
        }
    }

    for (offset, instr) in &irt0program {
        handle_instruction(&mut partition_entries, offset, instr);
    }

    // Every jump destination is a partition entry point
    // A partition lasts from entry to jump and defines what flags are local
    println!("{:?}", partition_entries);

    let mut partitions: Vec<Partition> = Vec::new();

    fn analyze_expression(
        e: &IRExpr,
        live_flags: &HashSet<NativeFlag>,
        external_flags: &mut HashSet<NativeFlag>,
    ) {
        match e {
            IRExpr::BinOp { lhs, rhs, .. } => {
                analyze_expression(lhs, live_flags, external_flags);
                analyze_expression(rhs, live_flags, external_flags);
            }
            IRExpr::Flag(flag) if !live_flags.contains(flag) => {
                external_flags.insert(flag.clone());
            }
            _ => {}
        }
    }

    fn analyze_partition(entry: &usize, program: &Program) -> Partition {
        let mut live_flags: HashSet<NativeFlag> = HashSet::new();
        let mut external_flags: HashSet<NativeFlag> = HashSet::new();
        for (offset, instr) in program {
            if offset < entry {
                continue;
            }
            match instr {
                IRInst::SetFlagsFrom(flags, _) => {
                    live_flags.extend(flags.iter().cloned());
                }
                IRInst::ClearFlags(flags) => {
                    flags.iter().for_each(|x| _ = live_flags.remove(x));
                }
                IRInst::If(expr, _) => {
                    analyze_expression(expr, &live_flags, &mut external_flags);
                }
                _ => {}
            }
        }
        Partition {
            entry_point: *entry,
            external_flags,
        }
    }

    for p in partition_entries {
        partitions.push(analyze_partition(&p, &irt0program));
    }

    for p in partitions {
        assert!(p.external_flags.is_empty());
    }
}
