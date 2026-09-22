use std::collections::HashMap;

use iced_x86::Register;

use crate::irt0::ir::{IRBinOpKind, IRExpr, IRInst, Program};

mod irt0;
mod irt1;

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

    let irt0program = irt0::lift(CODE, 0x140095be0);

    let mut edges: HashMap<usize, Option<usize>> = HashMap::new();
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
                Register::RIP => offset.clone(),
                _ => panic!("Unimplemented: {:?}", reg),
            },
            IRExpr::CU64(c) => c.clone().try_into().unwrap(),
            _ => panic!("Unimplemented: {:?}", expr),
        }
    }

    fn handle_instruction(
        edges: &mut HashMap<usize, Option<usize>>,
        offset: &usize,
        instr: &IRInst,
    ) {
        match instr {
            IRInst::If(_, inner) => {
                handle_instruction(edges, offset, inner);
            }
            IRInst::Jmp(expr) => {
                let target = try_eval_addr(expr, offset);
                edges.insert(offset.clone(), Some(target));
            }
            IRInst::Ret(_) => _ = edges.insert(offset.clone(), None),
            _ => (),
        }
    }

    for (offset, instr) in &irt0program {
        handle_instruction(&mut edges, offset, instr);
    }

    for (src, dest) in &edges {
        let mut inst: Option<&IRInst> = None;
        for (offset, instr) in &irt0program {
            if *offset == *src {
                inst = Some(instr);
                break;
            }
        }

        println!("\n=========\n{:?}\n-----------", inst.unwrap());
        if let Some(dest) = dest {
            for (offset, instr) in &irt0program {
                if offset < dest {
                    continue;
                }
                println!("{:?}", instr);
            }
        } else {
            println!("<EXIT>")
        }
    }

    println!("{:?}", edges)
}
