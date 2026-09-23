use std::collections::HashSet;

use iced_x86::{
    Code, Decoder, DecoderOptions, Instruction, MemorySize, Mnemonic, OpKind, Register,
};

pub type Program = Vec<(usize, IRInst)>;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum NativeFlag {
    Carry,
    Parity,
    AuxCarry,
    Zero,
    Sign,
    Trap,
    InterruptEnable,
    Direction,
    Overflow,
}

#[derive(Debug, Clone)]
pub enum IRBinOpKind {
    Add,
    Sub,

    Shl,

    And,

    Eq,
}

#[derive(Debug, Clone)]
pub enum IRExpr {
    BinOp {
        kind: IRBinOpKind,
        lhs: Box<IRExpr>,
        rhs: Box<IRExpr>,
    },

    Deref(Box<IRExpr>),

    // Native
    Reg(Register),
    Flag(NativeFlag),

    // Consts
    CU8(u8),
    CU32(u32),
    CU64(u64),
}

#[derive(Debug, Clone)]
pub enum IRInst {
    Asgn { dest: IRExpr, src: IRExpr },

    If(IRExpr, Box<IRInst>),
    Jmp(IRExpr),
    Ret(Option<IRExpr>),

    SetFlagsFrom(HashSet<NativeFlag>, IRExpr),
    ClearFlags(HashSet<NativeFlag>),
}

fn lift_op(x: Instruction, i: u32) -> IRExpr {
    // Adapted from iced's try_virtual_address
    match x.op_kind(i) {
        OpKind::Memory => {
            let base_reg = x.memory_base();
            let index_reg = x.memory_index();
            let mem_size = x.memory_size();

            let mut res = match mem_size {
                MemorySize::UInt32 => IRExpr::CU32(x.memory_displacement32()),
                MemorySize::UInt64 => IRExpr::CU64(x.memory_displacement64()),
                _ => panic!("Unimplemented {:?}", mem_size),
            };

            match base_reg {
                Register::None | Register::EIP | Register::RIP => {}
                _ => {
                    res = IRExpr::BinOp {
                        kind: IRBinOpKind::Add,
                        lhs: Box::new(IRExpr::Reg(base_reg)),
                        rhs: Box::new(res),
                    }
                }
            }

            if index_reg != Register::None {
                if x.vsib().is_none() {
                    unimplemented!()
                } else {
                    res = IRExpr::BinOp {
                        kind: IRBinOpKind::Add,
                        lhs: Box::new(IRExpr::Reg(index_reg)),
                        rhs: Box::new(res),
                    }
                }
            }

            IRExpr::Deref(Box::new(res))
        }
        OpKind::Register => IRExpr::Reg(x.op_register(i)),
        OpKind::NearBranch64 => IRExpr::CU64(x.near_branch_target()),
        OpKind::Immediate8 => IRExpr::CU8(x.immediate8()),
        _ => {
            panic!("Unimplemented address kind: {:?}", x.op_kind(i));
        }
    }
}

fn lift_mov(x: Instruction) -> Vec<IRInst> {
    match x.code() {
        Code::Mov_r64_rm64 | Code::Mov_r32_rm32 | Code::Mov_rm32_r32 => {
            vec![IRInst::Asgn {
                dest: lift_op(x, 0),
                src: lift_op(x, 1),
            }]
        }
        _ => {
            panic!("{:?}", x)
        }
    }
}

fn lift_add(x: Instruction) -> Vec<IRInst> {
    match x.code() {
        Code::Add_r32_rm32 | Code::Add_rm32_r32 => {
            let add_expr = IRExpr::BinOp {
                kind: IRBinOpKind::Add,
                lhs: Box::new(lift_op(x, 0)),
                rhs: Box::new(lift_op(x, 1)),
            };
            vec![
                IRInst::SetFlagsFrom(
                    HashSet::from([
                        NativeFlag::Carry,
                        NativeFlag::AuxCarry,
                        NativeFlag::Overflow,
                        NativeFlag::Parity,
                        NativeFlag::Sign,
                        NativeFlag::Zero,
                    ]),
                    add_expr.clone(),
                ),
                IRInst::Asgn {
                    dest: lift_op(x, 0),
                    src: add_expr.clone(),
                },
            ]
        }
        _ => {
            panic!("{:?}", x)
        }
    }
}

fn lift_sub(x: Instruction) -> Vec<IRInst> {
    match x.code() {
        Code::Sub_r32_rm32 => {
            let sub_expr = IRExpr::BinOp {
                kind: IRBinOpKind::Sub,
                lhs: Box::new(lift_op(x, 0)),
                rhs: Box::new(lift_op(x, 1)),
            };
            vec![
                IRInst::SetFlagsFrom(
                    HashSet::from([
                        NativeFlag::Overflow,
                        NativeFlag::Sign,
                        NativeFlag::Zero,
                        NativeFlag::AuxCarry,
                        NativeFlag::Parity,
                        NativeFlag::Carry,
                    ]),
                    sub_expr.clone(),
                ),
                IRInst::Asgn {
                    dest: lift_op(x, 0),
                    src: sub_expr.clone(),
                },
            ]
        }
        _ => {
            panic!("{:?}", x)
        }
    }
}

fn lift_cond(x: Instruction) -> Vec<IRInst> {
    match x.mnemonic() {
        Mnemonic::Test => {
            let mut res = vec![IRInst::ClearFlags(HashSet::from([
                NativeFlag::Carry,
                NativeFlag::Overflow,
            ]))];
            match x.code() {
                Code::Test_rm32_r32 => {
                    let and_expr = IRExpr::BinOp {
                        kind: IRBinOpKind::And,
                        lhs: Box::new(lift_op(x, 1)),
                        rhs: Box::new(lift_op(x, 1)),
                    };
                    res.extend(vec![IRInst::SetFlagsFrom(
                        HashSet::from([NativeFlag::Sign, NativeFlag::Zero, NativeFlag::Parity]),
                        and_expr,
                    )]);
                }
                _ => {
                    panic!("Unlifted test: {:?}", x)
                }
            }
            res
        }
        Mnemonic::Cmp => match x.code() {
            Code::Cmp_r32_rm32 => {
                let sub_expr = IRExpr::BinOp {
                    kind: IRBinOpKind::Sub,
                    lhs: Box::new(lift_op(x, 0)),
                    rhs: Box::new(lift_op(x, 1)),
                };
                vec![IRInst::SetFlagsFrom(
                    HashSet::from([
                        NativeFlag::Carry,
                        NativeFlag::Sign,
                        NativeFlag::Zero,
                        NativeFlag::AuxCarry,
                        NativeFlag::Parity,
                        NativeFlag::Carry,
                    ]),
                    sub_expr,
                )]
            }
            _ => panic!("{:?}", x),
        },
        _ => {
            panic!("Unlifted cond: {:?}", x)
        }
    }
}

fn lift_jmp(x: Instruction) -> Vec<IRInst> {
    match x.code() {
        Code::Je_rel8_64 => {
            vec![IRInst::If(
                IRExpr::BinOp {
                    kind: IRBinOpKind::Eq,
                    lhs: Box::new(IRExpr::Flag(NativeFlag::Zero)),
                    rhs: Box::new(IRExpr::CU8(0)),
                },
                Box::new(IRInst::Jmp(lift_op(x, 0))),
            )]
        }
        Code::Jb_rel8_64 => {
            vec![IRInst::If(
                IRExpr::BinOp {
                    kind: IRBinOpKind::Eq,
                    lhs: Box::new(IRExpr::Flag(NativeFlag::Carry)),
                    rhs: Box::new(IRExpr::CU8(1)),
                },
                Box::new(IRInst::Jmp(lift_op(x, 0))),
            )]
        }
        Code::Jae_rel8_64 => {
            vec![IRInst::If(
                IRExpr::BinOp {
                    kind: IRBinOpKind::Eq,
                    lhs: Box::new(IRExpr::Flag(NativeFlag::Carry)),
                    rhs: Box::new(IRExpr::CU8(0)),
                },
                Box::new(IRInst::Jmp(lift_op(x, 0))),
            )]
        }
        _ => panic!("{:?}", x),
    }
}

fn lift_shl(x: Instruction) -> Vec<IRInst> {
    match x.code() {
        Code::Shl_rm32_imm8 => {
            let expr = IRExpr::BinOp {
                kind: IRBinOpKind::Shl,
                lhs: Box::new(lift_op(x, 0)),
                rhs: Box::new(lift_op(x, 1)),
            };
            vec![
                IRInst::SetFlagsFrom(
                    HashSet::from([
                        NativeFlag::Sign,
                        NativeFlag::Zero,
                        NativeFlag::AuxCarry,
                        NativeFlag::Parity,
                        NativeFlag::Carry,
                    ]),
                    expr.clone(),
                ),
                IRInst::Asgn {
                    dest: lift_op(x, 0),
                    src: expr.clone(),
                },
            ]
        }
        _ => panic!("{:?}", x),
    }
}

fn lift_ret(x: Instruction) -> Vec<IRInst> {
    match x.code() {
        Code::Retnq => {
            vec![IRInst::Ret(None)]
        }
        _ => panic!("{:?}", x),
    }
}

pub fn lift_to_irt0(code: &[u8], base_offset: usize) -> Program {
    let mut decoder = Decoder::with_ip(
        64,
        code,
        base_offset.try_into().unwrap(),
        DecoderOptions::NONE,
    );

    let mut instruction = Instruction::default();

    let mut res: Program = vec![];
    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);

        let tmp_instr = match instruction.mnemonic() {
            Mnemonic::Mov => Some(lift_mov(instruction)),
            Mnemonic::Add => Some(lift_add(instruction)),
            Mnemonic::Sub => Some(lift_sub(instruction)),
            Mnemonic::Test | Mnemonic::Cmp => Some(lift_cond(instruction)),
            Mnemonic::Je | Mnemonic::Jb | Mnemonic::Jae => Some(lift_jmp(instruction)),
            Mnemonic::Shl => Some(lift_shl(instruction)),
            Mnemonic::Ret => Some(lift_ret(instruction)),
            Mnemonic::Nop => None,
            _ => {
                println!("{:?}", instruction);
                panic!("Unlifted instruction: {:?}", instruction.mnemonic())
            }
        };
        if let Some(instrs) = tmp_instr {
            res.extend(
                instrs
                    .iter()
                    .map(|x| (instruction.ip().try_into().unwrap(), x.clone())),
            );
        }
    }

    res
}
