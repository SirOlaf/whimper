use std::collections::HashSet;

use iced_x86::{
    Code, Decoder, DecoderOptions, Instruction, Mnemonic,
    OpKind::{self, NearBranch64},
    Register,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum CpuFlag {
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

pub type Program = Vec<Instr>;

#[derive(Debug)]
pub struct Instr {
    pub src_addr: usize,
    pub kind: InstrKind,
}

#[derive(Debug, Clone)]
pub enum BinOpKind {
    Xor,
    Add,
    Mul,
    And,
    Eq,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Register(Register),
    Flag(CpuFlag),
    Deref(Box<ExprKind>),
    CastByteSize(u8, Box<ExprKind>),       // Zero extend or truncate
    CastByteSizeSigned(u8, Box<ExprKind>), // Sign extend
    BinOp {
        kind: BinOpKind,
        lhs: Box<ExprKind>,
        rhs: Box<ExprKind>,
    },
    Not(Box<ExprKind>),

    FitsByteSize(u8, Box<ExprKind>),

    CU8(u8),
    CU32(u32),
    CU64(u64),
}

#[derive(Debug)]
pub enum InstrKind {
    Asgn { dest: ExprKind, src: ExprKind },
    If(ExprKind, Box<InstrKind>),
    Jmp(ExprKind),

    ClearFlags(HashSet<CpuFlag>),
    InvalidateFlags(HashSet<CpuFlag>),
    AsgnFlagsFrom(HashSet<CpuFlag>, ExprKind),

    Ret { stack_bytes: Option<usize> },
}

fn lift_operand(n: u32, x: Instruction) -> ExprKind {
    match x.op_kind(n) {
        OpKind::Register => ExprKind::Register(x.op_register(0)),
        OpKind::Immediate32 => ExprKind::CU32(x.immediate32()),
        OpKind::NearBranch64 => ExprKind::CU64(x.near_branch_target()),
        OpKind::Memory => {
            // Adapted from iced's try_virtual_address
            assert!(
                !matches!(x.segment_prefix(), Register::FS | Register::GS),
                "unsupported segment base: {x:?}"
            );
            let base_reg = x.memory_base();

            let offset = x.memory_displacement64();
            let mut expr = ExprKind::CU64(offset);
            let index_reg = x.memory_index();
            match base_reg {
                Register::None => {}
                Register::RIP | Register::EIP => {
                    expr = ExprKind::BinOp {
                        kind: BinOpKind::Add,
                        lhs: Box::new(ExprKind::CU64(x.ip_rel_memory_address())),
                        rhs: Box::new(expr),
                    }
                }
                _ => {
                    expr = ExprKind::BinOp {
                        kind: BinOpKind::Add,
                        lhs: Box::new(ExprKind::Register(base_reg)),
                        rhs: Box::new(expr),
                    }
                }
            };
            if index_reg != Register::None {
                if x.is_vsib() {
                    todo!()
                } else {
                    expr = ExprKind::BinOp {
                        kind: BinOpKind::Add,
                        lhs: Box::new(expr),
                        rhs: Box::new(ExprKind::BinOp {
                            kind: BinOpKind::Mul,
                            lhs: Box::new(ExprKind::Register(index_reg)),
                            rhs: Box::new(ExprKind::CU8(x.memory_index_scale() as u8)),
                        }),
                    }
                }
            }

            expr
        }
        _ => todo!("Op {} ({:?}), {:?}", n, x.op_kind(n), x),
    }
}

fn lift_mov(x: Instruction) -> Vec<InstrKind> {
    vec![InstrKind::Asgn {
        dest: lift_operand(0, x),
        src: lift_operand(1, x),
    }]
}

fn lift_movzx(x: Instruction) -> Vec<InstrKind> {
    match x.code() {
        Code::Movzx_r32_rm8 => {
            vec![InstrKind::Asgn {
                dest: lift_operand(0, x),
                src: ExprKind::CastByteSize(
                    1,
                    Box::new(ExprKind::Deref(Box::new(lift_operand(1, x)))),
                ),
            }]
        }
        _ => todo!("{:?}", x),
    }
}

fn lift_movsx(x: Instruction) -> Vec<InstrKind> {
    match x.code() {
        Code::Movsx_r32_rm8 => {
            vec![InstrKind::Asgn {
                dest: lift_operand(0, x),
                src: ExprKind::CastByteSizeSigned(
                    1,
                    Box::new(ExprKind::Deref(Box::new(lift_operand(1, x)))),
                ),
            }]
        }
        _ => todo!("{:?}", x),
    }
}

fn lift_xor(x: Instruction) -> Vec<InstrKind> {
    match x.code() {
        Code::Xor_r32_rm32 => {
            let expr = ExprKind::BinOp {
                kind: BinOpKind::Xor,
                lhs: Box::new(lift_operand(0, x)),
                rhs: Box::new(lift_operand(1, x)),
            };
            vec![
                InstrKind::ClearFlags(HashSet::from([CpuFlag::Overflow, CpuFlag::Carry])),
                InstrKind::AsgnFlagsFrom(
                    HashSet::from([CpuFlag::Sign, CpuFlag::Zero, CpuFlag::Parity]),
                    expr.clone(),
                ),
                InstrKind::InvalidateFlags(HashSet::from([CpuFlag::AuxCarry])),
                InstrKind::Asgn {
                    dest: lift_operand(0, x),
                    src: expr,
                },
            ]
        }
        _ => todo!("{:?}", x),
    }
}

fn lift_add(x: Instruction) -> Vec<InstrKind> {
    match x.code() {
        Code::Add_r32_rm32 => {
            let expr = ExprKind::BinOp {
                kind: BinOpKind::Add,
                lhs: Box::new(lift_operand(0, x)),
                rhs: Box::new(lift_operand(1, x)),
            };
            vec![
                InstrKind::AsgnFlagsFrom(
                    HashSet::from([
                        CpuFlag::Overflow,
                        CpuFlag::Sign,
                        CpuFlag::Zero,
                        CpuFlag::AuxCarry,
                        CpuFlag::Parity,
                    ]),
                    expr.clone(),
                ),
                InstrKind::Asgn {
                    dest: lift_operand(0, x),
                    src: expr,
                },
            ]
        }
        _ => todo!("{:?}", x),
    }
}

fn lift_cond(x: Instruction) -> Vec<InstrKind> {
    match x.mnemonic() {
        Mnemonic::Test => {
            let expr = ExprKind::BinOp {
                kind: BinOpKind::And,
                lhs: Box::new(lift_operand(0, x)),
                rhs: Box::new(lift_operand(1, x)),
            };
            vec![
                InstrKind::ClearFlags(HashSet::from([CpuFlag::Overflow, CpuFlag::Carry])),
                InstrKind::AsgnFlagsFrom(
                    HashSet::from([CpuFlag::Sign, CpuFlag::Zero, CpuFlag::Parity]),
                    expr,
                ),
                InstrKind::InvalidateFlags(HashSet::from([CpuFlag::AuxCarry])),
            ]
        }
        _ => todo!("{:?}", x),
    }
}

fn lift_jmp(x: Instruction) -> Vec<InstrKind> {
    match x.mnemonic() {
        Mnemonic::Je => vec![InstrKind::If(
            ExprKind::BinOp {
                kind: BinOpKind::Eq,
                lhs: Box::new(ExprKind::Flag(CpuFlag::Zero)),
                rhs: Box::new(ExprKind::CU8(1)),
            },
            Box::new(InstrKind::Jmp(lift_operand(0, x))),
        )],
        Mnemonic::Jne => vec![InstrKind::If(
            ExprKind::BinOp {
                kind: BinOpKind::Eq,
                lhs: Box::new(ExprKind::Flag(CpuFlag::Zero)),
                rhs: Box::new(ExprKind::CU8(0)),
            },
            Box::new(InstrKind::Jmp(lift_operand(0, x))),
        )],
        _ => todo!("{:?}", x),
    }
}

fn lift_imul(x: Instruction) -> Vec<InstrKind> {
    match x.op_count() {
        3 => {
            let expr = ExprKind::BinOp {
                kind: BinOpKind::Mul,
                lhs: Box::new(lift_operand(1, x)),
                rhs: Box::new(lift_operand(2, x)),
            };
            vec![
                InstrKind::AsgnFlagsFrom(
                    HashSet::from([CpuFlag::Carry, CpuFlag::Overflow]),
                    ExprKind::Not(Box::new(ExprKind::FitsByteSize(
                        x.op_register(0).size() as u8,
                        Box::new(expr.clone()),
                    ))),
                ),
                InstrKind::InvalidateFlags(HashSet::from([
                    CpuFlag::Sign,
                    CpuFlag::Zero,
                    CpuFlag::AuxCarry,
                    CpuFlag::Parity,
                ])),
                InstrKind::Asgn {
                    dest: lift_operand(0, x),
                    src: expr,
                },
            ]
        }
        _ => todo!("{:?} {:?}", x.op_count(), x),
    }
}

pub fn lift_lea(x: Instruction) -> Vec<InstrKind> {
    vec![InstrKind::Asgn {
        dest: lift_operand(0, x),
        src: lift_operand(1, x),
    }]
}

pub fn lift_ret(x: Instruction) -> Vec<InstrKind> {
    if x.op_count() != 0 {
        todo!()
    }
    vec![InstrKind::Ret { stack_bytes: None }]
}

pub fn lift(code: &[u8], base_address: usize) -> Program {
    let mut prog = Program::default();

    let mut decoder = Decoder::with_ip(64, code, base_address as u64, DecoderOptions::NONE);
    let mut instruction = Instruction::default();
    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);

        let mut lifted: Vec<InstrKind> = vec![];
        match instruction.mnemonic() {
            Mnemonic::Movzx => lifted.append(&mut lift_movzx(instruction)),
            Mnemonic::Movsx => lifted.append(&mut lift_movsx(instruction)),
            Mnemonic::Mov => lifted.append(&mut lift_mov(instruction)),
            Mnemonic::Xor => lifted.append(&mut lift_xor(instruction)),
            Mnemonic::Add => lifted.append(&mut lift_add(instruction)),
            Mnemonic::Test => lifted.append(&mut lift_cond(instruction)),
            Mnemonic::Je | Mnemonic::Jne => lifted.append(&mut lift_jmp(instruction)),
            Mnemonic::Imul => lifted.append(&mut lift_imul(instruction)),
            Mnemonic::Lea => lifted.append(&mut lift_lea(instruction)),
            Mnemonic::Ret => lifted.append(&mut lift_ret(instruction)),
            Mnemonic::Nop => (),
            _ => todo!("{:?} : {:?}", instruction.mnemonic(), instruction),
        }
        for l in lifted {
            println!("{:?}", l);
            prog.push(Instr {
                src_addr: instruction.ip() as usize,
                kind: l,
            });
        }
    }

    prog
}
