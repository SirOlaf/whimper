use std::collections::HashSet;

use iced_x86::{Code, Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};

#[derive(Debug, Clone)]
pub struct Program {
    pub entry_address: usize,
    pub instructions: Vec<(usize, IRInst)>,
}

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
    /// Low product bits at the operands' width (signedness-independent).
    Mul,

    Shl,
    /// Logical right shift.
    Shr,

    And,
    Or,

    Eq,
    SignedGt,
}

#[derive(Debug, Clone)]
pub enum IRExpr {
    BinOp {
        kind: IRBinOpKind,
        lhs: Box<IRExpr>,
        rhs: Box<IRExpr>,
    },

    Deref {
        address: Box<IRExpr>,
        size: usize,
    },
    ExtractBytes {
        value: Box<IRExpr>,
        offset: usize,
        size: usize,
    },
    ZeroExtend {
        value: Box<IRExpr>,
        size: usize,
    },
    SignExtend {
        value: Box<IRExpr>,
        size: usize,
    },

    // Native
    Reg(Register),
    Flag(NativeFlag),
    /// A byte range at a fixed offset from the entry stack pointer. Tier 2
    /// turns this into local values before source-like control flow is built.
    Stack {
        offset: i64,
        size: usize,
    },

    // Consts
    CU8(u8),
    CU32(u32),
    CU64(u64),
}

#[derive(Debug, Clone)]
pub enum IRInst {
    Asgn {
        dest: IRExpr,
        src: IRExpr,
    },

    If(IRExpr, Box<IRInst>),
    Jmp(IRExpr),
    Ret(Option<IRExpr>),

    SetFlagsFrom(HashSet<NativeFlag>, IRExpr),
    ClearFlags(HashSet<NativeFlag>),
    /// Architecturally undefined flags; reading one must remain unsupported.
    InvalidateFlags(HashSet<NativeFlag>),
}

fn bin_op(kind: IRBinOpKind, lhs: IRExpr, rhs: IRExpr) -> IRExpr {
    IRExpr::BinOp {
        kind,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

fn stack_address(address: &IRExpr) -> Option<i64> {
    match address {
        IRExpr::Reg(Register::RSP) => Some(0),
        IRExpr::BinOp {
            kind: IRBinOpKind::Add,
            lhs,
            rhs,
        } => {
            let IRExpr::Reg(Register::RSP) = lhs.as_ref() else {
                return None;
            };
            match rhs.as_ref() {
                IRExpr::CU64(value) => Some(*value as i64),
                IRExpr::CU32(value) => Some(*value as i32 as i64),
                _ => None,
            }
        }
        _ => None,
    }
}

fn resolve_stack_expr(expr: IRExpr, depth: i64) -> IRExpr {
    match expr {
        IRExpr::Deref { address, size } => {
            if let Some(displacement) = stack_address(&address) {
                IRExpr::Stack {
                    offset: displacement - depth,
                    size,
                }
            } else {
                IRExpr::Deref {
                    address: Box::new(resolve_stack_expr(*address, depth)),
                    size,
                }
            }
        }
        IRExpr::BinOp { kind, lhs, rhs } => bin_op(
            kind,
            resolve_stack_expr(*lhs, depth),
            resolve_stack_expr(*rhs, depth),
        ),
        IRExpr::ExtractBytes {
            value,
            offset,
            size,
        } => IRExpr::ExtractBytes {
            value: Box::new(resolve_stack_expr(*value, depth)),
            offset,
            size,
        },
        IRExpr::ZeroExtend { value, size } => IRExpr::ZeroExtend {
            value: Box::new(resolve_stack_expr(*value, depth)),
            size,
        },
        IRExpr::SignExtend { value, size } => IRExpr::SignExtend {
            value: Box::new(resolve_stack_expr(*value, depth)),
            size,
        },
        IRExpr::Reg(Register::RSP) => panic!("unresolved stack pointer use"),
        other => other,
    }
}

fn resolve_stack(instr: IRInst, depth: i64) -> IRInst {
    match instr {
        IRInst::Asgn { dest, src } => IRInst::Asgn {
            dest: resolve_stack_expr(dest, depth),
            src: resolve_stack_expr(src, depth),
        },
        IRInst::If(condition, inner) => IRInst::If(
            resolve_stack_expr(condition, depth),
            Box::new(resolve_stack(*inner, depth)),
        ),
        IRInst::Jmp(target) => IRInst::Jmp(resolve_stack_expr(target, depth)),
        IRInst::Ret(value) => IRInst::Ret(value.map(|value| resolve_stack_expr(value, depth))),
        IRInst::SetFlagsFrom(flags, expr) => {
            IRInst::SetFlagsFrom(flags, resolve_stack_expr(expr, depth))
        }
        other => other,
    }
}

/// Address arithmetic is independent of the memory operand's access width.
fn effective_address(x: Instruction, truncate32: bool) -> IRExpr {
    assert!(x.vsib().is_none(), "unsupported vector address: {x:?}");
    assert!(
        !matches!(x.segment_prefix(), Register::FS | Register::GS),
        "unsupported segment base: {x:?}"
    );
    if x.is_ip_rel_memory_operand() {
        return if truncate32 {
            IRExpr::CU32(x.ip_rel_memory_address() as u32)
        } else {
            IRExpr::CU64(x.ip_rel_memory_address())
        };
    }
    let base = if truncate32 {
        x.memory_base().full_register32()
    } else {
        x.memory_base()
    };
    let index = if truncate32 {
        x.memory_index().full_register32()
    } else {
        x.memory_index()
    };
    let address32 = truncate32 || base.is_gpr32() || index.is_gpr32();
    let constant = |value| {
        if address32 {
            IRExpr::CU32(value as u32)
        } else {
            IRExpr::CU64(value)
        }
    };
    let mut address = constant(x.memory_displacement64());
    if base != Register::None {
        address = bin_op(IRBinOpKind::Add, IRExpr::Reg(base), address);
    }
    if index != Register::None {
        let mut scaled = IRExpr::Reg(index);
        if x.memory_index_scale() != 1 {
            scaled = bin_op(
                IRBinOpKind::Mul,
                scaled,
                constant(x.memory_index_scale() as u64),
            );
        }
        address = bin_op(IRBinOpKind::Add, address, scaled);
    }
    if address32 && !truncate32 {
        IRExpr::ZeroExtend {
            value: Box::new(IRExpr::ExtractBytes {
                value: Box::new(address),
                offset: 0,
                size: 4,
            }),
            size: 8,
        }
    } else {
        address
    }
}

fn lift_op(x: Instruction, i: u32) -> IRExpr {
    match x.op_kind(i) {
        OpKind::Memory => {
            let size = x.memory_size().size();
            assert!(
                matches!(size, 1 | 2 | 4 | 8),
                "unsupported memory width: {x:?}"
            );
            IRExpr::Deref {
                address: Box::new(effective_address(x, false)),
                size,
            }
        }
        OpKind::Register => IRExpr::Reg(x.op_register(i)),
        OpKind::NearBranch64 => IRExpr::CU64(x.near_branch_target()),
        OpKind::Immediate8 => IRExpr::CU8(x.immediate8()),
        OpKind::Immediate16 => IRExpr::CU32(x.immediate16() as u32),
        OpKind::Immediate32 => IRExpr::CU32(x.immediate32()),
        OpKind::Immediate64 => IRExpr::CU64(x.immediate64()),
        OpKind::Immediate8to32 => IRExpr::CU32(x.immediate8to32() as u32),
        OpKind::Immediate8to16 => IRExpr::CU32(x.immediate8to16() as u16 as u32),
        OpKind::Immediate8to64 => IRExpr::CU64(x.immediate8to64() as u64),
        OpKind::Immediate32to64 => IRExpr::CU64(x.immediate32to64() as u64),
        _ => {
            panic!("Unimplemented address kind: {:?}", x.op_kind(i));
        }
    }
}

fn lift_extend(x: Instruction) -> Vec<IRInst> {
    // These are value conversions, not native operations in the next tier.
    assert!(
        matches!(
            x.code(),
            Code::Movzx_r32_rm8
                | Code::Movzx_r32_rm16
                | Code::Movzx_r64_rm8
                | Code::Movzx_r64_rm16
                | Code::Movsx_r32_rm8
                | Code::Movsx_r32_rm16
                | Code::Movsx_r64_rm8
                | Code::Movsx_r64_rm16
        ),
        "unsupported extension: {x:?}"
    );
    let value = Box::new(lift_op(x, 1));
    let size = x.op0_register().size();
    let src = if x.mnemonic() == Mnemonic::Movzx {
        IRExpr::ZeroExtend { value, size }
    } else {
        IRExpr::SignExtend { value, size }
    };
    vec![IRInst::Asgn {
        dest: lift_op(x, 0),
        src,
    }]
}

fn lift_lea(x: Instruction) -> Vec<IRInst> {
    assert!(
        matches!(x.code(), Code::Lea_r32_m | Code::Lea_r64_m),
        "unsupported LEA: {x:?}"
    );
    // Only the low 32 bits contribute to a 32-bit destination. Do the
    // arithmetic at that width instead of carrying high address bits onward.
    let src = effective_address(x, x.op0_register().size() == 4);
    vec![IRInst::Asgn {
        dest: lift_op(x, 0),
        src,
    }]
}

fn lift_imul(x: Instruction) -> Vec<IRInst> {
    assert!(
        matches!(
            x.code(),
            Code::Imul_r32_rm32_imm32 | Code::Imul_r32_rm32_imm8
        ),
        "unsupported IMUL: {x:?}"
    );
    // The two signed 32-bit operands have an exact signed 64-bit product.
    // CF/OF test whether truncation to 32 bits loses signed information.
    let product = bin_op(
        IRBinOpKind::Mul,
        IRExpr::SignExtend {
            value: Box::new(lift_op(x, 1)),
            size: 8,
        },
        IRExpr::SignExtend {
            value: Box::new(lift_op(x, 2)),
            size: 8,
        },
    );
    let low = IRExpr::ExtractBytes {
        value: Box::new(product.clone()),
        offset: 0,
        size: 4,
    };
    let overflow = bin_op(
        IRBinOpKind::Eq,
        bin_op(
            IRBinOpKind::Eq,
            product,
            IRExpr::SignExtend {
                value: Box::new(low),
                size: 8,
            },
        ),
        IRExpr::CU8(0),
    );
    vec![
        IRInst::Asgn {
            dest: IRExpr::Flag(NativeFlag::Carry),
            src: overflow.clone(),
        },
        IRInst::Asgn {
            dest: IRExpr::Flag(NativeFlag::Overflow),
            src: overflow,
        },
        IRInst::InvalidateFlags(HashSet::from([
            NativeFlag::Zero,
            NativeFlag::Sign,
            NativeFlag::Parity,
            NativeFlag::AuxCarry,
        ])),
        IRInst::Asgn {
            dest: lift_op(x, 0),
            src: bin_op(IRBinOpKind::Mul, lift_op(x, 1), lift_op(x, 2)),
        },
    ]
}

fn lift_mov(x: Instruction) -> Vec<IRInst> {
    for index in 0..x.op_count() {
        match x.op_kind(index) {
            OpKind::Register => assert!(
                x.op_register(index).is_gpr(),
                "unsupported MOV register: {x:?}"
            ),
            OpKind::Memory => assert!(
                matches!(x.memory_size().size(), 1 | 2 | 4 | 8),
                "unsupported MOV width: {x:?}"
            ),
            OpKind::Immediate8
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate64
            | OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate32to64 => {}
            _ => panic!("unsupported MOV operand: {x:?}"),
        }
    }
    vec![IRInst::Asgn {
        dest: lift_op(x, 0),
        src: lift_op(x, 1),
    }]
}

fn lift_arithmetic(x: Instruction, kind: IRBinOpKind) -> Vec<IRInst> {
    let operand = lift_op(x, 0);
    let rhs = if matches!(x.mnemonic(), Mnemonic::Inc | Mnemonic::Dec) {
        IRExpr::CU8(1)
    } else {
        lift_op(x, 1)
    };
    let result = bin_op(kind, operand.clone(), rhs);
    let mut flags = HashSet::from([
        NativeFlag::AuxCarry,
        NativeFlag::Overflow,
        NativeFlag::Parity,
        NativeFlag::Sign,
        NativeFlag::Zero,
    ]);
    if !matches!(x.mnemonic(), Mnemonic::Inc | Mnemonic::Dec) {
        flags.insert(NativeFlag::Carry);
    }
    vec![
        IRInst::SetFlagsFrom(flags, result.clone()),
        IRInst::Asgn {
            dest: operand,
            src: result,
        },
    ]
}

fn lift_movsxd(x: Instruction) -> Vec<IRInst> {
    vec![IRInst::Asgn {
        dest: lift_op(x, 0),
        src: IRExpr::SignExtend {
            value: Box::new(lift_op(x, 1)),
            size: 8,
        },
    }]
}

fn lift_cond(x: Instruction) -> Vec<IRInst> {
    match x.mnemonic() {
        Mnemonic::Test => {
            let mut res = vec![
                IRInst::ClearFlags(HashSet::from([NativeFlag::Carry, NativeFlag::Overflow])),
                IRInst::InvalidateFlags(HashSet::from([NativeFlag::AuxCarry])),
            ];
            match x.code() {
                Code::Test_rm8_r8 | Code::Test_rm32_r32 | Code::Test_rm64_r64 => {
                    let and_expr = IRExpr::BinOp {
                        kind: IRBinOpKind::And,
                        lhs: Box::new(lift_op(x, 0)),
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
        Mnemonic::Cmp => {
            let sub_expr = IRExpr::BinOp {
                kind: IRBinOpKind::Sub,
                lhs: Box::new(lift_op(x, 0)),
                rhs: Box::new(lift_op(x, 1)),
            };
            vec![IRInst::SetFlagsFrom(
                HashSet::from([
                    NativeFlag::Overflow,
                    NativeFlag::Sign,
                    NativeFlag::Zero,
                    NativeFlag::AuxCarry,
                    NativeFlag::Parity,
                    NativeFlag::Carry,
                ]),
                sub_expr,
            )]
        }
        _ => {
            panic!("Unlifted cond: {:?}", x)
        }
    }
}

fn lift_jmp(x: Instruction, signed_compare: Option<(IRExpr, IRExpr)>) -> Vec<IRInst> {
    match x.code() {
        Code::Jg_rel8_64
        | Code::Jg_rel32_64
        | Code::Jl_rel8_64
        | Code::Jl_rel32_64
        | Code::Jge_rel8_64
        | Code::Jge_rel32_64
        | Code::Jle_rel8_64
        | Code::Jle_rel32_64 => {
            let (lhs, rhs) = signed_compare.expect("signed jump must follow a supported compare");
            let (lhs, rhs) = if matches!(x.mnemonic(), Mnemonic::Jl | Mnemonic::Jge) {
                (rhs, lhs)
            } else {
                (lhs, rhs)
            };
            let gt = bin_op(IRBinOpKind::SignedGt, lhs, rhs);
            let condition = if matches!(x.mnemonic(), Mnemonic::Jge | Mnemonic::Jle) {
                bin_op(IRBinOpKind::Eq, gt, IRExpr::CU8(0))
            } else {
                gt
            };
            vec![IRInst::If(condition, Box::new(IRInst::Jmp(lift_op(x, 0))))]
        }
        Code::Je_rel8_64 | Code::Je_rel32_64 | Code::Jne_rel8_64 | Code::Jne_rel32_64 => {
            vec![IRInst::If(
                IRExpr::BinOp {
                    kind: IRBinOpKind::Eq,
                    lhs: Box::new(IRExpr::Flag(NativeFlag::Zero)),
                    rhs: Box::new(IRExpr::CU8(u8::from(x.mnemonic() == Mnemonic::Je))),
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
        Code::Jbe_rel8_64 => {
            vec![IRInst::If(
                IRExpr::BinOp {
                    kind: IRBinOpKind::Or,
                    lhs: Box::new(IRExpr::Flag(NativeFlag::Carry)),
                    rhs: Box::new(IRExpr::Flag(NativeFlag::Zero)),
                },
                Box::new(IRInst::Jmp(lift_op(x, 0))),
            )]
        }
        _ => panic!("{:?}", x),
    }
}

fn lift_shift(x: Instruction, kind: IRBinOpKind) -> Vec<IRInst> {
    let count = lift_op(x, 1);
    let count = if matches!(count, IRExpr::Reg(Register::CL)) {
        let width = if x.op_kind(0) == OpKind::Register {
            x.op0_register().size()
        } else {
            x.memory_size().size()
        };
        bin_op(
            IRBinOpKind::And,
            count,
            IRExpr::CU8(if width == 8 { 63 } else { 31 }),
        )
    } else {
        count
    };
    let expr = bin_op(kind, lift_op(x, 0), count);
    vec![
        IRInst::SetFlagsFrom(
            HashSet::from([
                NativeFlag::Sign,
                NativeFlag::Zero,
                NativeFlag::AuxCarry,
                NativeFlag::Parity,
                NativeFlag::Carry,
                NativeFlag::Overflow,
            ]),
            expr.clone(),
        ),
        IRInst::Asgn {
            dest: lift_op(x, 0),
            src: expr,
        },
    ]
}

fn lift_xor(x: Instruction) -> Vec<IRInst> {
    let same_register = x.op_kind(0) == OpKind::Register
        && x.op_kind(1) == OpKind::Register
        && x.op_register(0) == x.op_register(1);
    if !same_register || !matches!(x.code(), Code::Xor_r32_rm32 | Code::Xor_rm32_r32) {
        panic!("unsupported XOR: {x:?}");
    }

    vec![
        IRInst::ClearFlags(HashSet::from([NativeFlag::Carry, NativeFlag::Overflow])),
        IRInst::InvalidateFlags(HashSet::from([NativeFlag::AuxCarry])),
        IRInst::SetFlagsFrom(
            HashSet::from([NativeFlag::Sign, NativeFlag::Zero, NativeFlag::Parity]),
            IRExpr::CU32(0),
        ),
        IRInst::Asgn {
            dest: lift_op(x, 0),
            src: IRExpr::CU32(0),
        },
    ]
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

    let mut program = Program {
        entry_address: base_offset,
        instructions: Vec::new(),
    };
    let mut last_compare = None;
    let mut stack_depth = 0i64;
    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);

        let compare_for_jump = if matches!(
            instruction.mnemonic(),
            Mnemonic::Jg | Mnemonic::Jl | Mnemonic::Jge | Mnemonic::Jle
        ) {
            last_compare.clone()
        } else {
            None
        };
        let tmp_instr = match instruction.mnemonic() {
            Mnemonic::Mov => Some(lift_mov(instruction)),
            Mnemonic::Movsxd => Some(lift_movsxd(instruction)),
            Mnemonic::Movzx | Mnemonic::Movsx => Some(lift_extend(instruction)),
            Mnemonic::Lea => Some(lift_lea(instruction)),
            Mnemonic::Imul => Some(lift_imul(instruction)),
            Mnemonic::Add | Mnemonic::Inc => Some(lift_arithmetic(instruction, IRBinOpKind::Add)),
            Mnemonic::Sub | Mnemonic::Dec => Some(lift_arithmetic(instruction, IRBinOpKind::Sub)),
            Mnemonic::Push => {
                assert_eq!(
                    instruction.op_kind(0),
                    OpKind::Register,
                    "unsupported push: {instruction:?}"
                );
                assert!(
                    instruction.op0_register().is_gpr64(),
                    "unsupported push width: {instruction:?}"
                );
                stack_depth += 8;
                Some(vec![IRInst::Asgn {
                    dest: IRExpr::Stack {
                        offset: -stack_depth,
                        size: 8,
                    },
                    src: lift_op(instruction, 0),
                }])
            }
            Mnemonic::Pop => {
                assert_eq!(
                    instruction.op_kind(0),
                    OpKind::Register,
                    "unsupported pop: {instruction:?}"
                );
                assert!(
                    instruction.op0_register().is_gpr64(),
                    "unsupported pop width: {instruction:?}"
                );
                let popped = IRInst::Asgn {
                    dest: lift_op(instruction, 0),
                    src: IRExpr::Stack {
                        offset: -stack_depth,
                        size: 8,
                    },
                };
                stack_depth -= 8;
                Some(vec![popped])
            }
            Mnemonic::Cmovne => Some(vec![IRInst::If(
                bin_op(
                    IRBinOpKind::Eq,
                    IRExpr::Flag(NativeFlag::Zero),
                    IRExpr::CU8(0),
                ),
                Box::new(IRInst::Asgn {
                    dest: lift_op(instruction, 0),
                    src: lift_op(instruction, 1),
                }),
            )]),
            Mnemonic::Test | Mnemonic::Cmp => Some(lift_cond(instruction)),
            Mnemonic::Je
            | Mnemonic::Jne
            | Mnemonic::Jb
            | Mnemonic::Jae
            | Mnemonic::Jbe
            | Mnemonic::Jg
            | Mnemonic::Jl
            | Mnemonic::Jge
            | Mnemonic::Jle => Some(lift_jmp(instruction, compare_for_jump)),
            Mnemonic::Jmp => Some(vec![IRInst::Jmp(lift_op(instruction, 0))]),
            Mnemonic::Shl => Some(lift_shift(instruction, IRBinOpKind::Shl)),
            Mnemonic::Shr => Some(lift_shift(instruction, IRBinOpKind::Shr)),
            Mnemonic::Xor => Some(lift_xor(instruction)),
            Mnemonic::Ret => Some(lift_ret(instruction)),
            Mnemonic::Nop => None,
            _ => {
                println!("{:?}", instruction);
                panic!("Unlifted instruction: {:?}", instruction.mnemonic())
            }
        };
        if let Some(instrs) = tmp_instr {
            program.instructions.extend(instrs.iter().map(|x| {
                (
                    instruction.ip().try_into().unwrap(),
                    resolve_stack(x.clone(), stack_depth),
                )
            }));
        }

        last_compare = (instruction.mnemonic() == Mnemonic::Cmp)
            .then(|| (lift_op(instruction, 0), lift_op(instruction, 1)));
    }

    assert_eq!(stack_depth, 0, "unbalanced native stack frame");

    program
}
