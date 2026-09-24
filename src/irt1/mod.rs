pub mod ir;
pub mod prune_flags;
pub mod register_parameters;
pub mod render;
mod return_registers;

use std::collections::{HashMap, HashSet};

use iced_x86::Register;

use crate::irt0::ir::{
    IRBinOpKind as IRT0BinOpKind, IRExpr as IRT0Expr, IRInst as IRT0Inst, NativeFlag as IRT0Flag,
    Program as IRT0Program,
};

use self::ir::{
    IRBinOpKind, IRExpr, IRInst, NativeFlag, Program, SyntheticFunction, SyntheticFunctionId,
    VariableId, VariableType,
};

fn lift_flag(flag: IRT0Flag) -> NativeFlag {
    match flag {
        IRT0Flag::Carry => NativeFlag::Carry,
        IRT0Flag::Parity => NativeFlag::Parity,
        IRT0Flag::AuxCarry => NativeFlag::AuxCarry,
        IRT0Flag::Zero => NativeFlag::Zero,
        IRT0Flag::Sign => NativeFlag::Sign,
        IRT0Flag::Trap => NativeFlag::Trap,
        IRT0Flag::InterruptEnable => NativeFlag::InterruptEnable,
        IRT0Flag::Direction => NativeFlag::Direction,
        IRT0Flag::Overflow => NativeFlag::Overflow,
    }
}

fn lift_expr(expr: IRT0Expr) -> IRExpr {
    match expr {
        IRT0Expr::BinOp { kind, lhs, rhs } => IRExpr::BinOp {
            kind: match kind {
                IRT0BinOpKind::Add => IRBinOpKind::Add,
                IRT0BinOpKind::Sub => IRBinOpKind::Sub,
                IRT0BinOpKind::Mul => IRBinOpKind::Mul,
                IRT0BinOpKind::Shl => IRBinOpKind::Shl,
                IRT0BinOpKind::Shr => IRBinOpKind::Shr,
                IRT0BinOpKind::And => IRBinOpKind::And,
                IRT0BinOpKind::Or => IRBinOpKind::Or,
                IRT0BinOpKind::Eq => IRBinOpKind::Eq,
                IRT0BinOpKind::SignedGt => IRBinOpKind::SignedGt,
            },
            lhs: Box::new(lift_expr(*lhs)),
            rhs: Box::new(lift_expr(*rhs)),
        },
        IRT0Expr::Deref { address, size } => IRExpr::Deref {
            address: Box::new(lift_expr(*address)),
            size,
        },
        IRT0Expr::ExtractBytes {
            value,
            offset,
            size,
        } => IRExpr::ExtractBytes {
            value: Box::new(lift_expr(*value)),
            offset,
            size,
        },
        IRT0Expr::ZeroExtend { value, size } => IRExpr::ZeroExtend {
            value: Box::new(lift_expr(*value)),
            size,
        },
        IRT0Expr::SignExtend { value, size } => IRExpr::SignExtend {
            value: Box::new(lift_expr(*value)),
            size,
        },
        IRT0Expr::Reg(reg) => IRExpr::Reg(reg),
        IRT0Expr::Stack { offset, size } => IRExpr::Stack { offset, size },
        IRT0Expr::Flag(flag) => IRExpr::Flag(lift_flag(flag)),
        IRT0Expr::CU8(value) => IRExpr::CU8(value),
        IRT0Expr::CU32(value) => IRExpr::CU32(value),
        IRT0Expr::CU64(value) => IRExpr::CU64(value),
    }
}

fn jump_target(expr: &IRT0Expr, offset: usize) -> Option<usize> {
    match expr {
        IRT0Expr::CU64(value) => usize::try_from(*value).ok(),
        IRT0Expr::CU32(value) => usize::try_from(*value).ok(),
        IRT0Expr::Reg(Register::RIP) => Some(offset),
        IRT0Expr::BinOp {
            kind: IRT0BinOpKind::Add,
            lhs,
            rhs,
        } => jump_target(lhs, offset)?.checked_add(jump_target(rhs, offset)?),
        _ => None,
    }
}

fn stack_references(expr: &IRT0Expr, offsets: &mut Vec<i64>) {
    match expr {
        IRT0Expr::Stack { offset, .. } => offsets.push(*offset),
        IRT0Expr::BinOp { lhs, rhs, .. } => {
            stack_references(lhs, offsets);
            stack_references(rhs, offsets);
        }
        IRT0Expr::Deref { address, .. }
        | IRT0Expr::ExtractBytes { value: address, .. }
        | IRT0Expr::ZeroExtend { value: address, .. }
        | IRT0Expr::SignExtend { value: address, .. } => stack_references(address, offsets),
        _ => {}
    }
}

fn instruction_stack_references(instr: &IRT0Inst, offsets: &mut Vec<i64>) {
    match instr {
        IRT0Inst::Asgn { dest, src } => {
            stack_references(dest, offsets);
            stack_references(src, offsets);
        }
        IRT0Inst::If(condition, inner) => {
            stack_references(condition, offsets);
            instruction_stack_references(inner, offsets);
        }
        IRT0Inst::Jmp(value) | IRT0Inst::Ret(Some(value)) | IRT0Inst::SetFlagsFrom(_, value) => {
            stack_references(value, offsets)
        }
        _ => {}
    }
}

fn expression_reads_register(expr: &IRT0Expr, register: Register) -> bool {
    match expr {
        IRT0Expr::Reg(found) => found.full_register() == register,
        IRT0Expr::BinOp { lhs, rhs, .. } => {
            expression_reads_register(lhs, register) || expression_reads_register(rhs, register)
        }
        IRT0Expr::Deref { address, .. }
        | IRT0Expr::ExtractBytes { value: address, .. }
        | IRT0Expr::ZeroExtend { value: address, .. }
        | IRT0Expr::SignExtend { value: address, .. } => {
            expression_reads_register(address, register)
        }
        _ => false,
    }
}

fn instruction_reads_register(instr: &IRT0Inst, register: Register) -> bool {
    match instr {
        IRT0Inst::Asgn { dest, src } => {
            expression_reads_register(src, register)
                || !matches!(dest, IRT0Expr::Reg(_)) && expression_reads_register(dest, register)
        }
        IRT0Inst::If(condition, inner) => {
            expression_reads_register(condition, register)
                || instruction_reads_register(inner, register)
        }
        IRT0Inst::Jmp(value) | IRT0Inst::Ret(Some(value)) | IRT0Inst::SetFlagsFrom(_, value) => {
            expression_reads_register(value, register)
        }
        _ => false,
    }
}

/// Callee-saved register spills are ABI bookkeeping. Keep their exact native
/// effects in Tier 0, but remove a matched spill/reload when the slot has no
/// other use before building source-like state in this tier.
fn strip_frame_saves(source: &[(usize, IRT0Inst)]) -> Vec<(usize, IRT0Inst)> {
    let mut references: HashMap<i64, Vec<usize>> = HashMap::new();
    for (index, (_, instr)) in source.iter().enumerate() {
        let mut offsets = Vec::new();
        instruction_stack_references(instr, &mut offsets);
        for offset in offsets {
            references.entry(offset).or_default().push(index);
        }
    }
    let mut remove = HashSet::new();
    for (&offset, indices) in &references {
        let [save, restore] = indices.as_slice() else {
            continue;
        };
        let IRT0Inst::Asgn {
            dest:
                IRT0Expr::Stack {
                    offset: saved,
                    size: 8,
                },
            src: IRT0Expr::Reg(register),
        } = &source[*save].1
        else {
            continue;
        };
        let IRT0Inst::Asgn {
            dest: IRT0Expr::Reg(restored),
            src:
                IRT0Expr::Stack {
                    offset: loaded,
                    size: 8,
                },
        } = &source[*restore].1
        else {
            continue;
        };
        let nonvolatile = matches!(
            register.full_register(),
            Register::RBX
                | Register::RBP
                | Register::RSI
                | Register::RDI
                | Register::R12
                | Register::R13
                | Register::R14
                | Register::R15
        );
        let mut terminal = false;
        let mut used_after_restore = false;
        for (_, instr) in source.iter().skip(restore + 1) {
            if matches!(instr, IRT0Inst::Ret(_)) {
                terminal = true;
                break;
            }
            if matches!(instr, IRT0Inst::If(..) | IRT0Inst::Jmp(_))
                || instruction_reads_register(instr, register.full_register())
            {
                used_after_restore = true;
                break;
            }
        }
        if saved == &offset
            && loaded == &offset
            && register == restored
            && save < restore
            && nonvolatile
            && terminal
            && !used_after_restore
        {
            remove.insert(*save);
            remove.insert(*restore);
        }
    }
    source
        .iter()
        .enumerate()
        .filter_map(|(index, item)| (!remove.contains(&index)).then_some(item.clone()))
        .collect()
}

struct SyntheticFunctionBuilder<'a> {
    source: &'a [(usize, IRT0Inst)],
    entry_address: usize,
    jump_entries: HashSet<usize>,
    by_start: HashMap<usize, SyntheticFunctionId>,
    functions: Vec<SyntheticFunction>,
}

impl SyntheticFunctionBuilder<'_> {
    // The tier 0 program has one or more operations per source address. A jump
    // into an omitted NOP starts at the first surviving operation after it.
    fn index_at(&self, offset: usize) -> Option<usize> {
        let index = self
            .source
            .partition_point(|(address, _)| *address < offset);
        (index < self.source.len()).then_some(index)
    }

    fn local_target(&self, expr: &IRT0Expr, offset: usize) -> Option<usize> {
        let target = jump_target(expr, offset)?;
        if target < self.source.first()?.0 || target > self.source.last()?.0 {
            return None;
        }
        self.index_at(target)
    }

    fn target(&mut self, expr: &IRT0Expr, offset: usize) -> IRInst {
        match self.local_target(expr, offset) {
            Some(index) => IRInst::CallSynthetic {
                function: self.function(index),
                arguments: Vec::new(),
            },
            None => IRInst::Jump(lift_expr(expr.clone())),
        }
    }

    fn fallthrough(&mut self, index: usize) -> IRInst {
        if index < self.source.len() {
            IRInst::CallSynthetic {
                function: self.function(index),
                arguments: Vec::new(),
            }
        } else {
            IRInst::End
        }
    }

    fn function(&mut self, start: usize) -> SyntheticFunctionId {
        if let Some(reference) = self.by_start.get(&start) {
            return *reference;
        }

        // Reserve the function before following its edges. A backward jump
        // can then call a function that is still being constructed.
        let reference = SyntheticFunctionId {
            id: self.functions.len(),
        };
        self.by_start.insert(start, reference);
        self.functions.push(SyntheticFunction {
            entry_offset: if start == 0 {
                self.entry_address
            } else {
                self.source[start].0
            },
            parameters: Vec::new(),
            external_flags: HashSet::new(),
            body: Vec::new(),
        });

        let mut body: Vec<(usize, IRInst)> = Vec::new();
        let mut index = start;
        while index < self.source.len() {
            let (offset, instr) = &self.source[index];
            let offset = *offset;
            let instr = instr.clone();

            // Split before any shared entry. Without this boundary, the same
            // source instructions would also be copied into the predecessor.
            if index != start
                && (self.jump_entries.contains(&index) || self.by_start.contains_key(&index))
            {
                let previous_offset = body.last().unwrap().0;
                body.push((previous_offset, self.fallthrough(index)));
                break;
            }

            match instr {
                IRT0Inst::If(condition, inner) => {
                    let then_branch = match inner.as_ref() {
                        IRT0Inst::Jmp(target) => self.target(target, offset),
                        IRT0Inst::Asgn { dest, src } => {
                            // A conditional move is a local assignment followed by
                            // the same continuation as the unchanged arm.
                            let continuation = self.fallthrough(index + 1);
                            let id = SyntheticFunctionId {
                                id: self.functions.len(),
                            };
                            self.functions.push(SyntheticFunction {
                                entry_offset: offset,
                                parameters: Vec::new(),
                                external_flags: HashSet::new(),
                                body: vec![
                                    (
                                        offset,
                                        IRInst::Assign {
                                            dest: lift_expr(dest.clone()),
                                            src: lift_expr(src.clone()),
                                        },
                                    ),
                                    (offset, continuation),
                                ],
                            });
                            IRInst::CallSynthetic {
                                function: id,
                                arguments: Vec::new(),
                            }
                        }
                        _ => panic!("unsupported conditional tier 0 instruction"),
                    };
                    let else_branch = self.fallthrough(index + 1);
                    body.push((
                        offset,
                        IRInst::If {
                            condition: lift_expr(condition),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        },
                    ));
                    break;
                }
                IRT0Inst::Jmp(target) => {
                    let target = self.target(&target, offset);
                    body.push((offset, target));
                    break;
                }
                IRT0Inst::Ret(value) => {
                    body.push((offset, IRInst::Return(value.map(lift_expr))));
                    break;
                }
                IRT0Inst::Asgn { dest, src } => body.push((
                    offset,
                    IRInst::Assign {
                        dest: lift_expr(dest),
                        src: lift_expr(src),
                    },
                )),
                IRT0Inst::SetFlagsFrom(flags, expr) => body.push((
                    offset,
                    IRInst::SetFlagsFrom {
                        flags: flags.into_iter().map(lift_flag).collect(),
                        expr: lift_expr(expr),
                    },
                )),
                IRT0Inst::ClearFlags(flags) => {
                    body.push((
                        offset,
                        IRInst::ClearFlags {
                            flags: flags.into_iter().map(lift_flag).collect(),
                        },
                    ));
                }
                IRT0Inst::InvalidateFlags(flags) => body.push((
                    offset,
                    IRInst::InvalidateFlags {
                        flags: flags.into_iter().map(lift_flag).collect(),
                    },
                )),
            }
            index += 1;
        }

        self.functions[reference.id].body = body;
        reference
    }
}

fn condition_flags(expr: &IRExpr, flags: &mut Vec<NativeFlag>) {
    match expr {
        IRExpr::Flag(flag) if !flags.contains(flag) => flags.push(flag.clone()),
        IRExpr::BinOp { lhs, rhs, .. } => {
            condition_flags(lhs, flags);
            condition_flags(rhs, flags);
        }
        IRExpr::Deref { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::SignExtend { value: inner, .. }
        | IRExpr::Not(inner) => condition_flags(inner, flags),
        IRExpr::Stack { .. } => {}
        _ => {}
    }
}

fn flag_test(flag: &NativeFlag, expected: u8, slots: &HashMap<NativeFlag, VariableId>) -> IRExpr {
    let slot = IRExpr::Variable(slots[flag]);
    match expected {
        1 => slot,
        0 => IRExpr::Not(Box::new(slot)),
        _ => panic!("a flag can only be compared with 0 or 1"),
    }
}

fn lift_condition(expr: IRExpr, slots: &HashMap<NativeFlag, VariableId>) -> IRExpr {
    match expr {
        IRExpr::Flag(flag) => IRExpr::Variable(slots[&flag]),
        IRExpr::BinOp {
            kind: IRBinOpKind::Eq,
            lhs,
            rhs,
        } => match (*lhs, *rhs) {
            (IRExpr::Flag(flag), IRExpr::CU8(value)) | (IRExpr::CU8(value), IRExpr::Flag(flag)) => {
                flag_test(&flag, value, slots)
            }
            (lhs, rhs) => IRExpr::BinOp {
                kind: IRBinOpKind::Eq,
                lhs: Box::new(lift_condition(lhs, slots)),
                rhs: Box::new(lift_condition(rhs, slots)),
            },
        },
        IRExpr::BinOp {
            kind: IRBinOpKind::Or,
            lhs,
            rhs,
        } => IRExpr::BinOp {
            kind: IRBinOpKind::Or,
            lhs: Box::new(lift_condition(*lhs, slots)),
            rhs: Box::new(lift_condition(*rhs, slots)),
        },
        expr => {
            let mut flags = Vec::new();
            condition_flags(&expr, &mut flags);
            assert!(flags.is_empty(), "unsupported flag condition: {expr:?}");
            expr
        }
    }
}

fn flag_value(flag: &NativeFlag, expr: &IRExpr) -> IRExpr {
    match (flag, expr) {
        (NativeFlag::Zero, _) => IRExpr::BinOp {
            kind: IRBinOpKind::Eq,
            lhs: Box::new(expr.clone()),
            rhs: Box::new(IRExpr::CU8(0)),
        },
        (
            NativeFlag::Carry,
            IRExpr::BinOp {
                kind: IRBinOpKind::Sub,
                lhs,
                rhs,
            },
        ) => IRExpr::BinOp {
            kind: IRBinOpKind::UnsignedLt,
            lhs: Box::new((**lhs).clone()),
            rhs: Box::new((**rhs).clone()),
        },
        (
            NativeFlag::Carry,
            IRExpr::BinOp {
                kind: IRBinOpKind::Add,
                lhs,
                ..
            },
        ) => IRExpr::BinOp {
            kind: IRBinOpKind::UnsignedLt,
            lhs: Box::new(expr.clone()),
            rhs: Box::new((**lhs).clone()),
        },
        _ => unimplemented!("cannot express {flag:?} from {expr:?} as a boolean expression"),
    }
}

fn lift_conditions(
    function: SyntheticFunctionId,
    body: Vec<(usize, IRInst)>,
) -> Vec<(usize, IRInst)> {
    let mut flags = Vec::new();
    for (_, instr) in &body {
        if let IRInst::If { condition, .. } = instr {
            condition_flags(condition, &mut flags);
        }
    }
    if flags.is_empty() {
        return body;
    }

    let mut slots = HashMap::new();
    let mut writes: HashMap<usize, Vec<(NativeFlag, VariableId)>> = HashMap::new();
    for flag in flags {
        // The branch is terminal, so the last write in this body is its source.
        let Some(index) = body.iter().rposition(|(_, instr)| match instr {
            IRInst::SetFlagsFrom { flags, .. }
            | IRInst::ClearFlags { flags }
            | IRInst::InvalidateFlags { flags } => flags.contains(&flag),
            IRInst::Assign {
                dest: IRExpr::Flag(written),
                ..
            } => written == &flag,
            _ => false,
        }) else {
            unimplemented!(
                "synthetic function {} reads {flag:?} from another function; parameters are needed",
                function.id
            );
        };
        let variable = VariableId {
            owner: function,
            id: slots.len(),
        };
        slots.insert(flag.clone(), variable);
        writes.entry(index).or_default().push((flag, variable));
    }

    let entry_offset = body[0].0;
    let mut lifted = Vec::new();
    let mut variables: Vec<_> = slots.values().copied().collect();
    variables.sort_by_key(|variable| variable.id);
    for variable in variables {
        lifted.push((
            entry_offset,
            IRInst::DeclareVariable {
                variable,
                ty: VariableType::Bool,
            },
        ));
    }

    for (index, (offset, instr)) in body.into_iter().enumerate() {
        match instr {
            IRInst::Assign {
                dest: IRExpr::Flag(flag),
                src,
            } => {
                if let Some(assignments) = writes.get(&index) {
                    for (_, variable) in assignments {
                        lifted.push((
                            offset,
                            IRInst::AssignVariable {
                                variable: *variable,
                                value: src.clone(),
                            },
                        ));
                    }
                }
                lifted.push((
                    offset,
                    IRInst::Assign {
                        dest: IRExpr::Flag(flag),
                        src,
                    },
                ));
            }
            IRInst::InvalidateFlags { flags } => {
                assert!(
                    !writes.contains_key(&index),
                    "undefined flags {flags:?} used at 0x{offset:x}"
                );
                lifted.push((offset, IRInst::InvalidateFlags { flags }));
            }
            IRInst::SetFlagsFrom { flags, expr } => {
                if let Some(assignments) = writes.get(&index) {
                    for (flag, variable) in assignments {
                        lifted.push((
                            offset,
                            IRInst::AssignVariable {
                                variable: *variable,
                                value: flag_value(flag, &expr),
                            },
                        ));
                    }
                }
                lifted.push((offset, IRInst::SetFlagsFrom { flags, expr }));
            }
            IRInst::ClearFlags { flags } => {
                if let Some(assignments) = writes.get(&index) {
                    for (_, variable) in assignments {
                        lifted.push((
                            offset,
                            IRInst::AssignVariable {
                                variable: *variable,
                                value: IRExpr::Bool(false),
                            },
                        ));
                    }
                }
                lifted.push((offset, IRInst::ClearFlags { flags }));
            }
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => {
                lifted.push((
                    offset,
                    IRInst::If {
                        condition: lift_condition(condition, &slots),
                        then_branch,
                        else_branch,
                    },
                ));
            }
            instr => lifted.push((offset, instr)),
        }
    }
    lifted
}

pub fn lift(source: &IRT0Program) -> Program {
    let instructions = strip_frame_saves(&source.instructions);
    if instructions.is_empty() {
        return Program {
            entry_address: source.entry_address,
            entry: None,
            stack_widths: HashMap::new(),
            functions: Vec::new(),
        };
    }

    let mut builder = SyntheticFunctionBuilder {
        source: &instructions,
        entry_address: source.entry_address,
        jump_entries: HashSet::new(),
        by_start: HashMap::new(),
        functions: Vec::new(),
    };

    for (offset, instr) in &instructions {
        let target = match instr {
            IRT0Inst::Jmp(target) => Some(target),
            IRT0Inst::If(_, inner) => match inner.as_ref() {
                IRT0Inst::Jmp(target) => Some(target),
                _ => None,
            },
            _ => None,
        };
        if let Some(index) = target.and_then(|expr| builder.local_target(expr, *offset)) {
            builder.jump_entries.insert(index);
        }
    }

    let entry = builder.function(0);
    for (id, function) in builder.functions.iter_mut().enumerate() {
        let body = std::mem::take(&mut function.body);
        function.body = lift_conditions(SyntheticFunctionId { id }, body);
    }
    let mut program = prune_flags::tr(Program {
        entry_address: source.entry_address,
        entry: Some(entry),
        stack_widths: HashMap::new(),
        functions: builder.functions,
    });
    return_registers::run(&mut program);
    register_parameters::tr(program)
}
