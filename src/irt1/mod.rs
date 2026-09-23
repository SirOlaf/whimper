pub mod ir;
pub mod prune_flags;
pub mod register_parameters;
pub mod render;

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
                IRT0BinOpKind::Shl => IRBinOpKind::Shl,
                IRT0BinOpKind::And => IRBinOpKind::And,
                IRT0BinOpKind::Or => IRBinOpKind::Or,
                IRT0BinOpKind::Eq => IRBinOpKind::Eq,
            },
            lhs: Box::new(lift_expr(*lhs)),
            rhs: Box::new(lift_expr(*rhs)),
        },
        IRT0Expr::Deref(inner) => IRExpr::Deref(Box::new(lift_expr(*inner))),
        IRT0Expr::Reg(reg) => IRExpr::Reg(reg),
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

struct SyntheticFunctionBuilder<'a> {
    source: &'a IRT0Program,
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
            entry_offset: self.source[start].0,
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
                    let IRT0Inst::Jmp(target) = inner.as_ref() else {
                        panic!("tier 1 expects a jump inside a tier 0 conditional");
                    };
                    let then_branch = self.target(target, offset);
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
        IRExpr::Deref(inner) | IRExpr::Not(inner) => condition_flags(inner, flags),
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
            IRInst::SetFlagsFrom { flags, .. } | IRInst::ClearFlags { flags } => {
                flags.contains(&flag)
            }
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
    if source.is_empty() {
        return Program {
            entry: None,
            functions: Vec::new(),
        };
    }

    let mut builder = SyntheticFunctionBuilder {
        source,
        jump_entries: HashSet::new(),
        by_start: HashMap::new(),
        functions: Vec::new(),
    };

    for (offset, instr) in source {
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
    let program = prune_flags::tr(Program {
        entry: Some(entry),
        functions: builder.functions,
    });
    register_parameters::tr(program)
}
