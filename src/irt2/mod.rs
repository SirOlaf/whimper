mod constants;
pub mod ir;
pub mod render;
mod values;

use std::collections::HashMap;

use iced_x86::Register;

use crate::irt1::ir as t1;

use self::ir::{
    IRBinOpKind, IRExpr, IRInst, Parameter, Program, SyntheticFunction, SyntheticFunctionId,
    VariableId, VariableType,
};

fn lift_bin_op(kind: &t1::IRBinOpKind) -> IRBinOpKind {
    match kind {
        t1::IRBinOpKind::Add => IRBinOpKind::Add,
        t1::IRBinOpKind::Sub => IRBinOpKind::Sub,
        t1::IRBinOpKind::Mul => IRBinOpKind::Mul,
        t1::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t1::IRBinOpKind::And => IRBinOpKind::And,
        t1::IRBinOpKind::Or => IRBinOpKind::Or,
        t1::IRBinOpKind::Eq => IRBinOpKind::Eq,
        t1::IRBinOpKind::SignedGt => IRBinOpKind::SignedGt,
        t1::IRBinOpKind::UnsignedLt => IRBinOpKind::UnsignedLt,
    }
}

// Tier 1 emits absolute addresses as constants. Register-derived addresses
// still need a memory access even when their displacement is constant.
fn is_global_address(address: &t1::IRExpr) -> bool {
    match address {
        t1::IRExpr::CU8(_) | t1::IRExpr::CU32(_) | t1::IRExpr::CU64(_) => true,
        t1::IRExpr::BinOp { lhs, rhs, .. } => is_global_address(lhs) && is_global_address(rhs),
        _ => false,
    }
}

fn register_offset(register: Register) -> usize {
    match register {
        Register::AH | Register::BH | Register::CH | Register::DH => 1,
        _ => 0,
    }
}

fn widen_register_value(register: Register, value: IRExpr) -> IRExpr {
    let full = register.full_register();
    values::convert(value, register.size(), full.size(), false)
}

struct FunctionLifter {
    owner: SyntheticFunctionId,
    next_variable: usize,
    declarations: Vec<(VariableId, VariableType)>,
    source_variables: HashMap<t1::VariableId, VariableId>,
    registers: HashMap<Register, IRExpr>,
    widths: HashMap<VariableId, usize>,
    argument_widths: HashMap<usize, usize>,
}

impl FunctionLifter {
    fn new(owner: SyntheticFunctionId) -> Self {
        Self {
            owner,
            next_variable: 0,
            declarations: Vec::new(),
            source_variables: HashMap::new(),
            registers: HashMap::new(),
            widths: HashMap::new(),
            argument_widths: HashMap::new(),
        }
    }

    fn variable_id(&mut self) -> VariableId {
        let variable = VariableId {
            owner: self.owner,
            id: self.next_variable,
        };
        self.next_variable += 1;
        variable
    }

    fn slot(&mut self, ty: VariableType) -> VariableId {
        let variable = self.variable_id();
        let width = match ty {
            VariableType::Register(register) => Some(register.size()),
            VariableType::Unknown(size) => size,
            VariableType::Bool => Some(1),
        };
        if let Some(width) = width {
            self.widths.insert(variable, width);
        }
        self.declarations.push((variable, ty));
        variable
    }

    fn width(&self, value: &IRExpr) -> Option<usize> {
        values::width(value, &self.widths, &self.argument_widths)
    }

    fn extract(&self, value: IRExpr, offset: usize, size: usize) -> IRExpr {
        let width = self.width(&value).expect("unknown register value width");
        assert!(
            offset + size <= width,
            "register read exceeds its value width"
        );
        if offset == 0 {
            return values::convert(value, width, size, false);
        }
        if let Some((bits, _)) = values::constant(&value) {
            return values::literal(bits >> (offset * 8), size);
        }
        if let IRExpr::Convert {
            value: inner,
            source,
            target,
        } = &value
            && !source.signed
            && target.size > source.size
        {
            if offset >= source.size {
                return values::literal(0, size);
            }
            if offset + size <= source.size {
                return self.extract((**inner).clone(), offset, size);
            }
        }
        let shifted = values::binary(
            IRBinOpKind::Shr,
            value,
            IRExpr::CU8((offset * 8) as u8),
            width,
        );
        values::convert(shifted, width, size, false)
    }

    fn read_register(&self, register: Register) -> IRExpr {
        let full = register.full_register();
        let current = self.registers.get(&full).unwrap_or_else(|| {
            panic!(
                "tier 1 omitted an incoming value for {register:?} in fn_{}",
                self.owner.id
            )
        });
        if register == full {
            return current.clone();
        }
        let offset = register_offset(register);
        let size = register.size();
        self.extract(current.clone(), offset, size)
    }

    fn write_register(&mut self, register: Register, value: IRExpr) {
        let full = register.full_register();
        let next = if register == full {
            value
        } else if register.is_gpr32() && full.size() == 8 {
            values::convert(value, 4, 8, false)
        } else {
            let original = self
                .registers
                .get(&full)
                .cloned()
                .expect("tier 1 omitted the preserved part of a partial register write");
            let shift = register_offset(register) * 8;
            let field_mask = values::mask(register.size()) << shift;
            let preserved = values::binary(
                IRBinOpKind::And,
                original,
                values::literal(!field_mask, full.size()),
                full.size(),
            );
            let extended = values::convert(value, register.size(), full.size(), false);
            let inserted = values::binary(
                IRBinOpKind::Shl,
                extended,
                IRExpr::CU8(shift as u8),
                full.size(),
            );
            values::binary(IRBinOpKind::BitOr, preserved, inserted, full.size())
        };
        self.registers.insert(full, next);
    }

    fn expr(&mut self, expr: &t1::IRExpr, before: &mut Vec<IRInst>) -> IRExpr {
        match expr {
            t1::IRExpr::BinOp { kind, lhs, rhs } => {
                let lhs = self.expr(lhs, before);
                let rhs = self.expr(rhs, before);
                let size =
                    if values::constant(&lhs).is_some() && !matches!(kind, t1::IRBinOpKind::Shl) {
                        self.width(&rhs).or_else(|| self.width(&lhs))
                    } else {
                        self.width(&lhs).or_else(|| self.width(&rhs))
                    }
                    .expect("unknown arithmetic width");
                values::binary(lift_bin_op(kind), lhs, rhs, size)
            }
            t1::IRExpr::ExtractBytes {
                value,
                offset,
                size,
            } => {
                let value = self.expr(value, before);
                self.extract(value, *offset, *size)
            }
            t1::IRExpr::ZeroExtend { value, size } | t1::IRExpr::SignExtend { value, size } => {
                let value = self.expr(value, before);
                let from = self.width(&value).expect("unknown conversion input width");
                values::convert(
                    value,
                    from,
                    *size,
                    matches!(expr, t1::IRExpr::SignExtend { .. }),
                )
            }
            t1::IRExpr::Deref { address, size } => {
                let width = Some(*size);
                let global = is_global_address(address);
                let address = IRExpr::CastUnknownPtr {
                    address: Box::new(self.expr(address, before)),
                    size: width,
                };
                if global {
                    IRExpr::Deref(Box::new(address))
                } else {
                    // Keep repeated accesses distinct across stores and calls.
                    let variable = self.slot(VariableType::Unknown(width));
                    before.push(IRInst::LoadVariable { variable, address });
                    IRExpr::Variable(variable)
                }
            }
            t1::IRExpr::Reg(register) => self.read_register(*register),
            t1::IRExpr::CU8(value) => IRExpr::CU8(*value),
            t1::IRExpr::CU32(value) => IRExpr::CU32(*value),
            t1::IRExpr::CU64(value) => IRExpr::CU64(*value),
            t1::IRExpr::Variable(variable) => IRExpr::Variable(self.source_variables[variable]),
            t1::IRExpr::Bool(value) => IRExpr::Bool(*value),
            t1::IRExpr::Not(inner) => IRExpr::Not(Box::new(self.expr(inner, before))),
            _ => panic!("tier 1 produced an unsupported expression: {expr:?}"),
        }
    }

    fn inst(&mut self, instr: &t1::IRInst) -> Vec<IRInst> {
        let mut before = Vec::new();
        let lifted = match instr {
            t1::IRInst::Assign { dest, src } => {
                let src = self.expr(src, &mut before);
                match dest {
                    t1::IRExpr::Reg(register) => {
                        let width = self.width(&src).expect("unknown register assignment width");
                        let src = values::convert(src, width, register.size(), false);
                        // Constants and immutable snapshots need no register slot.
                        if values::snapshot(&src) {
                            self.write_register(*register, src);
                            return before;
                        }
                        let variable = self.slot(VariableType::Register(*register));
                        self.write_register(*register, IRExpr::Variable(variable));
                        IRInst::AssignVariable {
                            variable,
                            value: src,
                        }
                    }
                    t1::IRExpr::Deref { address, size } => {
                        let width = Some(*size);
                        let address = IRExpr::CastUnknownPtr {
                            address: Box::new(self.expr(address, &mut before)),
                            size: width,
                        };
                        if let IRExpr::Variable(variable) = src {
                            IRInst::StoreVariable { address, variable }
                        } else {
                            IRInst::Assign {
                                dest: IRExpr::Deref(Box::new(address)),
                                src,
                            }
                        }
                    }
                    dest => IRInst::Assign {
                        dest: self.expr(dest, &mut before),
                        src,
                    },
                }
            }
            t1::IRInst::Return(value) => {
                IRInst::Return(value.as_ref().map(|value| self.expr(value, &mut before)))
            }
            t1::IRInst::DeclareVariable { .. } => return before,
            t1::IRInst::AssignVariable { variable, value } => IRInst::AssignVariable {
                variable: self.source_variables[variable],
                value: self.expr(value, &mut before),
            },
            t1::IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => IRInst::If {
                condition: self.expr(condition, &mut before),
                then_branch: self.inst(then_branch),
                else_branch: self.inst(else_branch),
            },
            t1::IRInst::CallSynthetic {
                function,
                arguments,
            } => IRInst::CallSynthetic {
                function: SyntheticFunctionId { id: function.id },
                arguments: arguments
                    .iter()
                    .map(|argument| self.expr(argument, &mut before))
                    .collect(),
            },
            t1::IRInst::Jump(target) => IRInst::Jump(self.expr(target, &mut before)),
            t1::IRInst::End => IRInst::End,
            _ => panic!("tier 1 produced an unsupported instruction: {instr:?}"),
        };
        before.push(lifted);
        before
    }
}

fn lift_function(id: usize, source: &t1::SyntheticFunction, entry: bool) -> SyntheticFunction {
    let owner = SyntheticFunctionId { id };
    let mut lifter = FunctionLifter::new(owner);

    let parameters = source
        .parameters
        .iter()
        .enumerate()
        .map(|(index, register)| {
            if entry {
                lifter.argument_widths.insert(index + 1, register.size());
                lifter.registers.insert(
                    register.full_register(),
                    widen_register_value(*register, IRExpr::Argument(index + 1)),
                );
                Parameter::Native {
                    ordinal: index + 1,
                    register: *register,
                }
            } else {
                let variable = lifter.variable_id();
                lifter.widths.insert(variable, register.size());
                lifter.registers.insert(
                    register.full_register(),
                    widen_register_value(*register, IRExpr::Variable(variable)),
                );
                Parameter::Slot {
                    variable,
                    register: *register,
                }
            }
        })
        .collect();

    for (_, instr) in &source.body {
        if let t1::IRInst::DeclareVariable { variable, ty } = instr {
            let ty = match ty {
                t1::VariableType::Bool => VariableType::Bool,
            };
            let slot = lifter.slot(ty);
            lifter.source_variables.insert(*variable, slot);
        }
    }

    let mut body = Vec::new();
    for (offset, instr) in &source.body {
        body.extend(lifter.inst(instr).into_iter().map(|instr| (*offset, instr)));
    }
    body.splice(
        0..0,
        lifter.declarations.into_iter().map(|(variable, ty)| {
            (
                source.entry_offset,
                IRInst::DeclareVariable { variable, ty },
            )
        }),
    );

    SyntheticFunction {
        entry_offset: source.entry_offset,
        parameters,
        body,
    }
}

pub fn lift(source: &t1::Program) -> Program {
    let mut program = Program {
        entry: source
            .entry
            .map(|entry| SyntheticFunctionId { id: entry.id }),
        functions: source
            .functions
            .iter()
            .enumerate()
            .map(|(id, function)| {
                lift_function(id, function, source.entry.is_some_and(|e| e.id == id))
            })
            .collect(),
    };
    constants::run(&mut program);
    program
}
