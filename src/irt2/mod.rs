pub mod ir;
pub mod render;

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
        t1::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t1::IRBinOpKind::And => IRBinOpKind::And,
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

// A dereference does not reveal its width from its address. Look for a data
// register in the surrounding operation; the destination takes priority.
fn source_width(expr: &t1::IRExpr) -> Option<usize> {
    match expr {
        t1::IRExpr::Reg(register) => Some(register.size()),
        t1::IRExpr::BinOp { lhs, rhs, .. }
        | t1::IRExpr::Eq(lhs, rhs)
        | t1::IRExpr::UnsignedLt(lhs, rhs)
        | t1::IRExpr::Or(lhs, rhs) => source_width(lhs).or_else(|| source_width(rhs)),
        t1::IRExpr::Not(inner) => source_width(inner),
        t1::IRExpr::Deref(_)
        | t1::IRExpr::CU8(_)
        | t1::IRExpr::CU32(_)
        | t1::IRExpr::CU64(_)
        | t1::IRExpr::Variable(_)
        | t1::IRExpr::Bool(_) => None,
        _ => panic!("tier 1 produced an unsupported expression: {expr:?}"),
    }
}

fn register_offset(register: Register) -> usize {
    match register {
        Register::AH | Register::BH | Register::CH | Register::DH => 1,
        _ => 0,
    }
}

struct FunctionLifter {
    owner: SyntheticFunctionId,
    next_variable: usize,
    declarations: Vec<(VariableId, VariableType)>,
    source_variables: HashMap<t1::VariableId, VariableId>,
    registers: HashMap<Register, IRExpr>,
}

impl FunctionLifter {
    fn new(owner: SyntheticFunctionId) -> Self {
        Self {
            owner,
            next_variable: 0,
            declarations: Vec::new(),
            source_variables: HashMap::new(),
            registers: HashMap::new(),
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
        self.declarations.push((variable, ty));
        variable
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
        // The low 32 bits of a zero-extended 32-bit write are its slot.
        if offset == 0
            && size == 4
            && let IRExpr::ZeroExtend { value, .. } = current
        {
            return (**value).clone();
        }
        IRExpr::ExtractBytes {
            value: Box::new(current.clone()),
            offset,
            size,
        }
    }

    fn write_register(&mut self, register: Register) -> VariableId {
        let variable = self.slot(VariableType::Unknown(Some(register.size())));
        let full = register.full_register();
        let written = IRExpr::Variable(variable);
        let next = if register == full {
            written
        } else if register.is_gpr32() && full.size() == 8 {
            IRExpr::ZeroExtend {
                value: Box::new(written),
                size: 8,
            }
        } else {
            let original = self.registers.get(&full).unwrap_or_else(|| {
                panic!(
                    "tier 1 omitted the preserved bits of {full:?} in fn_{}",
                    self.owner.id
                )
            });
            IRExpr::ReplaceBytes {
                original: Box::new(original.clone()),
                value: Box::new(written),
                offset: register_offset(register),
                size: register.size(),
            }
        };
        self.registers.insert(full, next);
        variable
    }

    fn expr(
        &mut self,
        expr: &t1::IRExpr,
        width: Option<usize>,
        before: &mut Vec<IRInst>,
    ) -> IRExpr {
        match expr {
            t1::IRExpr::BinOp { kind, lhs, rhs } => {
                let width = width.or_else(|| source_width(expr));
                IRExpr::BinOp {
                    kind: lift_bin_op(kind),
                    lhs: Box::new(self.expr(lhs, width, before)),
                    rhs: Box::new(self.expr(rhs, width, before)),
                }
            }
            t1::IRExpr::Deref(address) => {
                let global = is_global_address(address);
                let address = IRExpr::CastUnknownPtr {
                    address: Box::new(self.expr(address, None, before)),
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
            t1::IRExpr::Eq(lhs, rhs) => IRExpr::Eq(
                Box::new(self.expr(lhs, width, before)),
                Box::new(self.expr(rhs, width, before)),
            ),
            t1::IRExpr::UnsignedLt(lhs, rhs) => IRExpr::UnsignedLt(
                Box::new(self.expr(lhs, width, before)),
                Box::new(self.expr(rhs, width, before)),
            ),
            t1::IRExpr::Or(lhs, rhs) => IRExpr::Or(
                Box::new(self.expr(lhs, width, before)),
                Box::new(self.expr(rhs, width, before)),
            ),
            t1::IRExpr::Not(inner) => IRExpr::Not(Box::new(self.expr(inner, width, before))),
            _ => panic!("tier 1 produced an unsupported expression: {expr:?}"),
        }
    }

    fn inst(&mut self, instr: &t1::IRInst) -> Vec<IRInst> {
        let mut before = Vec::new();
        let lifted = match instr {
            t1::IRInst::Assign { dest, src } => {
                let width = match dest {
                    t1::IRExpr::Reg(register) => Some(register.size()),
                    _ => source_width(src),
                };
                let src = self.expr(src, width, &mut before);
                match dest {
                    t1::IRExpr::Reg(register) => {
                        let variable = self.write_register(*register);
                        IRInst::AssignVariable {
                            variable,
                            value: src,
                        }
                    }
                    t1::IRExpr::Deref(address) => {
                        let global = is_global_address(address);
                        let address = IRExpr::CastUnknownPtr {
                            address: Box::new(self.expr(address, None, &mut before)),
                            size: width,
                        };
                        if !global {
                            let variable = self.slot(VariableType::Unknown(width));
                            before.push(IRInst::AssignVariable {
                                variable,
                                value: src,
                            });
                            before.push(IRInst::StoreVariable { address, variable });
                            return before;
                        }
                        IRInst::Assign {
                            dest: IRExpr::Deref(Box::new(address)),
                            src,
                        }
                    }
                    dest => IRInst::Assign {
                        dest: self.expr(dest, width, &mut before),
                        src,
                    },
                }
            }
            t1::IRInst::Return(value) => IRInst::Return(
                value
                    .as_ref()
                    .map(|value| self.expr(value, source_width(value), &mut before)),
            ),
            t1::IRInst::DeclareVariable { .. } => return before,
            t1::IRInst::AssignVariable { variable, value } => IRInst::AssignVariable {
                variable: self.source_variables[variable],
                value: self.expr(value, source_width(value), &mut before),
            },
            t1::IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => IRInst::If {
                condition: self.expr(condition, source_width(condition), &mut before),
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
                    .map(|argument| self.expr(argument, source_width(argument), &mut before))
                    .collect(),
            },
            t1::IRInst::Jump(target) => {
                IRInst::Jump(self.expr(target, source_width(target), &mut before))
            }
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
                lifter
                    .registers
                    .insert(register.full_register(), IRExpr::Argument(index + 1));
                Parameter::Native {
                    ordinal: index + 1,
                    register: *register,
                }
            } else {
                let variable = lifter.variable_id();
                lifter
                    .registers
                    .insert(register.full_register(), IRExpr::Variable(variable));
                Parameter::Slot {
                    variable,
                    size: register.size(),
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
    Program {
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
    }
}
