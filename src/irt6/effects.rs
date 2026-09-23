//! Conservative effects shared by restructuring and arithmetic recognition.

use std::collections::HashSet;

use super::ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, VariableId};

#[derive(Debug, Default)]
pub(super) struct Effects {
    pub reads: HashSet<VariableId>,
    pub writes: HashSet<VariableId>,
    pub memory_read: bool,
    pub memory_write: bool,
    pub control: bool,
    pub may_trap: bool,
    pub unknown_write: bool,
}

impl Effects {
    pub fn expression(&mut self, expr: &IRExpr) {
        match expr {
            IRExpr::Variable(variable) => {
                self.reads.insert(*variable);
            }
            IRExpr::BinOp { kind, lhs, rhs } => {
                self.may_trap |= *kind == IRBinOpKind::UnsignedMod;
                self.expression(lhs);
                self.expression(rhs);
            }
            IRExpr::Deref(address) => {
                self.memory_read = true;
                self.expression(address);
            }
            IRExpr::ElementAddress { base, index, .. } => {
                self.expression(base);
                self.expression(index);
            }
            IRExpr::MemoryAddress { address: inner, .. }
            | IRExpr::Convert { value: inner, .. }
            | IRExpr::Not(inner) => self.expression(inner),
            IRExpr::Argument(_)
            | IRExpr::CU8(_)
            | IRExpr::CU32(_)
            | IRExpr::CU64(_)
            | IRExpr::Bool(_) => {}
        }
    }

    pub fn instruction(&mut self, instr: &IRInst) {
        match instr {
            IRInst::Assign {
                dest: IRExpr::Variable(variable),
                src,
            }
            | IRInst::AssignVariable {
                variable,
                value: src,
            }
            | IRInst::DeclareAndAssignVariable {
                variable,
                value: src,
                ..
            } => {
                self.expression(src);
                self.writes.insert(*variable);
            }
            IRInst::CompoundAssign {
                dest: IRExpr::Variable(variable),
                kind,
                value,
            } => {
                self.reads.insert(*variable);
                self.expression(value);
                self.may_trap |= *kind == IRBinOpKind::UnsignedMod;
                self.writes.insert(*variable);
            }
            IRInst::CompoundAssign { dest, kind, value } => {
                self.expression(dest);
                self.expression(value);
                self.may_trap |= *kind == IRBinOpKind::UnsignedMod;
                self.memory_write = true;
                self.unknown_write |= !matches!(dest, IRExpr::Deref(_));
            }
            IRInst::Assign { dest, src } => {
                self.expression(dest);
                self.expression(src);
                self.memory_write = true;
                self.unknown_write |= !matches!(dest, IRExpr::Deref(_));
            }
            IRInst::DeclareVariable { variable, .. } => {
                self.writes.insert(*variable);
            }
            IRInst::LoadVariable { variable, address } => {
                self.expression(address);
                self.writes.insert(*variable);
                self.memory_read = true;
            }
            IRInst::StoreVariable { address, variable } => {
                self.expression(address);
                self.reads.insert(*variable);
                self.memory_write = true;
            }
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.control = true;
                self.expression(condition);
                for instr in then_branch.iter().chain(else_branch) {
                    self.instruction(instr);
                }
            }
            IRInst::While {
                condition, body, ..
            } => {
                self.control = true;
                let (LoopCondition::Before { expression, .. }
                | LoopCondition::After { expression, .. }) = condition;
                self.expression(expression);
                for (_, instr) in body {
                    self.instruction(instr);
                }
            }
            IRInst::ForEach {
                variable,
                vector,
                body,
                ..
            } => {
                self.control = true;
                self.expression(vector);
                self.memory_read = true;
                self.writes.insert(*variable);
                for (_, instr) in body {
                    self.instruction(instr);
                }
            }
            IRInst::Return(value) => {
                self.control = true;
                if let Some(value) = value {
                    self.expression(value);
                }
            }
            IRInst::Jump(value) => {
                self.control = true;
                self.expression(value);
            }
            IRInst::CallSynthetic { arguments, .. } => {
                self.control = true;
                self.memory_read = true;
                self.memory_write = true;
                for argument in arguments {
                    self.expression(argument);
                }
            }
            IRInst::Break | IRInst::Continue | IRInst::ContinueLoop(_) | IRInst::End => {
                self.control = true;
            }
        }
    }

    pub fn of_expression(expr: &IRExpr) -> Self {
        let mut effects = Self::default();
        effects.expression(expr);
        effects
    }
}

pub(super) fn repeatable(expr: &IRExpr) -> bool {
    let effects = Effects::of_expression(expr);
    !effects.memory_read && !effects.may_trap
}
