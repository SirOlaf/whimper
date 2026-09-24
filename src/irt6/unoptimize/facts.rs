use super::super::{
    arithmetic::{Context, Kind, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, VariableId, field_address},
};
use std::collections::HashMap;

#[derive(Clone, Default)]
pub(super) struct Facts {
    conditions: Vec<Value>,
    /// A variable last loaded from an address that has not since been written.
    pub(super) loaded_from: HashMap<VariableId, IRExpr>,
}

fn access(address: &IRExpr) -> Option<(&IRExpr, usize, usize)> {
    let (base, offset, size) = match address {
        IRExpr::MemoryAddress {
            address,
            size: Some(size),
        } => {
            let (base, offset) = field_address(address)?;
            (base, offset, *size)
        }
        IRExpr::ElementAddress {
            base,
            index,
            element_size,
        } => {
            let index = match index.as_ref() {
                IRExpr::CU8(value) => *value as usize,
                IRExpr::CU32(value) => *value as usize,
                IRExpr::CU64(value) => usize::try_from(*value).ok()?,
                _ => return None,
            };
            (
                base.as_ref(),
                index.checked_mul(*element_size)?,
                *element_size,
            )
        }
        _ => return None,
    };
    Some((base, offset, offset.checked_add(size)?))
}

fn disjoint_accesses(left: &IRExpr, right: &IRExpr) -> bool {
    let (Some((left_base, left_start, left_end)), Some((right_base, right_start, right_end))) =
        (access(left), access(right))
    else {
        return false;
    };
    left_base == right_base && (left_end <= right_start || right_end <= left_start)
}

pub(super) fn writes_disjoint(instr: &IRInst, address: &IRExpr) -> bool {
    match instr {
        IRInst::Assign {
            dest: IRExpr::Deref(written),
            ..
        }
        | IRInst::CompoundAssign {
            dest: IRExpr::Deref(written),
            ..
        } => disjoint_accesses(address, written),
        IRInst::StoreVariable {
            address: written, ..
        } => disjoint_accesses(address, written),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .all(|instr| writes_disjoint(instr, address)),
        IRInst::While { body, .. } | IRInst::ForEach { body, .. } => body
            .iter()
            .all(|(_, instr)| writes_disjoint(instr, address)),
        _ => {
            let mut effects = Effects::default();
            effects.instruction(instr);
            !effects.memory_write && !effects.unknown_write
        }
    }
}

impl Facts {
    pub(super) fn assume(&mut self, expression: &IRExpr, truth: bool, context: &Context) {
        if repeatable(expression) {
            let value = context.value(expression);
            self.conditions
                .push(if truth { value } else { value.negated() });
        }
    }

    pub(super) fn invalidate(
        &mut self,
        effects: &Effects,
        writes_disjoint: impl Fn(&IRExpr) -> bool,
    ) {
        if effects.unknown_write {
            self.conditions.clear();
            self.loaded_from.clear();
            return;
        }
        self.conditions
            .retain(|fact| !effects.writes.iter().any(|variable| fact.reads(*variable)));
        self.loaded_from.retain(|variable, address| {
            (!effects.memory_write || writes_disjoint(address))
                && !effects.writes.contains(variable)
                && !effects
                    .writes
                    .iter()
                    .any(|written| Effects::of_expression(address).reads.contains(written))
        });
    }

    pub(super) fn observe(&mut self, instr: &IRInst) {
        let loaded = match instr {
            IRInst::AssignVariable {
                variable,
                value: IRExpr::Deref(address),
            }
            | IRInst::DeclareAndAssignVariable {
                variable,
                value: IRExpr::Deref(address),
                ..
            }
            | IRInst::Assign {
                dest: IRExpr::Variable(variable),
                src: IRExpr::Deref(address),
            } => Some((*variable, address.as_ref())),
            IRInst::LoadVariable { variable, address } => Some((*variable, address)),
            _ => None,
        };
        if let Some((variable, address)) = loaded
            && repeatable(address)
            && !Effects::of_expression(address).reads.contains(&variable)
        {
            self.loaded_from.insert(variable, address.clone());
        }
    }

    pub(super) fn destination_contains(&self, destination: &IRExpr, dividend: &IRExpr) -> bool {
        match (destination, dividend) {
            (IRExpr::Variable(destination), IRExpr::Variable(dividend)) => destination == dividend,
            (IRExpr::Deref(address), IRExpr::Variable(variable)) => {
                self.loaded_from.get(variable) == Some(address.as_ref())
            }
            _ => false,
        }
    }

    pub(super) fn is_zero(&self, value: &Value) -> Option<bool> {
        if let Kind::Constant(constant) = value.kind {
            return Some(constant == 0);
        }
        self.conditions.iter().find_map(|fact| {
            let Kind::Binary { kind, lhs, rhs } = &fact.kind else {
                return None;
            };
            if (lhs.as_ref() == value && matches!(rhs.kind, Kind::Constant(0)))
                || (rhs.as_ref() == value && matches!(lhs.kind, Kind::Constant(0)))
            {
                match kind {
                    IRBinOpKind::Eq => Some(true),
                    IRBinOpKind::Ne => Some(false),
                    _ => None,
                }
            } else {
                None
            }
        })
    }
}
