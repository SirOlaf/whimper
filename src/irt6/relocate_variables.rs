//! Move a local into the sole branch that uses it when its initialization
//! can safely follow the branch condition.

use std::collections::HashSet;

use super::{
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, Parameter, Program, VariableId},
};

trait Slot {
    fn instruction(&self) -> &IRInst;
    fn instruction_mut(&mut self) -> &mut IRInst;
    fn into_instruction(self) -> IRInst;
}

impl Slot for IRInst {
    fn instruction(&self) -> &IRInst {
        self
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        self
    }

    fn into_instruction(self) -> IRInst {
        self
    }
}

impl Slot for (usize, IRInst) {
    fn instruction(&self) -> &IRInst {
        &self.1
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        &mut self.1
    }

    fn into_instruction(self) -> IRInst {
        self.1
    }
}

fn mentions(instr: &IRInst, variable: VariableId) -> bool {
    let mut effects = Effects::default();
    effects.instruction(instr);
    effects.reads.contains(&variable) || effects.writes.contains(&variable)
}

fn expression_mentions(expr: &IRExpr, variable: VariableId) -> bool {
    Effects::of_expression(expr).reads.contains(&variable)
}

fn zero(expr: &IRExpr) -> bool {
    matches!(expr, IRExpr::CU8(0) | IRExpr::CU32(0) | IRExpr::CU64(0))
}

/// CStringLength must read element zero to decide either outcome. The
/// first-byte load can therefore follow that check on its sole live path.
fn covered_first_byte_load(value: &IRExpr, condition: &IRExpr) -> bool {
    let IRExpr::Deref(address) = value else {
        return false;
    };
    let IRExpr::ElementAddress {
        base,
        index,
        element_size: 1,
    } = address.as_ref()
    else {
        return false;
    };
    if !zero(index) || !matches!(base.as_ref(), IRExpr::Argument(_) | IRExpr::Variable(_)) {
        return false;
    }
    let IRExpr::BinOp { kind, lhs, rhs } = condition else {
        return false;
    };
    if !matches!(kind, IRBinOpKind::Eq | IRBinOpKind::Ne) {
        return false;
    }
    matches!(lhs.as_ref(), IRExpr::CStringLength(source) if source == base) && zero(rhs)
        || matches!(rhs.as_ref(), IRExpr::CStringLength(source) if source == base) && zero(lhs)
}

fn movable(initializer: &IRInst, condition: &IRExpr) -> bool {
    match initializer {
        IRInst::DeclareVariable { .. } => true,
        IRInst::DeclareAndAssignVariable {
            variable, value, ..
        } => {
            !expression_mentions(value, *variable)
                && (repeatable(value) || covered_first_byte_load(value, condition))
        }
        _ => false,
    }
}

fn relocate<T: Slot>(body: &mut Vec<T>, parameters: &HashSet<VariableId>) {
    let mut index = 0;
    while index + 1 < body.len() {
        let variable = match body[index].instruction() {
            IRInst::DeclareVariable { variable, .. }
            | IRInst::DeclareAndAssignVariable { variable, .. } => *variable,
            _ => {
                index += 1;
                continue;
            }
        };
        if parameters.contains(&variable) {
            index += 1;
            continue;
        }
        let destination = match body[index + 1].instruction() {
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } if !expression_mentions(condition, variable)
                && movable(body[index].instruction(), condition)
                && !body[index + 2..]
                    .iter()
                    .any(|slot| mentions(slot.instruction(), variable)) =>
            {
                let then_uses = then_branch.iter().any(|instr| mentions(instr, variable));
                let else_uses = else_branch.iter().any(|instr| mentions(instr, variable));
                match (then_uses, else_uses) {
                    (true, false) => Some(true),
                    (false, true) => Some(false),
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(into_then) = destination {
            let initializer = body.remove(index).into_instruction();
            let IRInst::If {
                then_branch,
                else_branch,
                ..
            } = body[index].instruction_mut()
            else {
                unreachable!();
            };
            if into_then {
                then_branch.insert(0, initializer);
            } else {
                else_branch.insert(0, initializer);
            }
            // The next declaration may now be adjacent to the same branch.
        } else {
            index += 1;
        }
    }
    for slot in body {
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                relocate(then_branch, parameters);
                relocate(else_branch, parameters);
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                relocate(body, parameters);
            }
            _ => {}
        }
    }
}

pub(super) fn run(program: &mut Program) {
    for function in &mut program.functions {
        let parameters = function
            .parameters
            .iter()
            .filter_map(|parameter| match parameter {
                Parameter::Slot { variable, .. } => Some(*variable),
                Parameter::Argument { .. } => None,
            })
            .collect();
        relocate(&mut function.body, &parameters);
    }
}
