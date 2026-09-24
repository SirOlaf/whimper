use super::{Context, Effects, IRBinOpKind, IRExpr, IRInst, VariableId, repeatable};

#[derive(Debug, Clone)]
pub struct CompoundAssignment {
    pub dest: IRExpr,
    pub kind: IRBinOpKind,
    pub value: IRExpr,
}

#[derive(Debug, Clone)]
pub struct TemporaryBinaryAssignment {
    pub temporary: VariableId,
    pub replacement: IRInst,
}

/// Recognize `let t = a; t = t op b; destination = t`. The operands and
/// destination address must be safe to move into one assignment expression.
/// The caller proves that no other instruction uses or writes `t`.
pub fn temporary_binary_assignment(
    declaration: &IRInst,
    operation: &IRInst,
    write: &IRInst,
    context: &Context,
) -> Option<TemporaryBinaryAssignment> {
    let IRInst::DeclareAndAssignVariable {
        variable: temporary,
        value: initial,
        ..
    } = declaration
    else {
        return None;
    };
    let (kind, rhs) = match operation {
        IRInst::CompoundAssign {
            dest: IRExpr::Variable(variable),
            kind,
            value,
        } if variable == temporary => (kind, value),
        IRInst::AssignVariable { variable, value }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } if variable == temporary => {
            let IRExpr::BinOp { kind, lhs, rhs } = value else {
                return None;
            };
            if lhs.as_ref() != &IRExpr::Variable(*temporary) {
                return None;
            }
            (kind, rhs.as_ref())
        }
        _ => return None,
    };
    let initial_effects = Effects::of_expression(initial);
    let rhs_effects = Effects::of_expression(rhs);
    if !repeatable(initial)
        || !repeatable(rhs)
        || initial_effects.reads.contains(temporary)
        || rhs_effects.reads.contains(temporary)
    {
        return None;
    }
    let bits = context.value(&IRExpr::Variable(*temporary)).bits?;
    let combined = IRExpr::BinOp {
        kind: kind.clone(),
        lhs: Box::new(initial.clone()),
        rhs: Box::new(rhs.clone()),
    };
    if context.value(initial).bits != Some(bits) || context.value(&combined).bits != Some(bits) {
        return None;
    }
    let replacement = match write {
        IRInst::StoreVariable { address, variable } if variable == temporary => IRInst::Assign {
            dest: IRExpr::Deref(Box::new(address.clone())),
            src: combined,
        },
        IRInst::Assign {
            dest,
            src: IRExpr::Variable(variable),
        } if variable == temporary && matches!(dest, IRExpr::Variable(_) | IRExpr::Deref(_)) => {
            IRInst::Assign {
                dest: dest.clone(),
                src: combined,
            }
        }
        IRInst::AssignVariable {
            variable,
            value: IRExpr::Variable(source),
        } if source == temporary && variable != temporary => IRInst::AssignVariable {
            variable: *variable,
            value: combined,
        },
        _ => return None,
    };
    let destination = match &replacement {
        IRInst::Assign { dest, .. } => dest,
        IRInst::AssignVariable { variable, .. } => {
            if context.value(&IRExpr::Variable(*variable)).bits != Some(bits) {
                return None;
            }
            return Some(TemporaryBinaryAssignment {
                temporary: *temporary,
                replacement,
            });
        }
        _ => unreachable!(),
    };
    let address = match destination {
        IRExpr::Deref(address) => address.as_ref(),
        _ => destination,
    };
    if !repeatable(address)
        || Effects::of_expression(address).reads.contains(temporary)
        || context.value(destination).bits != Some(bits)
    {
        return None;
    }
    Some(TemporaryBinaryAssignment {
        temporary: *temporary,
        replacement,
    })
}

/// Recognize `a = a op b`, including the variable-specific assignment form.
/// Only commutative, eagerly evaluated operations may match `a = b op a`.
pub fn compound_assignment(instr: &IRInst) -> Option<CompoundAssignment> {
    let (dest, source) = match instr {
        IRInst::Assign { dest, src }
            if matches!(dest, IRExpr::Variable(_))
                || matches!(dest, IRExpr::Deref(address) if repeatable(address)) =>
        {
            (dest.clone(), src)
        }
        IRInst::AssignVariable { variable, value } => (IRExpr::Variable(*variable), value),
        _ => return None,
    };
    let IRExpr::BinOp { kind, lhs, rhs } = source else {
        return None;
    };
    if !matches!(
        kind,
        IRBinOpKind::Add
            | IRBinOpKind::Sub
            | IRBinOpKind::UnsignedMod
            | IRBinOpKind::Shl
            | IRBinOpKind::And
            | IRBinOpKind::Or
    ) {
        return None;
    }
    let value = if dest == **lhs {
        rhs.as_ref().clone()
    } else if matches!(dest, IRExpr::Variable(_))
        && matches!(kind, IRBinOpKind::Add | IRBinOpKind::And)
        && dest == **rhs
    {
        lhs.as_ref().clone()
    } else {
        return None;
    };
    Some(CompoundAssignment {
        dest,
        kind: kind.clone(),
        value,
    })
}
