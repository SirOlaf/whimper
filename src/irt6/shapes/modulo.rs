use super::{Context, IRBinOpKind, IRExpr, IRInst, repeatable};

#[derive(Debug, Clone)]
pub struct GuardedModulo {
    pub destination: IRExpr,
    pub dividend: IRExpr,
    pub replacement: IRInst,
}

/// Recognize a sole modulo assignment under `dividend u>= stride` (or the
/// opposite branch of `dividend u< stride`). The caller proves that skipping
/// the assignment leaves its destination equal to the dividend.
pub fn guarded_modulo(instr: &IRInst, context: &Context) -> Option<GuardedModulo> {
    let IRInst::If {
        condition,
        then_branch,
        else_branch,
    } = instr
    else {
        return None;
    };
    if !repeatable(condition) {
        return None;
    }
    let (operation, guard) = if let ([operation], []) = (&then_branch[..], &else_branch[..]) {
        (operation, context.value(condition))
    } else if let ([], [operation]) = (&then_branch[..], &else_branch[..]) {
        (operation, context.value(condition).negated())
    } else {
        return None;
    };
    let (destination, dividend, stride) = match operation {
        IRInst::AssignVariable {
            variable,
            value:
                IRExpr::BinOp {
                    kind: IRBinOpKind::UnsignedMod,
                    lhs,
                    rhs,
                },
        } => (
            IRExpr::Variable(*variable),
            lhs.as_ref().clone(),
            rhs.as_ref(),
        ),
        IRInst::Assign {
            dest,
            src:
                IRExpr::BinOp {
                    kind: IRBinOpKind::UnsignedMod,
                    lhs,
                    rhs,
                },
        } => (dest.clone(), lhs.as_ref().clone(), rhs.as_ref()),
        IRInst::CompoundAssign {
            dest,
            kind: IRBinOpKind::UnsignedMod,
            value,
        } => (dest.clone(), dest.clone(), value),
        _ => return None,
    };
    if !repeatable(&dividend) || !repeatable(stride) {
        return None;
    }
    let bits = context.value(&dividend).bits?;
    if !matches!(bits, 8 | 16 | 32 | 64) || context.value(stride).bits != Some(bits) {
        return None;
    }
    let expected = IRExpr::BinOp {
        kind: IRBinOpKind::UnsignedGe,
        lhs: Box::new(dividend.clone()),
        rhs: Box::new(stride.clone()),
    };
    if guard != context.value(&expected) {
        return None;
    }
    Some(GuardedModulo {
        destination,
        dividend,
        replacement: operation.clone(),
    })
}
