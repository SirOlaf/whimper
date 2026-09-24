use super::{IRBinOpKind, IRExpr, IRInst};

/// Push a negation through a short-circuit Boolean chain. Bitwise And is
/// intentionally excluded: replacing it with a logical Or would change its
/// value and evaluation behavior.
pub fn de_morgan(expr: &IRExpr) -> Option<IRExpr> {
    let IRExpr::Not(inner) = expr else {
        return None;
    };
    let IRExpr::BinOp { kind, lhs, rhs } = inner.as_ref() else {
        return None;
    };
    distribute_negation(kind, lhs, rhs)
}

fn distribute_negation(kind: &IRBinOpKind, lhs: &IRExpr, rhs: &IRExpr) -> Option<IRExpr> {
    let opposite = match kind {
        IRBinOpKind::Or => IRBinOpKind::LogicalAnd,
        IRBinOpKind::LogicalAnd => IRBinOpKind::Or,
        _ => return None,
    };
    Some(IRExpr::BinOp {
        kind: opposite,
        lhs: Box::new(negate_boolean(lhs)),
        rhs: Box::new(negate_boolean(rhs)),
    })
}

fn negate_boolean(expr: &IRExpr) -> IRExpr {
    if let IRExpr::BinOp { kind, lhs, rhs } = expr {
        if let Some(distributed) = distribute_negation(kind, lhs, rhs) {
            return distributed;
        }
        let opposite = match kind {
            IRBinOpKind::Eq => Some(IRBinOpKind::Ne),
            IRBinOpKind::Ne => Some(IRBinOpKind::Eq),
            IRBinOpKind::SignedGt => Some(IRBinOpKind::SignedLe),
            IRBinOpKind::SignedLe => Some(IRBinOpKind::SignedGt),
            IRBinOpKind::UnsignedLt => Some(IRBinOpKind::UnsignedGe),
            IRBinOpKind::UnsignedGe => Some(IRBinOpKind::UnsignedLt),
            _ => None,
        };
        if let Some(kind) = opposite {
            return IRExpr::BinOp {
                kind,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            };
        }
    }
    IRExpr::Not(Box::new(expr.clone()))
}

/// Recognize an if whose only actions return zero and one.
/// The condition is evaluated once in either form, so it need not be repeatable.
pub fn boolean_return(instr: &IRInst) -> Option<IRExpr> {
    let IRInst::If {
        condition,
        then_branch,
        else_branch,
    } = instr
    else {
        return None;
    };
    let ([IRInst::Return(Some(then_value))], [IRInst::Return(Some(else_value))]) =
        (&then_branch[..], &else_branch[..])
    else {
        return None;
    };
    let then_is_true = match (then_value, else_value) {
        (IRExpr::Bool(true), IRExpr::Bool(false))
        | (IRExpr::CU8(1), IRExpr::CU8(0))
        | (IRExpr::CU32(1), IRExpr::CU32(0))
        | (IRExpr::CU64(1), IRExpr::CU64(0)) => true,
        (IRExpr::Bool(false), IRExpr::Bool(true))
        | (IRExpr::CU8(0), IRExpr::CU8(1))
        | (IRExpr::CU32(0), IRExpr::CU32(1))
        | (IRExpr::CU64(0), IRExpr::CU64(1)) => false,
        _ => return None,
    };
    Some(if then_is_true {
        // An if can test a non-boolean value. Normalize its truthiness before
        // returning it, so a true condition such as 2 still returns 1.
        IRExpr::Not(Box::new(IRExpr::Not(Box::new(condition.clone()))))
    } else {
        IRExpr::Not(Box::new(condition.clone()))
    })
}
