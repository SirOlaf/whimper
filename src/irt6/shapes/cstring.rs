use super::{Context, IRBinOpKind, IRExpr, VariableId, VariableType, unsigned_constant};

/// A cached read of the first byte is an empty-string check once its base has
/// been promoted to CString. The caller proves the cached load is still valid.
pub fn cstring_empty_check(
    condition: &IRExpr,
    loaded_from: &std::collections::HashMap<VariableId, IRExpr>,
    context: &Context,
) -> Option<IRExpr> {
    let IRExpr::BinOp {
        kind: IRBinOpKind::Eq,
        lhs,
        rhs,
    } = condition
    else {
        return None;
    };
    let variable = match (lhs.as_ref(), rhs.as_ref()) {
        (IRExpr::Variable(variable), zero) | (zero, IRExpr::Variable(variable))
            if unsigned_constant(zero) == Some(0) =>
        {
            *variable
        }
        _ => return None,
    };
    let IRExpr::ElementAddress {
        base,
        index,
        element_size: 1,
    } = loaded_from.get(&variable)?
    else {
        return None;
    };
    if unsigned_constant(index) != Some(0)
        || context.direct_type(base.as_ref()) != Some(&VariableType::CString)
    {
        return None;
    }
    Some(IRExpr::BinOp {
        kind: IRBinOpKind::Eq,
        lhs: Box::new(IRExpr::CStringLength(base.clone())),
        rhs: Box::new(IRExpr::CU64(0)),
    })
}
