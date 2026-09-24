//! Resolve byte/register operations to integer values before control-flow recovery.

use std::collections::HashMap;

use super::ir::{DataId, IRBinOpKind, IRExpr, IntegerType, VariableId};

pub(super) fn mask(size: usize) -> u64 {
    assert!((1..=8).contains(&size), "unsupported integer width: {size}");
    u64::MAX >> (64 - size * 8)
}

pub(super) fn literal(value: u64, size: usize) -> IRExpr {
    match size {
        1 => IRExpr::CU8(value as u8),
        4 => IRExpr::CU32(value as u32),
        8 => IRExpr::CU64(value),
        2 => IRExpr::Convert {
            value: Box::new(IRExpr::CU32(value as u16 as u32)),
            source: IntegerType {
                size: 4,
                signed: false,
            },
            target: IntegerType {
                size: 2,
                signed: false,
            },
        },
        _ => panic!("unsupported integer width: {size}"),
    }
}

pub(super) fn constant(expr: &IRExpr) -> Option<(u64, usize)> {
    match expr {
        IRExpr::CU8(value) => Some((*value as u64, 1)),
        IRExpr::CU32(value) => Some((*value as u64, 4)),
        IRExpr::CU64(value) => Some((*value, 8)),
        IRExpr::Bool(value) => Some((u64::from(*value), 1)),
        IRExpr::Convert {
            value,
            source,
            target,
        } => {
            let (value, _) = constant(value)?;
            Some((convert_bits(value, *source, *target), target.size))
        }
        _ => None,
    }
}

fn convert_bits(value: u64, source: IntegerType, target: IntegerType) -> u64 {
    let value = value & mask(source.size);
    let extended = if source.signed && value & (1 << (source.size * 8 - 1)) != 0 {
        value | !mask(source.size)
    } else {
        value
    };
    extended & mask(target.size)
}

pub(super) fn width(
    expr: &IRExpr,
    variables: &HashMap<VariableId, usize>,
    arguments: &HashMap<usize, usize>,
    data: &HashMap<DataId, usize>,
) -> Option<usize> {
    match expr {
        IRExpr::Variable(variable) => variables.get(variable).copied(),
        IRExpr::Data(id) => data.get(id).copied(),
        IRExpr::Argument(ordinal) => arguments.get(ordinal).copied(),
        IRExpr::CU8(_) | IRExpr::Bool(_) | IRExpr::Not(_) => Some(1),
        IRExpr::CU32(_) => Some(4),
        IRExpr::CU64(_) => Some(8),
        IRExpr::Convert { target, .. } => Some(target.size),
        IRExpr::CastUnknownPtr { .. } => Some(8),
        IRExpr::Deref(address) => match address.as_ref() {
            IRExpr::CastUnknownPtr { size, .. } => *size,
            _ => None,
        },
        IRExpr::BinOp { kind, lhs, rhs } => match kind {
            IRBinOpKind::Eq | IRBinOpKind::SignedGt | IRBinOpKind::UnsignedLt | IRBinOpKind::Or => {
                Some(1)
            }
            IRBinOpKind::Shl | IRBinOpKind::Shr => width(lhs, variables, arguments, data),
            _ => {
                let left = width(lhs, variables, arguments, data);
                let right = width(rhs, variables, arguments, data);
                if constant(rhs).is_some() {
                    left.or(right)
                } else if constant(lhs).is_some() {
                    right.or(left)
                } else {
                    left.zip(right).map(|(a, b)| a.max(b))
                }
            }
        },
    }
}

pub(super) fn convert(value: IRExpr, from: usize, to: usize, signed: bool) -> IRExpr {
    if from == to {
        return value;
    }
    let source = IntegerType { size: from, signed };
    let target = IntegerType { size: to, signed };
    if let Some((bits, _)) = constant(&value) {
        return literal(convert_bits(bits, source, target), to);
    }
    if let IRExpr::Convert {
        value: inner,
        source: old_source,
        target: old_target,
    } = &value
    {
        // A narrowing read of a widened register does not need its high bits.
        if to <= old_source.size && from == old_target.size && from >= old_source.size {
            return convert((**inner).clone(), old_source.size, to, false);
        }
        // Compose widenings only when they interpret the intermediate sign bit
        // identically, or the intermediate unsigned widening made it zero.
        if from == old_target.size
            && from >= old_source.size
            && to > from
            && (signed == old_source.signed || (!old_source.signed && from > old_source.size))
        {
            return convert((**inner).clone(), old_source.size, to, old_source.signed);
        }
    }
    IRExpr::Convert {
        value: Box::new(value),
        source,
        target,
    }
}

pub(super) fn binary(kind: IRBinOpKind, lhs: IRExpr, rhs: IRExpr, size: usize) -> IRExpr {
    if let (Some((left, _)), Some((right, _))) = (constant(&lhs), constant(&rhs)) {
        let left = left & mask(size);
        let right_bits = right & mask(size);
        let value = match kind {
            IRBinOpKind::Add => left.wrapping_add(right_bits),
            IRBinOpKind::Sub => left.wrapping_sub(right_bits),
            IRBinOpKind::Mul => left.wrapping_mul(right_bits),
            IRBinOpKind::Shl => left.wrapping_shl((right & if size == 8 { 63 } else { 31 }) as u32),
            IRBinOpKind::Shr => left.wrapping_shr((right & if size == 8 { 63 } else { 31 }) as u32),
            IRBinOpKind::And => left & right_bits,
            IRBinOpKind::BitOr => left | right_bits,
            IRBinOpKind::Or => return IRExpr::Bool(left != 0 || right != 0),
            IRBinOpKind::Eq => return IRExpr::Bool(left == right_bits),
            IRBinOpKind::UnsignedLt => return IRExpr::Bool(left < right_bits),
            IRBinOpKind::SignedGt => {
                let shift = 64 - size * 8;
                return IRExpr::Bool(
                    ((left << shift) as i64 >> shift) > ((right_bits << shift) as i64 >> shift),
                );
            }
        };
        return literal(value & mask(size), size);
    }
    let zero = |expr: &IRExpr| constant(expr).is_some_and(|(value, _)| value == 0);
    match kind {
        IRBinOpKind::Add if zero(&lhs) => return rhs,
        IRBinOpKind::Add
        | IRBinOpKind::Sub
        | IRBinOpKind::Shl
        | IRBinOpKind::Shr
        | IRBinOpKind::BitOr
            if zero(&rhs) =>
        {
            return lhs;
        }
        IRBinOpKind::And if lhs == rhs && snapshot(&lhs) => return lhs,
        _ => {}
    }
    IRExpr::BinOp {
        kind,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

/// These values can be substituted repeatedly without repeating memory reads.
pub(super) fn snapshot(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Variable(_) | IRExpr::Argument(_) => true,
        IRExpr::Convert { value, .. } => snapshot(value),
        _ => constant(expr).is_some(),
    }
}
