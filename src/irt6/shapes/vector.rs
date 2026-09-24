use super::{
    Context, Effects, IRBinOpKind, IRExpr, IRInst, LoopCondition, VariableId, VariableType,
    unsigned_constant,
};

#[derive(Debug, Clone)]
pub struct VectorIteration {
    pub counter: VariableId,
    pub element: VariableId,
    pub replacement: IRInst,
}
fn increment_of(instr: &IRInst, counter: VariableId) -> bool {
    let value = match instr {
        IRInst::CompoundAssign {
            dest: IRExpr::Variable(variable),
            kind: IRBinOpKind::Add,
            value,
        } if *variable == counter => return unsigned_constant(value) == Some(1),
        IRInst::AssignVariable { variable, value }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } if *variable == counter => value,
        _ => return false,
    };
    matches!(value, IRExpr::BinOp { kind: IRBinOpKind::Add, lhs, rhs }
        if lhs.as_ref() == &IRExpr::Variable(counter) && unsigned_constant(rhs) == Some(1))
}

fn load_from_index<'a>(
    instr: &'a IRInst,
    element: VariableId,
) -> Option<(&'a IRExpr, &'a IRExpr, usize)> {
    if let IRInst::LoadVariable {
        variable,
        address:
            IRExpr::ElementAddress {
                base,
                index,
                element_size,
            },
    } = instr
        && *variable == element
    {
        return Some((base, index, *element_size));
    }
    let value = match instr {
        IRInst::AssignVariable { variable, value }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } if *variable == element => value,
        _ => return None,
    };
    let IRExpr::Deref(address) = value else {
        return None;
    };
    let IRExpr::ElementAddress {
        base,
        index,
        element_size,
    } = address.as_ref()
    else {
        return None;
    };
    Some((base, index, *element_size))
}

/// Match a zero-terminated traversal whose only counter use is a wrapping
/// increment and the next element address. The caller checks that both local
/// variables have no uses outside this three-instruction sequence.
pub fn vector_iteration(
    counter_init: &IRInst,
    element_init: &IRInst,
    loop_instr: &IRInst,
    context: &Context,
) -> Option<VectorIteration> {
    let IRInst::DeclareAndAssignVariable {
        variable: counter,
        ty: VariableType::UnsignedInteger(index_bits),
        value: start_expr,
    } = counter_init
    else {
        return None;
    };
    if !matches!(index_bits, 8 | 16 | 32 | 64) {
        return None;
    }
    let start = unsigned_constant(start_expr)?;
    if *index_bits < 64 && start >= (1u64 << index_bits) {
        return None;
    }
    let IRInst::DeclareAndAssignVariable {
        variable: element,
        ty: element_type,
        value: IRExpr::Deref(initial_address),
    } = element_init
    else {
        return None;
    };
    let IRExpr::ElementAddress {
        base: vector,
        index: initial_index,
        element_size,
    } = initial_address.as_ref()
    else {
        return None;
    };
    if unsigned_constant(initial_index) != Some(start) {
        return None;
    }
    let valid_vector = match context.direct_type(vector) {
        Some(VariableType::Vector(vector_element)) => vector_element.as_ref() == element_type,
        Some(VariableType::CString) => *element_type == VariableType::Integer(8),
        _ => false,
    };
    if !valid_vector {
        return None;
    }
    let width = match element_type {
        VariableType::Integer(bits) | VariableType::UnsignedInteger(bits)
            if matches!(bits, 8 | 16 | 32 | 64) =>
        {
            bits / 8
        }
        _ => return None,
    };
    if *element_size != width {
        return None;
    }
    let IRInst::While {
        label: None,
        entry_offset,
        condition:
            LoopCondition::Before {
                offset: condition_offset,
                expression: check,
            },
        body,
    } = loop_instr
    else {
        return None;
    };
    let IRExpr::BinOp {
        kind: IRBinOpKind::Ne,
        lhs,
        rhs,
    } = check
    else {
        return None;
    };
    if !((lhs.as_ref() == &IRExpr::Variable(*element) && unsigned_constant(rhs) == Some(0))
        || (rhs.as_ref() == &IRExpr::Variable(*element) && unsigned_constant(lhs) == Some(0)))
    {
        return None;
    }
    let (load_offset, last) = body.last()?;
    let (next_vector, next_index, next_size) = load_from_index(last, *element)?;
    if next_vector != vector.as_ref() || next_size != width {
        return None;
    }
    let expected_index = if *index_bits == 64 {
        IRExpr::Variable(*counter)
    } else {
        IRExpr::Convert {
            value: Box::new(IRExpr::Variable(*counter)),
            source: crate::irt6::ir::IntegerType {
                size: index_bits / 8,
                signed: false,
            },
            target: crate::irt6::ir::IntegerType {
                size: 8,
                signed: false,
            },
        }
    };
    if next_index != &expected_index {
        return None;
    }
    let mut advance = None;
    let mut remaining = Vec::new();
    for (offset, instr) in &body[..body.len() - 1] {
        if increment_of(instr, *counter) {
            if advance.replace(*offset).is_some() {
                return None;
            }
            continue;
        }
        let mut effects = Effects::default();
        effects.instruction(instr);
        if effects.control
            || effects.memory_write
            || effects.unknown_write
            || effects.may_trap
            || effects.reads.contains(counter)
            || effects.writes.contains(counter)
            || effects.writes.contains(element)
        {
            return None;
        }
        if let IRExpr::Variable(vector_variable) = vector.as_ref()
            && effects.writes.contains(vector_variable)
        {
            return None;
        }
        remaining.push((*offset, instr.clone()));
    }
    Some(VectorIteration {
        counter: *counter,
        element: *element,
        replacement: IRInst::ForEach {
            entry_offset: *entry_offset,
            condition_offset: *condition_offset,
            advance_offset: advance?,
            load_offset: *load_offset,
            variable: *element,
            element_type: element_type.clone(),
            vector: vector.as_ref().clone(),
            start,
            index_bits: *index_bits,
            body: remaining,
        },
    })
}
