//! Shape recognizers consume the arithmetic IR, never rendered text.

use super::{
    arithmetic::{Context, Kind, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, VariableId, VariableType},
};

#[derive(Debug, Clone)]
pub struct SubtractionLoop {
    pub accumulator: VariableId,
    pub stride: Value,
    /// Keep the source expression for code generation; normalization is a proof
    /// tool and does not invent evaluation or memory access order.
    pub stride_source: IRExpr,
    pub bits: usize,
    pub blockers: Vec<&'static str>,
}

#[derive(Debug, Clone)]
pub struct LoopAnalysis {
    pub offset: usize,
    pub check: Value,
    pub updates: Vec<(VariableId, Value)>,
    pub subtraction: Option<SubtractionLoop>,
}

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

#[derive(Debug, Clone)]
pub struct GuardedModulo {
    pub destination: IRExpr,
    pub dividend: IRExpr,
    pub replacement: IRInst,
}

#[derive(Debug, Clone)]
pub struct VectorIteration {
    pub counter: VariableId,
    pub element: VariableId,
    pub replacement: IRInst,
}

fn unsigned_constant(expr: &IRExpr) -> Option<u64> {
    match expr {
        IRExpr::CU8(value) => Some(*value as u64),
        IRExpr::CU32(value) => Some(*value as u64),
        IRExpr::CU64(value) => Some(*value),
        _ => None,
    }
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
    let Some(VariableType::Vector(vector_element)) = context.direct_type(vector) else {
        return None;
    };
    if vector_element.as_ref() != element_type {
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
            source: super::ir::IntegerType {
                size: index_bits / 8,
                signed: false,
            },
            target: super::ir::IntegerType {
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

pub(super) fn assignment(instr: &IRInst) -> Option<(VariableId, &IRExpr)> {
    match instr {
        IRInst::AssignVariable { variable, value }
        | IRInst::DeclareAndAssignVariable {
            variable, value, ..
        }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } => Some((*variable, value)),
        _ => None,
    }
}

pub fn analyze(instr: &IRInst, context: &Context) -> Option<LoopAnalysis> {
    let IRInst::While {
        entry_offset,
        label,
        condition,
        body,
    } = instr
    else {
        return None;
    };
    let (LoopCondition::Before { expression, .. } | LoopCondition::After { expression, .. }) =
        condition;
    let check = context.value(expression);
    let updates = body
        .iter()
        .filter_map(|(_, instr)| assignment(instr))
        .map(|(variable, value)| (variable, context.value(value)))
        .collect::<Vec<_>>();
    let mut analysis = LoopAnalysis {
        offset: *entry_offset,
        check,
        updates,
        subtraction: None,
    };
    let Kind::Binary {
        kind: IRBinOpKind::UnsignedGe,
        lhs,
        rhs,
    } = &analysis.check.kind
    else {
        return Some(analysis);
    };
    let Kind::Atom(IRExpr::Variable(accumulator)) = &lhs.kind else {
        return Some(analysis);
    };
    let Some(expected_update) = lhs.subtract(rhs) else {
        return Some(analysis);
    };
    if !analysis
        .updates
        .iter()
        .any(|(variable, value)| variable == accumulator && *value == expected_update)
    {
        return Some(analysis);
    }
    // Negation normalization preserves the operands, so the original right
    // operand is the expression whose evaluation the replacement must retain.
    let mut source = expression;
    while let IRExpr::Not(inner) = source {
        source = inner;
    }
    let IRExpr::BinOp {
        rhs: stride_source, ..
    } = source
    else {
        return Some(analysis);
    };
    let mut blockers = Vec::new();
    if matches!(condition, LoopCondition::After { .. }) {
        blockers.push("entry condition has not been proved; guarded loop rotation required");
    }
    if label.is_some() {
        blockers.push("loop has a control-flow label");
    }
    if rhs.reads(*accumulator) {
        blockers.push("stride depends on the accumulator");
    }
    if !repeatable(stride_source) {
        blockers.push("stride evaluation can read memory or trap");
    }
    let mut effects = Effects::default();
    for (_, instr) in body {
        effects.instruction(instr);
    }
    if effects.writes.iter().any(|variable| rhs.reads(*variable)) {
        blockers.push("stride changes within the loop");
    }
    if effects.memory_read {
        blockers.push("loop reloads memory; no memory independence proof");
    }
    if effects.memory_write {
        blockers.push("loop stores intermediate results");
    }
    if effects.control {
        blockers.push("loop contains additional control flow");
    }
    if effects.may_trap {
        blockers.push("loop contains a potentially trapping operation");
    }
    if body.len() != 1 {
        blockers.push("loop contains additional operations");
    }
    if matches!(
        body.first().map(|(_, instr)| instr),
        Some(IRInst::DeclareAndAssignVariable { .. })
    ) {
        blockers.push("update declares a binding inside the loop");
    }
    if rhs.kind == Kind::Constant(0) {
        blockers.push("stride is zero; loop does not terminate");
    }
    analysis.subtraction = Some(SubtractionLoop {
        accumulator: *accumulator,
        stride: rhs.as_ref().clone(),
        stride_source: stride_source.as_ref().clone(),
        bits: lhs.bits.unwrap(),
        blockers,
    });
    Some(analysis)
}
