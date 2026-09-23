//! Shape recognizers consume the arithmetic IR, never rendered text.

use super::{
    arithmetic::{Context, Kind, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, VariableId},
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
