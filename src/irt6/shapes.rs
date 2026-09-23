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
