use super::super::{
    arithmetic::{Bindings, Context, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition},
    shapes,
};
use super::{Options, facts::Facts};

pub(super) struct Rule {
    pub(super) name: &'static str,
    pub(super) apply: fn(&mut IRInst, usize, &Context, &Facts, &Options) -> Option<usize>,
}

pub(super) const RULES: &[Rule] = &[
    Rule {
        name: "cstring-empty-check",
        apply: recover_cstring_empty_check,
    },
    Rule {
        name: "boolean-branch-to-return",
        apply: recover_boolean_return,
    },
    Rule {
        name: "guarded-do-to-while",
        apply: rotate_guarded_loop,
    },
    Rule {
        name: "repeated-subtraction-to-remainder",
        apply: recover_remainder,
    },
    Rule {
        name: "eliminate-guarded-modulo",
        apply: eliminate_guarded_modulo,
    },
    Rule {
        name: "compound-assignment",
        apply: recover_compound_assignment,
    },
    Rule {
        name: "de-morgan",
        apply: simplify_boolean_chains,
    },
];

fn simplify_boolean_expression(expr: &mut IRExpr) -> bool {
    let mut changed = match expr {
        IRExpr::BinOp { lhs, rhs, .. }
        | IRExpr::ElementAddress {
            base: lhs,
            index: rhs,
            ..
        } => {
            let left_changed = simplify_boolean_expression(lhs);
            let right_changed = simplify_boolean_expression(rhs);
            left_changed || right_changed
        }
        IRExpr::Deref(inner)
        | IRExpr::CStringLength(inner)
        | IRExpr::MemoryAddress { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => simplify_boolean_expression(inner),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Data(_)
        | IRExpr::Bool(_) => false,
    };
    if let Some(replacement) = shapes::de_morgan(expr) {
        *expr = replacement;
        changed = true;
    }
    changed
}

fn simplify_boolean_chains(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let changed = match instr {
        IRInst::Assign { dest, src } => {
            let dest_changed = simplify_boolean_expression(dest);
            let src_changed = simplify_boolean_expression(src);
            dest_changed || src_changed
        }
        IRInst::CompoundAssign { dest, value, .. } => {
            let dest_changed = simplify_boolean_expression(dest);
            let value_changed = simplify_boolean_expression(value);
            dest_changed || value_changed
        }
        IRInst::Return(Some(value))
        | IRInst::DeclareAndAssignVariable { value, .. }
        | IRInst::AssignVariable { value, .. }
        | IRInst::Jump(value)
        | IRInst::LoadVariable { address: value, .. }
        | IRInst::StoreVariable { address: value, .. } => simplify_boolean_expression(value),
        IRInst::If { condition, .. } => simplify_boolean_expression(condition),
        IRInst::While { condition, .. } => {
            let (LoopCondition::Before { expression, .. }
            | LoopCondition::After { expression, .. }) = condition;
            simplify_boolean_expression(expression)
        }
        IRInst::ForEach { vector, .. } => simplify_boolean_expression(vector),
        IRInst::CallSynthetic { arguments, .. } => {
            arguments.iter_mut().fold(false, |changed, argument| {
                simplify_boolean_expression(argument) || changed
            })
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => false,
    };
    changed.then_some(offset)
}

fn recover_boolean_return(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let value = shapes::boolean_return(instr)?;
    *instr = IRInst::Return(Some(value));
    Some(offset)
}

fn recover_cstring_empty_check(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let IRInst::If { condition, .. } = instr else {
        return None;
    };
    *condition = shapes::cstring_empty_check(condition, &facts.loaded_from, context)?;
    Some(offset)
}

fn eliminate_guarded_modulo(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let shape = shapes::guarded_modulo(instr, context)?;
    if !facts.destination_contains(&shape.destination, &shape.dividend) {
        return None;
    }
    // On the skipped path dividend < stride, so the stride is nonzero and
    // dividend % stride is dividend. The destination already holds it.
    *instr = shape.replacement;
    Some(offset)
}

fn recover_compound_assignment(
    instr: &mut IRInst,
    offset: usize,
    _context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
    let shape = shapes::compound_assignment(instr)?;
    *instr = IRInst::CompoundAssign {
        dest: shape.dest,
        kind: shape.kind,
        value: shape.value,
    };
    Some(offset)
}

fn rotate_guarded_loop(
    instr: &mut IRInst,
    _offset: usize,
    context: &Context,
    _facts: &Facts,
    _options: &Options,
) -> Option<usize> {
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
    fn branch(branch: &mut [IRInst], guard: &Value, context: &Context) -> Option<usize> {
        let mut bindings = Bindings::new();
        for instr in branch {
            match instr {
                // Only a prefix of fresh local declarations may separate the
                // guard from the loop. Capture their values at the declaration.
                IRInst::DeclareAndAssignVariable {
                    variable, value, ..
                } if repeatable(value) => {
                    if guard.reads(*variable)
                        || bindings.values().any(|value| value.reads(*variable))
                    {
                        return None;
                    }
                    let value = context.with_bindings(value, &bindings);
                    let destination = context.value(&IRExpr::Variable(*variable));
                    if destination.bits != value.bits {
                        return None;
                    }
                    bindings.insert(*variable, value);
                }
                IRInst::While {
                    label: None,
                    condition,
                    body,
                    entry_offset,
                } => {
                    let LoopCondition::After { offset, expression } = condition else {
                        return None;
                    };
                    if !repeatable(expression)
                        || context.with_bindings(expression, &bindings) != *guard
                    {
                        return None;
                    }
                    // Continue in earlier tiers can bypass a trailing check.
                    // Nested control flow requires a separate rotation proof.
                    let mut effects = Effects::default();
                    for (_, instr) in body {
                        effects.instruction(instr);
                    }
                    if effects.control {
                        return None;
                    }
                    *condition = LoopCondition::Before {
                        offset: *offset,
                        expression: expression.clone(),
                    };
                    return Some(*entry_offset);
                }
                _ => return None,
            }
        }
        None
    }
    let guard = context.value(condition);
    branch(then_branch, &guard, context).or_else(|| branch(else_branch, &guard.negated(), context))
}

fn recover_remainder(
    instr: &mut IRInst,
    _offset: usize,
    context: &Context,
    facts: &Facts,
    options: &Options,
) -> Option<usize> {
    let analysis = shapes::analyze(instr, context)?;
    let shape = analysis.subtraction?;
    if !shape.blockers.is_empty() {
        return None;
    }
    match facts.is_zero(&shape.stride) {
        Some(true) => return None,
        None if !options.allow_assumptions => return None,
        _ => {}
    }
    // A zero stride makes this matched loop nonterminating. Recover the
    // operation for terminating executions, where the stride is nonzero.
    *instr = IRInst::AssignVariable {
        variable: shape.accumulator,
        value: IRExpr::BinOp {
            kind: IRBinOpKind::UnsignedMod,
            lhs: Box::new(IRExpr::Variable(shape.accumulator)),
            rhs: Box::new(shape.stride_source),
        },
    };
    Some(analysis.offset)
}
