//! A single read-only walk for shape analyses that inspect nested Tier 6 IR.

use super::super::{
    arithmetic::Context,
    ir::{IRExpr, IRInst, LoopCondition, Program},
};

/// Implement either callback to inspect every node. Callbacks run before the
/// node's children, in source order. The offset is the closest recorded source
/// offset; branches without their own offset inherit their parent's offset.
pub trait Analyzer {
    fn instruction(&mut self, _instr: &IRInst, _offset: usize, _context: &Context) {}
    fn expression(&mut self, _expr: &IRExpr, _offset: usize, _context: &Context) {}
}

/// Register independent analyzers here without duplicating the AST walk.
pub fn walk(program: &Program, analyzers: &mut [&mut dyn Analyzer]) {
    for function in &program.functions {
        let context = Context::from_function(function);
        for (offset, instr) in &function.body {
            instruction(instr, *offset, &context, analyzers);
        }
    }
}

fn expression(
    expr: &IRExpr,
    offset: usize,
    context: &Context,
    analyzers: &mut [&mut dyn Analyzer],
) {
    for analyzer in analyzers.iter_mut() {
        analyzer.expression(expr, offset, context);
    }
    match expr {
        IRExpr::BinOp { lhs, rhs, .. }
        | IRExpr::ElementAddress {
            base: lhs,
            index: rhs,
            ..
        } => {
            expression(lhs, offset, context, analyzers);
            expression(rhs, offset, context, analyzers);
        }
        IRExpr::Deref(inner)
        | IRExpr::MemoryAddress { address: inner, .. }
        | IRExpr::CStringLength(inner)
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => expression(inner, offset, context, analyzers),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn instruction(
    instr: &IRInst,
    offset: usize,
    context: &Context,
    analyzers: &mut [&mut dyn Analyzer],
) {
    for analyzer in analyzers.iter_mut() {
        analyzer.instruction(instr, offset, context);
    }
    match instr {
        IRInst::Assign { dest, src } => {
            expression(dest, offset, context, analyzers);
            expression(src, offset, context, analyzers);
        }
        IRInst::CompoundAssign { dest, value, .. } => {
            expression(dest, offset, context, analyzers);
            expression(value, offset, context, analyzers);
        }
        IRInst::Return(Some(value))
        | IRInst::DeclareAndAssignVariable { value, .. }
        | IRInst::AssignVariable { value, .. }
        | IRInst::Jump(value) => expression(value, offset, context, analyzers),
        IRInst::LoadVariable { address, .. } | IRInst::StoreVariable { address, .. } => {
            expression(address, offset, context, analyzers);
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression(condition, offset, context, analyzers);
            for child in then_branch.iter().chain(else_branch) {
                instruction(child, offset, context, analyzers);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            let (LoopCondition::Before {
                offset,
                expression: check,
            }
            | LoopCondition::After {
                offset,
                expression: check,
            }) = condition;
            expression(check, *offset, context, analyzers);
            for (offset, child) in body {
                instruction(child, *offset, context, analyzers);
            }
        }
        IRInst::ForEach { vector, body, .. } => {
            expression(vector, offset, context, analyzers);
            for (offset, child) in body {
                instruction(child, *offset, context, analyzers);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                expression(argument, offset, context, analyzers);
            }
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => {}
    }
}
