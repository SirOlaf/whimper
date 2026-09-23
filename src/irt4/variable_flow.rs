//! A tier 4 local view of slot operations and structured control flow.
//!
//! Each node reads its inputs before writing its destination. Dependencies
//! retain their base and displacement, so an address such as `slot + 0x24`
//! remains distinguishable from a plain read of `slot`.

use std::collections::HashSet;

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, LoopId, SyntheticFunction, VariableId,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Offset {
    pub base: VariableId,
    pub displacement: i128,
}

#[derive(Default)]
pub(super) struct Operation {
    pub dependencies: HashSet<Offset>,
    pub write: Option<VariableId>,
    pub offset: Option<Offset>,
    pub argument: Option<usize>,
}

impl Operation {
    pub fn reads(&self, variable: VariableId) -> bool {
        self.dependencies
            .iter()
            .any(|dependency| dependency.base == variable)
    }
}

pub(super) struct Node {
    pub operation: Operation,
    pub successors: Vec<usize>,
}

pub(super) struct Flow {
    pub nodes: Vec<Node>,
    pub entry: usize,
}

fn constant(expr: &IRExpr) -> Option<i128> {
    match expr {
        IRExpr::CU8(value) => Some(i128::from(*value)),
        IRExpr::CU32(value) => Some(i128::from(*value)),
        IRExpr::CU64(value) => Some(i128::from(*value)),
        _ => None,
    }
}

/// Recognize copies and base-plus-constant values without losing the offset.
/// The original expression remains in tier 4 for any eventual replacement.
fn offset(expr: &IRExpr) -> Option<Offset> {
    match expr {
        IRExpr::Variable(base) => Some(Offset {
            base: *base,
            displacement: 0,
        }),
        IRExpr::BinOp { kind, lhs, rhs } => match kind {
            IRBinOpKind::Add => {
                if let (Some(mut value), Some(delta)) = (offset(lhs), constant(rhs)) {
                    value.displacement = value.displacement.checked_add(delta)?;
                    Some(value)
                } else if let (Some(delta), Some(mut value)) = (constant(lhs), offset(rhs)) {
                    value.displacement = value.displacement.checked_add(delta)?;
                    Some(value)
                } else {
                    None
                }
            }
            IRBinOpKind::Sub => {
                let mut value = offset(lhs)?;
                value.displacement = value.displacement.checked_sub(constant(rhs)?)?;
                Some(value)
            }
            IRBinOpKind::Shl
            | IRBinOpKind::And
            | IRBinOpKind::Or
            | IRBinOpKind::Eq
            | IRBinOpKind::SignedGt
            | IRBinOpKind::Ne
            | IRBinOpKind::UnsignedLt
            | IRBinOpKind::UnsignedGe => None,
        },
        _ => None,
    }
}

fn reads(expr: &IRExpr, result: &mut HashSet<Offset>) {
    if let Some(dependency) = offset(expr) {
        result.insert(dependency);
        return;
    }
    match expr {
        IRExpr::BinOp { lhs, rhs, .. } => {
            reads(lhs, result);
            reads(rhs, result);
        }
        IRExpr::ReplaceBytes {
            original, value, ..
        } => {
            reads(original, result);
            reads(value, result);
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::Not(inner) => reads(inner, result),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn operation(instr: &IRInst) -> Operation {
    let mut op = Operation::default();
    match instr {
        IRInst::Assign { dest, src } => {
            reads(src, &mut op.dependencies);
            if let IRExpr::Variable(variable) = dest {
                op.write = Some(*variable);
                op.offset = offset(src);
                if let IRExpr::Argument(ordinal) = src {
                    op.argument = Some(*ordinal);
                }
            } else {
                reads(dest, &mut op.dependencies);
            }
        }
        IRInst::AssignVariable { variable, value }
        | IRInst::DeclareAndAssignVariable {
            variable, value, ..
        } => {
            reads(value, &mut op.dependencies);
            op.write = Some(*variable);
            op.offset = offset(value);
            if let IRExpr::Argument(ordinal) = value {
                op.argument = Some(*ordinal);
            }
        }
        IRInst::LoadVariable { variable, address } => {
            reads(address, &mut op.dependencies);
            op.write = Some(*variable);
        }
        IRInst::StoreVariable { address, variable } => {
            reads(address, &mut op.dependencies);
            op.dependencies.insert(Offset {
                base: *variable,
                displacement: 0,
            });
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => reads(value, &mut op.dependencies),
        IRInst::If { condition, .. } => reads(condition, &mut op.dependencies),
        IRInst::While { condition, .. } => match condition {
            LoopCondition::Before { expression, .. } | LoopCondition::After { expression, .. } => {
                reads(expression, &mut op.dependencies)
            }
        },
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                reads(argument, &mut op.dependencies);
            }
        }
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => {}
    }
    op
}

#[derive(Clone, Copy)]
struct LoopTargets {
    label: Option<LoopId>,
    break_to: usize,
    continue_to: usize,
}

struct Builder {
    nodes: Vec<Node>,
}

impl Builder {
    fn push(&mut self, operation: Operation, successors: Vec<usize>) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node {
            operation,
            successors,
        });
        id
    }

    fn sequence<'a>(
        &mut self,
        instructions: impl DoubleEndedIterator<Item = &'a IRInst>,
        mut next: usize,
        loops: &[LoopTargets],
    ) -> usize {
        for instr in instructions.rev() {
            next = self.instruction(instr, next, loops);
        }
        next
    }

    fn instruction(&mut self, instr: &IRInst, next: usize, loops: &[LoopTargets]) -> usize {
        match instr {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_entry = self.sequence(then_branch.iter(), next, loops);
                let else_entry = self.sequence(else_branch.iter(), next, loops);
                self.push(operation(instr), vec![then_entry, else_entry])
            }
            IRInst::While {
                label,
                condition,
                body,
                ..
            } => {
                let check = self.push(operation(instr), Vec::new());
                let (body_end, continue_to) = match condition {
                    LoopCondition::Before { .. } => (check, check),
                    LoopCondition::After { .. } => {
                        // A continue to a do-while loop skips its trailing check.
                        let start = self.push(Operation::default(), Vec::new());
                        (check, start)
                    }
                };
                let mut nested = loops.to_vec();
                nested.push(LoopTargets {
                    label: *label,
                    break_to: next,
                    continue_to,
                });
                let body_entry =
                    self.sequence(body.iter().map(|(_, instr)| instr), body_end, &nested);
                match condition {
                    LoopCondition::Before { .. } => {
                        self.nodes[check].successors = vec![body_entry, next];
                        check
                    }
                    LoopCondition::After { .. } => {
                        self.nodes[continue_to].successors = vec![body_entry];
                        self.nodes[check].successors = vec![continue_to, next];
                        continue_to
                    }
                }
            }
            IRInst::Break => self.push(
                operation(instr),
                loops
                    .last()
                    .map_or_else(Vec::new, |target| vec![target.break_to]),
            ),
            IRInst::Continue => self.push(
                operation(instr),
                loops
                    .last()
                    .map_or_else(Vec::new, |target| vec![target.continue_to]),
            ),
            IRInst::ContinueLoop(label) => self.push(
                operation(instr),
                loops
                    .iter()
                    .rev()
                    .find(|target| target.label == Some(*label))
                    .map_or_else(Vec::new, |target| vec![target.continue_to]),
            ),
            IRInst::Return(_) | IRInst::CallSynthetic { .. } | IRInst::Jump(_) | IRInst::End => {
                self.push(operation(instr), Vec::new())
            }
            _ => self.push(operation(instr), vec![next]),
        }
    }
}

impl Flow {
    pub fn from_function(function: &SyntheticFunction) -> Self {
        let mut builder = Builder { nodes: Vec::new() };
        let exit = builder.push(Operation::default(), Vec::new());
        let entry = builder.sequence(function.body.iter().map(|(_, instr)| instr), exit, &[]);
        Self {
            nodes: builder.nodes,
            entry,
        }
    }
}
