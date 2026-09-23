mod eliminate_aliases;
mod inline_loop_conditions;
pub mod ir;
pub mod render;
mod variable_flow;

use crate::irt3::ir as t3;

use self::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, LoopId, Parameter, Program, SyntheticFunction,
    SyntheticFunctionId, VariableId, VariableType,
};

fn function_id(id: t3::SyntheticFunctionId) -> SyntheticFunctionId {
    SyntheticFunctionId { id: id.id }
}

fn variable_id(id: t3::VariableId) -> VariableId {
    VariableId {
        owner: function_id(id.owner),
        id: id.id,
    }
}

fn loop_id(id: t3::LoopId) -> LoopId {
    LoopId { id: id.id }
}

fn parameter(parameter: &t3::Parameter) -> Parameter {
    match parameter {
        t3::Parameter::Native { ordinal, register } => Parameter::Native {
            ordinal: *ordinal,
            register: *register,
        },
        t3::Parameter::Slot { variable, register } => Parameter::Slot {
            variable: variable_id(*variable),
            register: *register,
        },
    }
}

fn variable_type(ty: t3::VariableType) -> VariableType {
    match ty {
        t3::VariableType::Unknown(size) => VariableType::Unknown(size),
        t3::VariableType::Register(register) => VariableType::Register(register),
        t3::VariableType::Bool => VariableType::Bool,
    }
}

fn bin_op(kind: &t3::IRBinOpKind) -> IRBinOpKind {
    match kind {
        t3::IRBinOpKind::Add => IRBinOpKind::Add,
        t3::IRBinOpKind::Sub => IRBinOpKind::Sub,
        t3::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t3::IRBinOpKind::And => IRBinOpKind::And,
        t3::IRBinOpKind::Or => IRBinOpKind::Or,
        t3::IRBinOpKind::Eq => IRBinOpKind::Eq,
        t3::IRBinOpKind::UnsignedLt => IRBinOpKind::UnsignedLt,
    }
}

fn expression(expr: &t3::IRExpr) -> IRExpr {
    match expr {
        t3::IRExpr::BinOp { kind, lhs, rhs } => IRExpr::BinOp {
            kind: bin_op(kind),
            lhs: Box::new(expression(lhs)),
            rhs: Box::new(expression(rhs)),
        },
        t3::IRExpr::Deref(address) => IRExpr::Deref(Box::new(expression(address))),
        t3::IRExpr::CastUnknownPtr { address, size } => IRExpr::CastUnknownPtr {
            address: Box::new(expression(address)),
            size: *size,
        },
        t3::IRExpr::Argument(ordinal) => IRExpr::Argument(*ordinal),
        t3::IRExpr::ExtractBytes {
            value,
            offset,
            size,
        } => IRExpr::ExtractBytes {
            value: Box::new(expression(value)),
            offset: *offset,
            size: *size,
        },
        t3::IRExpr::ZeroExtend { value, size } => IRExpr::ZeroExtend {
            value: Box::new(expression(value)),
            size: *size,
        },
        t3::IRExpr::ReplaceBytes {
            original,
            value,
            offset,
            size,
        } => IRExpr::ReplaceBytes {
            original: Box::new(expression(original)),
            value: Box::new(expression(value)),
            offset: *offset,
            size: *size,
        },
        t3::IRExpr::CU8(value) => IRExpr::CU8(*value),
        t3::IRExpr::CU32(value) => IRExpr::CU32(*value),
        t3::IRExpr::CU64(value) => IRExpr::CU64(*value),
        t3::IRExpr::Variable(variable) => IRExpr::Variable(variable_id(*variable)),
        t3::IRExpr::Bool(value) => IRExpr::Bool(*value),
        t3::IRExpr::Not(inner) => IRExpr::Not(Box::new(expression(inner))),
    }
}

fn negate(expr: IRExpr) -> IRExpr {
    match expr {
        IRExpr::Not(inner) => *inner,
        other => IRExpr::Not(Box::new(other)),
    }
}

/// Return the condition and work performed on the repeating branch when this
/// instruction is the loop's sole exit check.
fn repeat_guard(instr: &t3::IRInst) -> Option<(IRExpr, &[t3::IRInst])> {
    match instr {
        t3::IRInst::Break => Some((IRExpr::Bool(false), &[])),
        t3::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } if then_branch.len() == 1 && matches!(then_branch[0], t3::IRInst::Break) => {
            Some((negate(expression(condition)), else_branch))
        }
        t3::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } if else_branch.len() == 1 && matches!(else_branch[0], t3::IRInst::Break) => {
            Some((expression(condition), then_branch))
        }
        _ => None,
    }
}

/// Count exits from this loop. A break inside a nested loop belongs to that
/// nested loop, while a function exit inside it still exits this one.
fn exit_count(instr: &t3::IRInst, nested: bool) -> usize {
    match instr {
        t3::IRInst::Break => usize::from(!nested),
        t3::IRInst::Return(_)
        | t3::IRInst::Jump(_)
        | t3::IRInst::End
        | t3::IRInst::CallSynthetic { .. } => 1,
        t3::IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .map(|instr| exit_count(instr, nested))
            .sum(),
        t3::IRInst::Loop { body, .. } => {
            body.iter().map(|(_, instr)| exit_count(instr, true)).sum()
        }
        _ => 0,
    }
}

/// A continue to this loop skips the trailing condition of a do-while or the
/// rotated prefix, so keep its explicit break form.
fn continues_here(instr: &t3::IRInst, label: Option<t3::LoopId>, nested: bool) -> bool {
    match instr {
        t3::IRInst::Continue => !nested,
        t3::IRInst::ContinueLoop(target) => Some(*target) == label,
        t3::IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .any(|instr| continues_here(instr, label, nested)),
        t3::IRInst::Loop { body, .. } => body
            .iter()
            .any(|(_, instr)| continues_here(instr, label, true)),
        _ => false,
    }
}

fn declares_variable(instr: &t3::IRInst) -> bool {
    match instr {
        t3::IRInst::DeclareVariable { .. } => true,
        t3::IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch.iter().chain(else_branch).any(declares_variable),
        t3::IRInst::Loop { body, .. } => body.iter().any(|(_, instr)| declares_variable(instr)),
        _ => false,
    }
}

fn lift_branch(body: &[t3::IRInst]) -> Vec<IRInst> {
    body.iter()
        .flat_map(|instr| instructions(0, instr).into_iter().map(|(_, instr)| instr))
        .collect()
}

fn lift_body(body: &[(usize, t3::IRInst)]) -> Vec<(usize, IRInst)> {
    body.iter()
        .flat_map(|(offset, instr)| instructions(*offset, instr))
        .collect()
}

fn loop_instructions(
    label: Option<t3::LoopId>,
    entry_offset: usize,
    body: &[(usize, t3::IRInst)],
) -> Vec<(usize, IRInst)> {
    let single_exit = body
        .iter()
        .map(|(_, instr)| exit_count(instr, false))
        .sum::<usize>()
        == 1;
    let guard = single_exit
        .then(|| {
            body.iter()
                .enumerate()
                .find_map(|(index, (offset, instr))| {
                    repeat_guard(instr).and_then(|(expression, updates)| {
                        (!updates.iter().any(declares_variable))
                            .then_some((index, *offset, expression, updates))
                    })
                })
        })
        .flatten();
    let continues = body
        .iter()
        .any(|(_, instr)| continues_here(instr, label, false));

    if let Some((index, offset, expression, updates)) = guard {
        if index == 0 {
            let mut loop_body = updates
                .iter()
                .flat_map(|instr| instructions(offset, instr))
                .collect::<Vec<_>>();
            loop_body.extend(lift_body(&body[1..]));
            return vec![(
                entry_offset,
                IRInst::While {
                    label: label.map(loop_id),
                    entry_offset,
                    condition: LoopCondition::Before { offset, expression },
                    body: loop_body,
                },
            )];
        }

        if !continues {
            if index == body.len() - 1 && updates.is_empty() {
                return vec![(
                    entry_offset,
                    IRInst::While {
                        label: label.map(loop_id),
                        entry_offset,
                        condition: LoopCondition::After { offset, expression },
                        body: lift_body(&body[..index]),
                    },
                )];
            }

            // Rotation evaluates the original prefix once before the first
            // check, then after each repeating iteration. A declaration is
            // kept in place because duplicating its scope changes bindings.
            let prefix = &body[..index];
            if !prefix.iter().any(|(_, instr)| declares_variable(instr)) {
                let mut result = lift_body(prefix);
                let mut loop_body = updates
                    .iter()
                    .flat_map(|instr| instructions(offset, instr))
                    .collect::<Vec<_>>();
                loop_body.extend(lift_body(&body[index + 1..]));
                loop_body.extend(lift_body(prefix));
                result.push((
                    offset,
                    IRInst::While {
                        label: label.map(loop_id),
                        entry_offset: offset,
                        condition: LoopCondition::Before { offset, expression },
                        body: loop_body,
                    },
                ));
                return result;
            }
        }
    }

    vec![(
        entry_offset,
        IRInst::While {
            label: label.map(loop_id),
            entry_offset,
            condition: LoopCondition::Before {
                offset: entry_offset,
                expression: IRExpr::Bool(true),
            },
            body: lift_body(body),
        },
    )]
}

fn instructions(offset: usize, instr: &t3::IRInst) -> Vec<(usize, IRInst)> {
    match instr {
        t3::IRInst::Loop {
            label,
            entry_offset,
            body,
        } => loop_instructions(*label, *entry_offset, body),
        _ => vec![(offset, instruction(instr))],
    }
}

fn instruction(instr: &t3::IRInst) -> IRInst {
    match instr {
        t3::IRInst::Assign { dest, src } => IRInst::Assign {
            dest: expression(dest),
            src: expression(src),
        },
        t3::IRInst::Return(value) => IRInst::Return(value.as_ref().map(expression)),
        t3::IRInst::DeclareVariable { variable, ty } => IRInst::DeclareVariable {
            variable: variable_id(*variable),
            ty: variable_type(*ty),
        },
        t3::IRInst::AssignVariable { variable, value } => IRInst::AssignVariable {
            variable: variable_id(*variable),
            value: expression(value),
        },
        t3::IRInst::LoadVariable { variable, address } => IRInst::LoadVariable {
            variable: variable_id(*variable),
            address: expression(address),
        },
        t3::IRInst::StoreVariable { address, variable } => IRInst::StoreVariable {
            address: expression(address),
            variable: variable_id(*variable),
        },
        t3::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => IRInst::If {
            condition: expression(condition),
            then_branch: lift_branch(then_branch),
            else_branch: lift_branch(else_branch),
        },
        t3::IRInst::Loop { .. } => unreachable!("loops are lifted by instructions"),
        t3::IRInst::Break => IRInst::Break,
        t3::IRInst::Continue => IRInst::Continue,
        t3::IRInst::ContinueLoop(label) => IRInst::ContinueLoop(loop_id(*label)),
        t3::IRInst::CallSynthetic {
            function,
            arguments,
        } => IRInst::CallSynthetic {
            function: function_id(*function),
            arguments: arguments.iter().map(expression).collect(),
        },
        t3::IRInst::Jump(target) => IRInst::Jump(expression(target)),
        t3::IRInst::End => IRInst::End,
    }
}

pub fn lift(source: &t3::Program) -> Program {
    let mut program = Program {
        entry: source.entry.map(function_id),
        functions: source
            .functions
            .iter()
            .map(|function| SyntheticFunction {
                entry_offset: function.entry_offset,
                parameters: function.parameters.iter().map(parameter).collect(),
                body: function
                    .body
                    .iter()
                    .flat_map(|(offset, instr)| instructions(*offset, instr))
                    .collect(),
            })
            .collect(),
    };
    eliminate_aliases::run(&mut program);
    inline_loop_conditions::run(&mut program);
    program
}
