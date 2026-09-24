mod coalesce_loop_copies;
mod eliminate_aliases;
mod fold_constants;
mod inline_loop_conditions;
pub mod ir;
mod lift_return_branches;
mod place_declarations;
pub mod render;
mod simplify_binary_operations;
mod simplify_branches;
mod variable_flow;

use crate::irt3::ir as t3;
use std::collections::HashSet;

use self::ir::{
    DataId, DataVariable, IRBinOpKind, IRExpr, IRInst, LoopCondition, LoopId, Parameter, Program,
    SyntheticFunction, SyntheticFunctionId, VariableId, VariableType,
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
        t3::Parameter::Input { ordinal, size } => Parameter::Argument {
            ordinal: *ordinal,
            size: *size,
        },
        t3::Parameter::Value { variable, size } => Parameter::Slot {
            variable: variable_id(*variable),
            size: *size,
        },
        t3::Parameter::Native { ordinal, register } => Parameter::Argument {
            ordinal: *ordinal,
            size: register.size(),
        },
        t3::Parameter::Slot { variable, register } => Parameter::Slot {
            variable: variable_id(*variable),
            size: register.size(),
        },
    }
}

fn variable_type(ty: t3::VariableType) -> VariableType {
    match ty {
        t3::VariableType::Unknown(size) => VariableType::Unknown(size),
        t3::VariableType::Register(register) => VariableType::Unknown(Some(register.size())),
        t3::VariableType::Bool => VariableType::Bool,
    }
}

fn bin_op(kind: &t3::IRBinOpKind) -> IRBinOpKind {
    match kind {
        t3::IRBinOpKind::Add => IRBinOpKind::Add,
        t3::IRBinOpKind::Sub => IRBinOpKind::Sub,
        t3::IRBinOpKind::Mul => IRBinOpKind::Mul,
        t3::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t3::IRBinOpKind::Shr => IRBinOpKind::Shr,
        t3::IRBinOpKind::BitOr => IRBinOpKind::BitOr,
        t3::IRBinOpKind::And => IRBinOpKind::And,
        t3::IRBinOpKind::Or => IRBinOpKind::Or,
        t3::IRBinOpKind::Eq => IRBinOpKind::Eq,
        t3::IRBinOpKind::SignedGt => IRBinOpKind::SignedGt,
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
        t3::IRExpr::Convert {
            value,
            source,
            target,
        } => IRExpr::Convert {
            value: Box::new(expression(value)),
            source: self::ir::IntegerType {
                size: source.size,
                signed: source.signed,
            },
            target: self::ir::IntegerType {
                size: target.size,
                signed: target.signed,
            },
        },
        t3::IRExpr::CU8(value) => IRExpr::CU8(*value),
        t3::IRExpr::CU32(value) => IRExpr::CU32(*value),
        t3::IRExpr::CU64(value) => IRExpr::CU64(*value),
        t3::IRExpr::Variable(variable) => IRExpr::Variable(variable_id(*variable)),
        t3::IRExpr::Data(id) => IRExpr::Data(DataId { id: id.id }),
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

fn contains_loop(instr: &t3::IRInst) -> bool {
    match instr {
        t3::IRInst::Loop { .. } => true,
        t3::IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch.iter().chain(else_branch).any(contains_loop),
        _ => false,
    }
}

fn read_variables(expr: &t3::IRExpr, reads: &mut HashSet<t3::VariableId>) {
    match expr {
        t3::IRExpr::Variable(variable) => {
            reads.insert(*variable);
        }
        t3::IRExpr::BinOp { lhs, rhs, .. } => {
            read_variables(lhs, reads);
            read_variables(rhs, reads);
        }
        t3::IRExpr::Deref(inner)
        | t3::IRExpr::CastUnknownPtr { address: inner, .. }
        | t3::IRExpr::Convert { value: inner, .. }
        | t3::IRExpr::Not(inner) => read_variables(inner, reads),
        _ => {}
    }
}

fn instruction_reads(instr: &t3::IRInst, skip: &t3::IRInst, reads: &mut HashSet<t3::VariableId>) {
    if std::ptr::eq(instr, skip) {
        return;
    }
    match instr {
        t3::IRInst::Assign { dest, src } => {
            read_variables(src, reads);
            if !matches!(dest, t3::IRExpr::Variable(_)) {
                read_variables(dest, reads);
            }
        }
        t3::IRInst::AssignVariable { value, .. } => read_variables(value, reads),
        t3::IRInst::LoadVariable { address, .. } => read_variables(address, reads),
        t3::IRInst::StoreVariable { address, variable } => {
            read_variables(address, reads);
            reads.insert(*variable);
        }
        t3::IRInst::Return(Some(value)) | t3::IRInst::Jump(value) => read_variables(value, reads),
        t3::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            read_variables(condition, reads);
            for instr in then_branch.iter().chain(else_branch) {
                instruction_reads(instr, skip, reads);
            }
        }
        t3::IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                instruction_reads(instr, skip, reads);
            }
        }
        t3::IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                read_variables(argument, reads);
            }
        }
        _ => {}
    }
}

fn pure_expression(expr: &t3::IRExpr) -> bool {
    match expr {
        t3::IRExpr::Deref(_) | t3::IRExpr::Data(_) => false,
        t3::IRExpr::BinOp { lhs, rhs, .. } => pure_expression(lhs) && pure_expression(rhs),
        t3::IRExpr::CastUnknownPtr { address, .. }
        | t3::IRExpr::Convert { value: address, .. }
        | t3::IRExpr::Not(address) => pure_expression(address),
        _ => true,
    }
}

/// Repeat-edge assignments may also run on the final iteration when their
/// effects cannot escape the loop or change the trailing check.
fn movable_repeat_updates(
    function: &t3::SyntheticFunction,
    loop_instr: &t3::IRInst,
    condition: &IRExpr,
    updates: &[t3::IRInst],
) -> bool {
    let mut guard_reads = HashSet::new();
    fn ir_reads(expr: &IRExpr, reads: &mut HashSet<VariableId>) {
        match expr {
            IRExpr::Variable(variable) => {
                reads.insert(*variable);
            }
            IRExpr::BinOp { lhs, rhs, .. } => {
                ir_reads(lhs, reads);
                ir_reads(rhs, reads);
            }
            IRExpr::Deref(inner)
            | IRExpr::CastUnknownPtr { address: inner, .. }
            | IRExpr::Convert { value: inner, .. }
            | IRExpr::Not(inner) => ir_reads(inner, reads),
            _ => {}
        }
    }
    ir_reads(condition, &mut guard_reads);
    let mut outside_reads = HashSet::new();
    for (_, instr) in &function.body {
        instruction_reads(instr, loop_instr, &mut outside_reads);
    }
    updates.iter().all(|instr| {
        let (variable, value) = match instr {
            t3::IRInst::AssignVariable { variable, value } => (variable, value),
            t3::IRInst::Assign {
                dest: t3::IRExpr::Variable(variable),
                src,
            } => (variable, src),
            _ => return false,
        };
        !guard_reads.contains(&variable_id(*variable))
            && !outside_reads.contains(variable)
            && pure_expression(value)
    })
}

fn lift_branch(body: &[t3::IRInst], function: &t3::SyntheticFunction) -> Vec<IRInst> {
    body.iter()
        .flat_map(|instr| {
            instructions(0, instr, function)
                .into_iter()
                .map(|(_, instr)| instr)
        })
        .collect()
}

fn lift_body(
    body: &[(usize, t3::IRInst)],
    function: &t3::SyntheticFunction,
) -> Vec<(usize, IRInst)> {
    body.iter()
        .flat_map(|(offset, instr)| instructions(*offset, instr, function))
        .collect()
}

fn loop_instructions(
    label: Option<t3::LoopId>,
    entry_offset: usize,
    body: &[(usize, t3::IRInst)],
    function: &t3::SyntheticFunction,
    loop_instr: &t3::IRInst,
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
                .flat_map(|instr| instructions(offset, instr, function))
                .collect::<Vec<_>>();
            loop_body.extend(lift_body(&body[1..], function));
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
            let prefix = &body[..index];
            let rotatable = !prefix
                .iter()
                .any(|(_, instr)| declares_variable(instr) || contains_loop(instr));
            if index == body.len() - 1
                && (updates.is_empty()
                    || (!rotatable
                        && movable_repeat_updates(function, loop_instr, &expression, updates)))
            {
                let mut loop_body = lift_body(&body[..index], function);
                loop_body.extend(
                    lift_branch(updates, function)
                        .into_iter()
                        .map(|instr| (offset, instr)),
                );
                return vec![(
                    entry_offset,
                    IRInst::While {
                        label: label.map(loop_id),
                        entry_offset,
                        condition: LoopCondition::After { offset, expression },
                        body: loop_body,
                    },
                )];
            }

            // Rotation evaluates the original prefix once before the first
            // check, then after each repeating iteration. Do not copy nested
            // loops: that duplicates large regions of code and makes one
            // source loop appear as two loops in the rendered function.
            // Declarations stay in place because duplicating their scope
            // changes bindings.
            if rotatable {
                let mut result = lift_body(prefix, function);
                let mut loop_body = updates
                    .iter()
                    .flat_map(|instr| instructions(offset, instr, function))
                    .collect::<Vec<_>>();
                loop_body.extend(lift_body(&body[index + 1..], function));
                loop_body.extend(lift_body(prefix, function));
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
            body: lift_body(body, function),
        },
    )]
}

fn instructions(
    offset: usize,
    instr: &t3::IRInst,
    function: &t3::SyntheticFunction,
) -> Vec<(usize, IRInst)> {
    match instr {
        t3::IRInst::Loop {
            label,
            entry_offset,
            body,
        } => loop_instructions(*label, *entry_offset, body, function, instr),
        _ => vec![(offset, instruction(instr, function))],
    }
}

fn instruction(instr: &t3::IRInst, function: &t3::SyntheticFunction) -> IRInst {
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
            then_branch: lift_branch(then_branch, function),
            else_branch: lift_branch(else_branch, function),
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
        entry_address: source.entry_address,
        entry: source.entry.map(function_id),
        data: source
            .data
            .iter()
            .map(|item| DataVariable {
                id: DataId { id: item.id.id },
                address: item.address,
                name: item.name.clone(),
                ty: variable_type(item.ty),
            })
            .collect(),
        functions: source
            .functions
            .iter()
            .map(|function| SyntheticFunction {
                entry_offset: function.entry_offset,
                parameters: function.parameters.iter().map(parameter).collect(),
                body: function
                    .body
                    .iter()
                    .flat_map(|(offset, instr)| instructions(*offset, instr, function))
                    .collect(),
            })
            .collect(),
    };
    fold_constants::run(&mut program);
    for function in &mut program.functions {
        function.body = collapse_constant_branches(std::mem::take(&mut function.body));
    }
    fold_constants::run(&mut program);
    eliminate_aliases::run(&mut program);
    coalesce_loop_copies::run(&mut program);
    eliminate_aliases::run(&mut program);
    inline_loop_conditions::run(&mut program);
    simplify_binary_operations::run(&mut program);
    simplify_branches::run(&mut program);
    lift_return_branches::run(&mut program);
    place_declarations::run(&mut program);
    remove_unused_declarations(&mut program);
    prune_unused_entry_arguments(&mut program);
    program
}

fn remove_unused_declarations(program: &mut Program) {
    fn keep(instr: &mut IRInst, mentioned: &std::collections::HashSet<VariableId>) -> bool {
        match instr {
            IRInst::DeclareVariable { variable, .. } => mentioned.contains(variable),
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                then_branch.retain_mut(|instr| keep(instr, mentioned));
                else_branch.retain_mut(|instr| keep(instr, mentioned));
                true
            }
            IRInst::While { body, .. } => {
                body.retain_mut(|(_, instr)| keep(instr, mentioned));
                true
            }
            _ => true,
        }
    }
    for function in &mut program.functions {
        let flow = variable_flow::Flow::from_function(function);
        let mut mentioned = std::collections::HashSet::new();
        for node in &flow.nodes {
            if let Some(variable) = node.operation.write {
                mentioned.insert(variable);
            }
            for dependency in &node.operation.dependencies {
                mentioned.insert(dependency.base);
            }
        }
        function
            .body
            .retain_mut(|(_, instr)| keep(instr, &mentioned));
    }
}

fn expression_arguments(expr: &IRExpr, used: &mut std::collections::HashSet<usize>) {
    match expr {
        IRExpr::Argument(ordinal) => {
            used.insert(*ordinal);
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            expression_arguments(lhs, used);
            expression_arguments(rhs, used);
        }
        IRExpr::Deref(inner)
        | IRExpr::Not(inner)
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::CastUnknownPtr { address: inner, .. } => expression_arguments(inner, used),
        _ => {}
    }
}

fn instruction_arguments(
    instr: &IRInst,
    used: &mut std::collections::HashSet<usize>,
    called: &mut std::collections::HashSet<usize>,
) {
    match instr {
        IRInst::Assign { dest, src } => {
            expression_arguments(dest, used);
            expression_arguments(src, used);
        }
        IRInst::DeclareAndAssignVariable { value, .. } | IRInst::AssignVariable { value, .. } => {
            expression_arguments(value, used)
        }
        IRInst::LoadVariable { address, .. }
        | IRInst::StoreVariable { address, .. }
        | IRInst::Return(Some(address))
        | IRInst::Jump(address) => expression_arguments(address, used),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_arguments(condition, used);
            for instr in then_branch.iter().chain(else_branch) {
                instruction_arguments(instr, used, called);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            match condition {
                self::ir::LoopCondition::Before { expression, .. }
                | self::ir::LoopCondition::After { expression, .. } => {
                    expression_arguments(expression, used)
                }
            }
            for (_, instr) in body {
                instruction_arguments(instr, used, called);
            }
        }
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            called.insert(function.id);
            for argument in arguments {
                expression_arguments(argument, used);
            }
        }
        _ => {}
    }
}

fn prune_unused_entry_arguments(program: &mut Program) {
    let Some(entry) = program.entry else { return };
    let mut used = std::collections::HashSet::new();
    let mut called = std::collections::HashSet::new();
    for function in &program.functions {
        for (_, instr) in &function.body {
            instruction_arguments(instr, &mut used, &mut called);
        }
    }
    if called.contains(&entry.id) {
        return;
    }
    program.functions[entry.id]
        .parameters
        .retain(|parameter| match parameter {
            Parameter::Argument { ordinal, .. } => used.contains(ordinal),
            Parameter::Slot { .. } => true,
        });
}

fn collapse_constant_branches(body: Vec<(usize, IRInst)>) -> Vec<(usize, IRInst)> {
    let mut result = Vec::new();
    for (offset, instr) in body {
        match instr {
            IRInst::If {
                condition: IRExpr::Bool(value),
                then_branch,
                else_branch,
            } => {
                let selected = if value { then_branch } else { else_branch };
                result.extend(collapse_constant_branches(
                    selected
                        .into_iter()
                        .map(|instr| (offset, instr))
                        .collect::<Vec<_>>(),
                ));
            }
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_branch = collapse_constant_branches(
                    then_branch
                        .into_iter()
                        .map(|instr| (offset, instr))
                        .collect::<Vec<_>>(),
                )
                .into_iter()
                .map(|(_, instr)| instr)
                .collect();
                let else_branch = collapse_constant_branches(
                    else_branch
                        .into_iter()
                        .map(|instr| (offset, instr))
                        .collect::<Vec<_>>(),
                )
                .into_iter()
                .map(|(_, instr)| instr)
                .collect();
                result.push((
                    offset,
                    IRInst::If {
                        condition,
                        then_branch,
                        else_branch,
                    },
                ));
            }
            IRInst::While {
                label,
                entry_offset,
                condition,
                body,
            } => {
                result.push((
                    offset,
                    IRInst::While {
                        label,
                        entry_offset,
                        condition,
                        body: collapse_constant_branches(body),
                    },
                ));
            }
            other => result.push((offset, other)),
        }
    }
    result
}
