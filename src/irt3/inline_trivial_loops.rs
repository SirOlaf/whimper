//! Turn synthetic self-transfers into explicit loops.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRExpr, IRInst, Parameter, Program, SyntheticFunction, SyntheticFunctionId, VariableId,
    VariableType,
};

#[derive(Clone, Copy)]
struct LoopParameter {
    variable: VariableId,
    register: iced_x86::Register,
}

fn canonical_variable(
    variable: VariableId,
    aliases: &HashMap<VariableId, VariableId>,
) -> VariableId {
    let mut current = variable;
    let mut remaining = aliases.len();
    while let Some(next) = aliases.get(&current) {
        if *next == current || remaining == 0 {
            break;
        }
        current = *next;
        remaining -= 1;
    }
    current
}

fn add_alias(
    source: VariableId,
    target: VariableId,
    aliases: &mut HashMap<VariableId, VariableId>,
) {
    let source = canonical_variable(source, aliases);
    let target = canonical_variable(target, aliases);
    if source != target {
        aliases.insert(source, target);
    }
}

fn collect_register_slots(instr: &IRInst, slots: &mut HashMap<VariableId, iced_x86::Register>) {
    match instr {
        IRInst::DeclareVariable {
            variable,
            ty: VariableType::Register(register),
        } => {
            slots.insert(*variable, *register);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                collect_register_slots(instr, slots);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                collect_register_slots(instr, slots);
            }
        }
        _ => {}
    }
}

fn collect_merges(
    instr: &IRInst,
    function_id: SyntheticFunctionId,
    parameters: &[LoopParameter],
    register_slots: &HashMap<VariableId, iced_x86::Register>,
    aliases: &mut HashMap<VariableId, VariableId>,
) {
    match instr {
        IRInst::CallSynthetic {
            function,
            arguments,
        } if *function == function_id => {
            assert_eq!(arguments.len(), parameters.len());
            for (argument, parameter) in arguments.iter().zip(parameters) {
                if let IRExpr::Variable(variable) = argument
                    && register_slots.get(variable) == Some(&parameter.register)
                {
                    add_alias(*variable, parameter.variable, aliases);
                }
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                collect_merges(instr, function_id, parameters, register_slots, aliases);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                collect_merges(instr, function_id, parameters, register_slots, aliases);
            }
        }
        _ => {}
    }
}

fn rewrite_expression(
    expr: &mut IRExpr,
    aliases: &HashMap<VariableId, VariableId>,
    native_states: &HashMap<usize, VariableId>,
) {
    match expr {
        IRExpr::Variable(variable) => *variable = canonical_variable(*variable, aliases),
        IRExpr::Argument(ordinal) => {
            if let Some(variable) = native_states.get(ordinal) {
                *expr = IRExpr::Variable(*variable);
            }
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            rewrite_expression(lhs, aliases, native_states);
            rewrite_expression(rhs, aliases, native_states);
        }
        IRExpr::ReplaceBytes {
            original, value, ..
        } => {
            rewrite_expression(original, aliases, native_states);
            rewrite_expression(value, aliases, native_states);
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::Not(inner) => rewrite_expression(inner, aliases, native_states),
        IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_) | IRExpr::Bool(_) => {}
    }
}

fn rewrite_instruction(
    instr: &mut IRInst,
    aliases: &HashMap<VariableId, VariableId>,
    native_states: &HashMap<usize, VariableId>,
) {
    match instr {
        IRInst::Assign { dest, src } => {
            rewrite_expression(dest, aliases, native_states);
            rewrite_expression(src, aliases, native_states);
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => {
            rewrite_expression(value, aliases, native_states);
        }
        IRInst::DeclareVariable { variable, .. } => {
            *variable = canonical_variable(*variable, aliases);
        }
        IRInst::AssignVariable { variable, value } => {
            *variable = canonical_variable(*variable, aliases);
            rewrite_expression(value, aliases, native_states);
        }
        IRInst::LoadVariable { variable, address } => {
            *variable = canonical_variable(*variable, aliases);
            rewrite_expression(address, aliases, native_states);
        }
        IRInst::StoreVariable { address, variable } => {
            rewrite_expression(address, aliases, native_states);
            *variable = canonical_variable(*variable, aliases);
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            rewrite_expression(condition, aliases, native_states);
            for instr in then_branch.iter_mut().chain(else_branch) {
                rewrite_instruction(instr, aliases, native_states);
            }
        }
        IRInst::Loop { body, .. } => {
            for (_, instr) in body {
                rewrite_instruction(instr, aliases, native_states);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                rewrite_expression(argument, aliases, native_states);
            }
        }
        IRInst::Return(None)
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => {}
    }
}

fn fresh_variable(function_id: SyntheticFunctionId, next_variable: &mut usize) -> VariableId {
    let variable = VariableId {
        owner: function_id,
        id: *next_variable,
    };
    *next_variable += 1;
    variable
}

fn rewrite_self_calls(
    instr: IRInst,
    function_id: SyntheticFunctionId,
    parameters: &[LoopParameter],
    next_variable: &mut usize,
    declarations: &mut Vec<(VariableId, VariableType)>,
) -> Vec<IRInst> {
    match instr {
        IRInst::CallSynthetic {
            function,
            arguments,
        } if function == function_id => {
            assert_eq!(arguments.len(), parameters.len());
            let mut staged = Vec::new();
            let mut updates = Vec::new();
            for (argument, parameter) in arguments.into_iter().zip(parameters) {
                let argument = match argument {
                    IRExpr::Variable(variable) if variable == parameter.variable => continue,
                    argument => argument,
                };
                let temporary = fresh_variable(function_id, next_variable);
                declarations.push((
                    temporary,
                    VariableType::Unknown(Some(parameter.register.size())),
                ));
                staged.push(IRInst::AssignVariable {
                    variable: temporary,
                    value: argument,
                });
                updates.push(IRInst::AssignVariable {
                    variable: parameter.variable,
                    value: IRExpr::Variable(temporary),
                });
            }
            staged.extend(updates);
            staged.push(IRInst::Continue);
            staged
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => vec![IRInst::If {
            condition,
            then_branch: then_branch
                .into_iter()
                .flat_map(|instr| {
                    rewrite_self_calls(instr, function_id, parameters, next_variable, declarations)
                })
                .collect(),
            else_branch: else_branch
                .into_iter()
                .flat_map(|instr| {
                    rewrite_self_calls(instr, function_id, parameters, next_variable, declarations)
                })
                .collect(),
        }],
        IRInst::Loop {
            label,
            entry_offset,
            body,
        } => vec![IRInst::Loop {
            label,
            entry_offset,
            body: body
                .into_iter()
                .flat_map(|(offset, instr)| {
                    rewrite_self_calls(instr, function_id, parameters, next_variable, declarations)
                        .into_iter()
                        .map(move |instr| (offset, instr))
                })
                .collect(),
        }],
        instr => vec![instr],
    }
}

fn exit_call_count(instr: &IRInst) -> usize {
    match instr {
        IRInst::CallSynthetic { .. } => 1,
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .map(exit_call_count)
            .sum::<usize>()
            .min(2),
        // The input to this pass has no loops yet. Keep any future nested
        // loop transfers local instead of hoisting them past this loop.
        IRInst::Loop { .. } => 0,
        _ => 0,
    }
}

fn replace_exit_call(instr: &mut IRInst) -> Option<IRInst> {
    match instr {
        IRInst::CallSynthetic { .. } => match std::mem::replace(instr, IRInst::Break) {
            call @ IRInst::CallSynthetic { .. } => Some(call),
            _ => unreachable!(),
        },
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter_mut()
            .chain(else_branch)
            .find_map(replace_exit_call),
        IRInst::Loop { .. } => None,
        _ => None,
    }
}

fn hoist_single_exit_call(body: &mut [(usize, IRInst)]) -> Option<(usize, IRInst)> {
    let count = body
        .iter()
        .map(|(_, instr)| exit_call_count(instr))
        .sum::<usize>()
        .min(2);
    if count != 1 {
        return None;
    }

    body.iter_mut()
        .find_map(|(offset, instr)| replace_exit_call(instr).map(|call| (*offset, call)))
}

fn max_variable_id(function: &SyntheticFunction) -> Option<usize> {
    fn include(maximum: &mut Option<usize>, id: usize) {
        *maximum = Some(match *maximum {
            Some(found) => found.max(id),
            None => id,
        });
    }

    fn expression_max(expr: &IRExpr, maximum: &mut Option<usize>) {
        match expr {
            IRExpr::Variable(variable) => include(maximum, variable.id),
            IRExpr::BinOp { lhs, rhs, .. } => {
                expression_max(lhs, maximum);
                expression_max(rhs, maximum);
            }
            IRExpr::ReplaceBytes {
                original, value, ..
            } => {
                expression_max(original, maximum);
                expression_max(value, maximum);
            }
            IRExpr::Deref(inner)
            | IRExpr::CastUnknownPtr { address: inner, .. }
            | IRExpr::ExtractBytes { value: inner, .. }
            | IRExpr::ZeroExtend { value: inner, .. }
            | IRExpr::Not(inner) => expression_max(inner, maximum),
            IRExpr::Argument(_)
            | IRExpr::CU8(_)
            | IRExpr::CU32(_)
            | IRExpr::CU64(_)
            | IRExpr::Bool(_) => {}
        }
    }

    fn instruction_max(instr: &IRInst, maximum: &mut Option<usize>) {
        let variable = match instr {
            IRInst::AssignVariable { variable, .. }
            | IRInst::DeclareVariable { variable, .. }
            | IRInst::LoadVariable { variable, .. }
            | IRInst::StoreVariable { variable, .. } => Some(variable),
            _ => None,
        };
        if let Some(variable) = variable {
            include(maximum, variable.id);
        }
        match instr {
            IRInst::Assign { dest, src } => {
                expression_max(dest, maximum);
                expression_max(src, maximum);
            }
            IRInst::Return(Some(value)) | IRInst::Jump(value) => {
                expression_max(value, maximum);
            }
            IRInst::AssignVariable { value, .. } => expression_max(value, maximum),
            IRInst::LoadVariable { address, .. } => expression_max(address, maximum),
            IRInst::StoreVariable { address, .. } => expression_max(address, maximum),
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => {
                expression_max(condition, maximum);
                for instr in then_branch.iter().chain(else_branch) {
                    instruction_max(instr, maximum);
                }
            }
            IRInst::Loop { body, .. } => {
                for (_, instr) in body {
                    instruction_max(instr, maximum);
                }
            }
            IRInst::CallSynthetic { arguments, .. } => {
                for argument in arguments {
                    expression_max(argument, maximum);
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

    let mut maximum = None;
    for parameter in &function.parameters {
        if let Parameter::Slot { variable, .. } = parameter {
            include(&mut maximum, variable.id);
        }
    }
    for (_, instr) in &function.body {
        instruction_max(instr, &mut maximum);
    }
    maximum
}

fn lower_function(function: &mut SyntheticFunction, function_id: SyntheticFunctionId) {
    fn has_self_call(instr: &IRInst, function_id: SyntheticFunctionId) -> bool {
        match instr {
            IRInst::CallSynthetic { function, .. } => *function == function_id,
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => then_branch
                .iter()
                .chain(else_branch)
                .any(|instr| has_self_call(instr, function_id)),
            IRInst::Loop { body, .. } => body
                .iter()
                .any(|(_, instr)| has_self_call(instr, function_id)),
            _ => false,
        }
    }

    if !function
        .body
        .iter()
        .any(|(_, instr)| has_self_call(instr, function_id))
    {
        return;
    }

    let mut next_variable = max_variable_id(function).map_or(0, |id| id + 1);
    let mut parameters = Vec::with_capacity(function.parameters.len());
    let mut native_states = HashMap::new();
    let mut native_initial_values = Vec::new();
    for parameter in &function.parameters {
        match parameter {
            Parameter::Native { ordinal, register } => {
                let variable = fresh_variable(function_id, &mut next_variable);
                parameters.push(LoopParameter {
                    variable,
                    register: *register,
                });
                native_states.insert(*ordinal, variable);
                native_initial_values.push((variable, *ordinal, *register));
            }
            Parameter::Slot { variable, register } => parameters.push(LoopParameter {
                variable: *variable,
                register: *register,
            }),
        }
    }

    let mut register_slots = HashMap::new();
    for parameter in &function.parameters {
        if let Parameter::Slot { variable, register } = parameter {
            register_slots.insert(*variable, *register);
        }
    }
    for (_, instr) in &function.body {
        collect_register_slots(instr, &mut register_slots);
    }

    let mut aliases = HashMap::new();
    for (_, instr) in &function.body {
        collect_merges(
            instr,
            function_id,
            &parameters,
            &register_slots,
            &mut aliases,
        );
    }

    for (_, instr) in &mut function.body {
        rewrite_instruction(instr, &aliases, &native_states);
    }
    for parameter in &mut function.parameters {
        if let Parameter::Slot { variable, .. } = parameter {
            *variable = canonical_variable(*variable, &aliases);
        }
    }
    for parameter in &mut parameters {
        parameter.variable = canonical_variable(parameter.variable, &aliases);
    }
    for (variable, _, _) in &mut native_initial_values {
        *variable = canonical_variable(*variable, &aliases);
    }

    let mut temporary_declarations = Vec::new();
    let mut rewritten = Vec::with_capacity(function.body.len());
    for (offset, instr) in std::mem::take(&mut function.body) {
        for instr in rewrite_self_calls(
            instr,
            function_id,
            &parameters,
            &mut next_variable,
            &mut temporary_declarations,
        ) {
            rewritten.push((offset, instr));
        }
    }

    let loop_variables: HashSet<_> = parameters.iter().map(|param| param.variable).collect();
    let native_variables: HashSet<_> = native_initial_values
        .iter()
        .map(|(variable, _, _)| *variable)
        .collect();
    let mut declarations = Vec::new();
    let mut declared = HashSet::new();
    let mut loop_body = Vec::new();
    for (offset, instr) in rewritten {
        match instr {
            IRInst::DeclareVariable { variable, ty } => {
                if loop_variables.contains(&variable) || native_variables.contains(&variable) {
                    continue;
                }
                if declared.insert(variable) {
                    declarations.push((offset, IRInst::DeclareVariable { variable, ty }));
                }
            }
            instr => loop_body.push((offset, instr)),
        }
    }
    for (variable, _, register) in &native_initial_values {
        if declared.insert(*variable) {
            declarations.push((
                function.entry_offset,
                IRInst::DeclareVariable {
                    variable: *variable,
                    ty: VariableType::Register(*register),
                },
            ));
        }
    }
    for (variable, ty) in temporary_declarations {
        let variable = canonical_variable(variable, &aliases);
        if declared.insert(variable) {
            declarations.push((
                function.entry_offset,
                IRInst::DeclareVariable { variable, ty },
            ));
        }
    }

    let exit_call = hoist_single_exit_call(&mut loop_body);
    let mut body = declarations;
    for (variable, ordinal, _) in native_initial_values {
        body.push((
            function.entry_offset,
            IRInst::AssignVariable {
                variable,
                value: IRExpr::Argument(ordinal),
            },
        ));
    }
    body.push((
        function.entry_offset,
        IRInst::Loop {
            label: None,
            entry_offset: function.entry_offset,
            body: loop_body,
        },
    ));
    if let Some(exit_call) = exit_call {
        body.push(exit_call);
    }
    function.body = body;
}

pub fn tr(mut program: Program) -> Program {
    for (id, function) in program.functions.iter_mut().enumerate() {
        lower_function(function, SyntheticFunctionId { id });
    }
    program
}
