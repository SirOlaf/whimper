//! Coalesce a loop's entry copy with its carried slot when the two values
//! cannot be observed independently.

use std::collections::HashMap;

use super::ir::{
    IRExpr, IRInst, LoopCondition, Parameter, Program, SyntheticFunction, VariableId, VariableType,
};

fn expression_reads(expr: &IRExpr, variable: VariableId) -> usize {
    match expr {
        IRExpr::Variable(found) => usize::from(*found == variable),
        IRExpr::BinOp { lhs, rhs, .. } => {
            expression_reads(lhs, variable) + expression_reads(rhs, variable)
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => expression_reads(inner, variable),
        _ => 0,
    }
}

fn reads(instr: &IRInst, variable: VariableId, skip: Option<*const IRInst>) -> usize {
    if skip == Some(instr as *const IRInst) {
        return 0;
    }
    match instr {
        IRInst::Assign { dest, src } => {
            expression_reads(src, variable)
                + if matches!(dest, IRExpr::Variable(_)) {
                    0
                } else {
                    expression_reads(dest, variable)
                }
        }
        IRInst::AssignVariable { value, .. } | IRInst::DeclareAndAssignVariable { value, .. } => {
            expression_reads(value, variable)
        }
        IRInst::LoadVariable { address, .. } => expression_reads(address, variable),
        IRInst::StoreVariable {
            address,
            variable: read,
        } => expression_reads(address, variable) + usize::from(*read == variable),
        IRInst::Return(Some(value)) | IRInst::Jump(value) => expression_reads(value, variable),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_reads(condition, variable)
                + then_branch
                    .iter()
                    .chain(else_branch)
                    .map(|instr| reads(instr, variable, skip))
                    .sum::<usize>()
        }
        IRInst::While {
            condition, body, ..
        } => {
            let expression = match condition {
                LoopCondition::Before { expression, .. }
                | LoopCondition::After { expression, .. } => expression,
            };
            expression_reads(expression, variable)
                + body
                    .iter()
                    .map(|(_, instr)| reads(instr, variable, skip))
                    .sum::<usize>()
        }
        IRInst::CallSynthetic { arguments, .. } => arguments
            .iter()
            .map(|argument| expression_reads(argument, variable))
            .sum(),
        _ => 0,
    }
}

fn written(instr: &IRInst, variable: VariableId) -> usize {
    match instr {
        IRInst::Assign {
            dest: IRExpr::Variable(dest),
            ..
        }
        | IRInst::AssignVariable { variable: dest, .. }
        | IRInst::DeclareAndAssignVariable { variable: dest, .. }
        | IRInst::LoadVariable { variable: dest, .. } => usize::from(*dest == variable),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .map(|instr| written(instr, variable))
            .sum(),
        IRInst::While { body, .. } => body.iter().map(|(_, instr)| written(instr, variable)).sum(),
        _ => 0,
    }
}

fn assigned(instr: &IRInst) -> Option<(VariableId, &IRExpr)> {
    match instr {
        IRInst::Assign {
            dest: IRExpr::Variable(dest),
            src,
        }
        | IRInst::AssignVariable {
            variable: dest,
            value: src,
        } => Some((*dest, src)),
        _ => None,
    }
}

fn continues_here(instr: &IRInst, nested: bool) -> bool {
    match instr {
        IRInst::Continue => !nested,
        // A labeled continue may leave this loop and skip its carried-slot
        // update even when it targets a different enclosing loop.
        IRInst::ContinueLoop(_) => true,
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .any(|instr| continues_here(instr, nested)),
        IRInst::While { body, .. } => body.iter().any(|(_, instr)| continues_here(instr, true)),
        _ => false,
    }
}

fn types(function: &SyntheticFunction) -> HashMap<VariableId, VariableType> {
    fn collect(instr: &IRInst, result: &mut HashMap<VariableId, VariableType>) {
        match instr {
            IRInst::DeclareVariable { variable, ty }
            | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
                result.insert(*variable, *ty);
            }
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                for instr in then_branch.iter().chain(else_branch) {
                    collect(instr, result);
                }
            }
            IRInst::While { body, .. } => {
                for (_, instr) in body {
                    collect(instr, result);
                }
            }
            _ => {}
        }
    }
    let mut result = HashMap::new();
    for parameter in &function.parameters {
        if let Parameter::Slot { variable, size } = parameter {
            result.insert(*variable, VariableType::Unknown(Some(*size)));
        }
    }
    for (_, instr) in &function.body {
        collect(instr, &mut result);
    }
    result
}

#[derive(Clone, Copy)]
struct Candidate {
    source: VariableId,
    target: VariableId,
    entry_offset: usize,
}

fn find_in_loop(
    function: &SyntheticFunction,
    loop_instr: &IRInst,
    types: &HashMap<VariableId, VariableType>,
) -> Option<Candidate> {
    let IRInst::While {
        entry_offset,
        condition,
        body,
        ..
    } = loop_instr
    else {
        return None;
    };
    if body.iter().any(|(_, instr)| continues_here(instr, false)) {
        return None;
    }
    let check = match condition {
        LoopCondition::Before { expression, .. } | LoopCondition::After { expression, .. } => {
            expression
        }
    };
    for (header, (_, instr)) in body.iter().enumerate() {
        let Some((target, value)) = assigned(instr) else {
            break;
        };
        let IRExpr::Variable(source) = value else {
            continue;
        };
        let ty = types.get(source);
        if target == *source
            || types.get(&target) != ty
            || !matches!(
                ty,
                Some(VariableType::Unknown(Some(_)) | VariableType::Bool)
            )
        {
            continue;
        }
        if body[..header]
            .iter()
            .any(|(_, instr)| reads(instr, target, None) != 0 || written(instr, target) != 0)
        {
            continue;
        }
        let outside = |variable| {
            function
                .body
                .iter()
                .map(|(_, instr)| reads(instr, variable, Some(loop_instr as *const IRInst)))
                .sum::<usize>()
        };
        if outside(target) != 0 || outside(*source) != 0 || reads(loop_instr, *source, None) != 1 {
            continue;
        }
        let writes = body
            .iter()
            .enumerate()
            .filter(|(_, (_, instr))| written(instr, *source) != 0)
            .collect::<Vec<_>>();
        let [(tail, (_, tail_instr))] = writes.as_slice() else {
            continue;
        };
        let Some((dest, value)) = assigned(tail_instr) else {
            continue;
        };
        if dest != *source
            || *tail <= header
            || body[*tail + 1..]
                .iter()
                .any(|(_, instr)| reads(instr, target, None) != 0 || written(instr, target) != 0)
        {
            continue;
        }
        if expression_reads(check, target) != 0
            && (!matches!(condition, LoopCondition::After { .. })
                || *value != IRExpr::Variable(target))
        {
            continue;
        }
        return Some(Candidate {
            source: *source,
            target,
            entry_offset: *entry_offset,
        });
    }
    None
}

fn find(
    function: &SyntheticFunction,
    instr: &IRInst,
    types: &HashMap<VariableId, VariableType>,
) -> Option<Candidate> {
    if let Some(candidate) = find_in_loop(function, instr, types) {
        return Some(candidate);
    }
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .find_map(|instr| find(function, instr, types)),
        IRInst::While { body, .. } => body
            .iter()
            .find_map(|(_, instr)| find(function, instr, types)),
        _ => None,
    }
}

fn replace_expr(expr: &mut IRExpr, target: VariableId, source: VariableId) {
    match expr {
        IRExpr::Variable(variable) if *variable == target => *variable = source,
        IRExpr::BinOp { lhs, rhs, .. } => {
            replace_expr(lhs, target, source);
            replace_expr(rhs, target, source);
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => replace_expr(inner, target, source),
        _ => {}
    }
}

fn replace(instr: &mut IRInst, target: VariableId, source: VariableId) {
    match instr {
        IRInst::Assign { dest, src } => {
            replace_expr(dest, target, source);
            replace_expr(src, target, source);
        }
        IRInst::AssignVariable { variable, value } => {
            if *variable == target {
                *variable = source;
            }
            replace_expr(value, target, source);
        }
        IRInst::DeclareAndAssignVariable {
            variable, value, ..
        } => {
            replace_expr(value, target, source);
            if *variable == target {
                *instr = IRInst::AssignVariable {
                    variable: source,
                    value: value.clone(),
                };
            }
        }
        IRInst::LoadVariable { variable, address } => {
            if *variable == target {
                *variable = source;
            }
            replace_expr(address, target, source);
        }
        IRInst::StoreVariable { address, variable } => {
            replace_expr(address, target, source);
            if *variable == target {
                *variable = source;
            }
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => replace_expr(value, target, source),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            replace_expr(condition, target, source);
            for instr in then_branch.iter_mut().chain(else_branch) {
                replace(instr, target, source);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            let expression = match condition {
                LoopCondition::Before { expression, .. }
                | LoopCondition::After { expression, .. } => expression,
            };
            replace_expr(expression, target, source);
            for (_, instr) in body {
                replace(instr, target, source);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                replace_expr(argument, target, source);
            }
        }
        _ => {}
    }
}

fn self_copy(instr: &IRInst) -> bool {
    matches!(assigned(instr), Some((dest, IRExpr::Variable(source))) if dest == *source)
}

fn remove_self_copies(instr: &mut IRInst) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            then_branch.retain(|instr| !self_copy(instr));
            else_branch.retain(|instr| !self_copy(instr));
            for instr in then_branch.iter_mut().chain(else_branch) {
                remove_self_copies(instr);
            }
        }
        IRInst::While { body, .. } => {
            body.retain(|(_, instr)| !self_copy(instr));
            for (_, instr) in body {
                remove_self_copies(instr);
            }
        }
        _ => {}
    }
}

fn apply(instr: &mut IRInst, candidate: Candidate) -> bool {
    match instr {
        IRInst::While {
            entry_offset, body, ..
        } if *entry_offset == candidate.entry_offset
            && body.iter().any(|(_, instr)| {
                matches!(assigned(instr), Some((target, IRExpr::Variable(source)))
                    if target == candidate.target && *source == candidate.source)
            }) =>
        {
            let header = body
                .iter()
                .position(|(_, instr)| {
                    matches!(assigned(instr), Some((target, IRExpr::Variable(source)))
                        if target == candidate.target && *source == candidate.source)
                })
                .unwrap();
            body.remove(header);
            replace(instr, candidate.target, candidate.source);
            remove_self_copies(instr);
            true
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter_mut()
            .chain(else_branch)
            .any(|instr| apply(instr, candidate)),
        IRInst::While { body, .. } => body.iter_mut().any(|(_, instr)| apply(instr, candidate)),
        _ => false,
    }
}

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        loop {
            let declared = types(function);
            let candidate = function
                .body
                .iter()
                .find_map(|(_, instr)| find(function, instr, &declared));
            let Some(candidate) = candidate else { break };
            if !function
                .body
                .iter_mut()
                .any(|(_, instr)| apply(instr, candidate))
            {
                break;
            }
        }
    }
}
