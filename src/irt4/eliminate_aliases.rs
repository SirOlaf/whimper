//! Remove slot copies when the control-flow graph proves their source stable.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRExpr, IRInst, LoopCondition, Parameter, Program, SyntheticFunction, VariableId, VariableType,
};
use super::variable_flow::Flow;

fn declarations(instr: &IRInst, types: &mut HashMap<VariableId, VariableType>) {
    match instr {
        IRInst::DeclareVariable { variable, ty } => {
            types.insert(*variable, *ty);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                declarations(instr, types);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                declarations(instr, types);
            }
        }
        _ => {}
    }
}

fn width(ty: VariableType) -> Option<usize> {
    match ty {
        VariableType::Unknown(size) => size,
        VariableType::Register(register) => Some(register.size()),
        VariableType::Bool => None,
    }
}

fn assignment(instr: &IRInst, target: VariableId) -> Option<&IRExpr> {
    match instr {
        IRInst::AssignVariable { variable, value } if *variable == target => Some(value),
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src,
        } if *variable == target => Some(src),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .find_map(|instr| assignment(instr, target)),
        IRInst::While { body, .. } => body.iter().find_map(|(_, instr)| assignment(instr, target)),
        _ => None,
    }
}

fn reachable(
    flow: &Flow,
    start: impl IntoIterator<Item = usize>,
    blocked: &HashSet<usize>,
) -> HashSet<usize> {
    let mut seen = HashSet::new();
    let mut pending: Vec<_> = start.into_iter().collect();
    while let Some(node) = pending.pop() {
        if blocked.contains(&node) || !seen.insert(node) {
            continue;
        }
        pending.extend(flow.nodes[node].successors.iter().copied());
    }
    seen
}

/// A read must follow the copy on every path. After that copy, no path may
/// change the base before reading the target. Re-entering the copy resets it.
fn safe(flow: &Flow, definitions: &[usize], target: VariableId, base: VariableId) -> bool {
    let blocked: HashSet<_> = definitions.iter().copied().collect();
    let reachable_nodes = reachable(flow, [flow.entry], &HashSet::new());
    if !definitions
        .iter()
        .any(|definition| reachable_nodes.contains(definition))
    {
        return false;
    }
    if reachable(flow, [flow.entry], &blocked)
        .iter()
        .any(|&node| flow.nodes[node].operation.reads(target))
    {
        return false;
    }

    let mut seen = HashSet::new();
    let mut pending: Vec<_> = definitions
        .iter()
        .flat_map(|&definition| {
            flow.nodes[definition]
                .successors
                .iter()
                .map(|&node| (node, false))
        })
        .collect();
    while let Some((node, changed)) = pending.pop() {
        if !seen.insert((node, changed)) {
            continue;
        }
        let op = &flow.nodes[node].operation;
        if blocked.contains(&node) {
            continue;
        }
        if changed && op.reads(target) {
            return false;
        }
        let changed = changed || op.write == Some(base);
        pending.extend(
            flow.nodes[node]
                .successors
                .iter()
                .map(|&next| (next, changed)),
        );
    }
    true
}

fn candidate(function: &SyntheticFunction, flow: &Flow) -> Option<(VariableId, IRExpr)> {
    let mut types = HashMap::new();
    for parameter in &function.parameters {
        if let Parameter::Slot { variable, register } = parameter {
            types.insert(*variable, VariableType::Register(*register));
        }
    }
    for (_, instr) in &function.body {
        declarations(instr, &mut types);
    }
    let parameters: HashSet<_> = function
        .parameters
        .iter()
        .filter_map(|parameter| match parameter {
            Parameter::Slot { variable, .. } => Some(*variable),
            Parameter::Native { .. } => None,
        })
        .collect();
    let mut writes = HashMap::new();
    for (index, node) in flow.nodes.iter().enumerate() {
        if let Some(variable) = node.operation.write {
            writes.entry(variable).or_insert_with(Vec::new).push(index);
        }
    }
    let mut ordered = writes.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|(_, definitions)| definitions[0]);
    for (&target, definitions) in ordered {
        let Some(derived) = flow.nodes[definitions[0]].operation.offset else {
            continue;
        };
        if target == derived.base
            || parameters.contains(&target)
            || definitions
                .iter()
                .any(|&index| flow.nodes[index].operation.offset != Some(derived))
        {
            continue;
        }
        let (Some(target_width), Some(base_width)) = (
            types.get(&target).copied().and_then(width),
            types.get(&derived.base).copied().and_then(width),
        ) else {
            continue;
        };
        // An address offset is only substituted at pointer width. This also
        // avoids changing the truncation point of a narrower assignment.
        if target_width != base_width {
            continue;
        }
        let value = function
            .body
            .iter()
            .find_map(|(_, instr)| assignment(instr, target))?
            .clone();
        if !matches!(value, IRExpr::Variable(_)) && target_width != 8 {
            continue;
        }
        if !safe(flow, definitions, target, derived.base) {
            continue;
        }
        return Some((target, value));
    }
    None
}

fn replace_expression(expr: &mut IRExpr, target: VariableId, value: &IRExpr) {
    match expr {
        IRExpr::Variable(variable) if *variable == target => *expr = value.clone(),
        IRExpr::BinOp { lhs, rhs, .. } => {
            replace_expression(lhs, target, value);
            replace_expression(rhs, target, value);
        }
        IRExpr::ReplaceBytes {
            original,
            value: replacement,
            ..
        } => {
            replace_expression(original, target, value);
            replace_expression(replacement, target, value);
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::Not(inner) => replace_expression(inner, target, value),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn rewrite(instr: &mut IRInst, target: VariableId, value: &IRExpr) {
    match instr {
        IRInst::Assign { dest, src } => {
            replace_expression(src, target, value);
            if !matches!(dest, IRExpr::Variable(_)) {
                replace_expression(dest, target, value);
            }
        }
        IRInst::AssignVariable { value: expr, .. } => replace_expression(expr, target, value),
        IRInst::LoadVariable { address, .. } => replace_expression(address, target, value),
        IRInst::StoreVariable { address, variable } => {
            replace_expression(address, target, value);
            if *variable == target {
                *instr = IRInst::Assign {
                    dest: IRExpr::Deref(Box::new(address.clone())),
                    src: value.clone(),
                };
            }
        }
        IRInst::Return(Some(expr)) | IRInst::Jump(expr) => {
            replace_expression(expr, target, value);
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            replace_expression(condition, target, value);
            for instr in then_branch.iter_mut().chain(else_branch) {
                rewrite(instr, target, value);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            match condition {
                LoopCondition::Before { expression, .. }
                | LoopCondition::After { expression, .. } => {
                    replace_expression(expression, target, value)
                }
            }
            for (_, instr) in body {
                rewrite(instr, target, value);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                replace_expression(argument, target, value);
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

fn remove(instr: &mut IRInst, target: VariableId) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            retain(then_branch, target);
            retain(else_branch, target);
        }
        IRInst::While { body, .. } => {
            body.retain(|(_, instr)| !is_removed(instr, target));
            for (_, instr) in body {
                remove(instr, target);
            }
        }
        _ => {}
    }
}

fn is_removed(instr: &IRInst, target: VariableId) -> bool {
    match instr {
        IRInst::DeclareVariable { variable, .. } | IRInst::AssignVariable { variable, .. }
            if *variable == target =>
        {
            true
        }
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            ..
        } if *variable == target => true,
        _ => false,
    }
}

fn retain(body: &mut Vec<IRInst>, target: VariableId) {
    body.retain(|instr| !is_removed(instr, target));
    for instr in body {
        remove(instr, target);
    }
}

fn effect_free(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Deref(_) => false,
        IRExpr::BinOp { lhs, rhs, .. } => effect_free(lhs) && effect_free(rhs),
        IRExpr::ReplaceBytes {
            original, value, ..
        } => effect_free(original) && effect_free(value),
        IRExpr::CastUnknownPtr { address, .. }
        | IRExpr::ExtractBytes { value: address, .. }
        | IRExpr::ZeroExtend { value: address, .. }
        | IRExpr::Not(address) => effect_free(address),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => true,
    }
}

fn simplify(instr: &mut IRInst) {
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            simplify_branch(then_branch);
            simplify_branch(else_branch);
            if then_branch.is_empty() && !else_branch.is_empty() {
                *condition = match std::mem::replace(condition, IRExpr::Bool(false)) {
                    IRExpr::Not(inner) => *inner,
                    value => IRExpr::Not(Box::new(value)),
                };
                std::mem::swap(then_branch, else_branch);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body.iter_mut() {
                simplify(instr);
            }
            body.retain(|(_, instr)| !empty_if(instr));
        }
        _ => {}
    }
}

fn empty_if(instr: &IRInst) -> bool {
    matches!(instr, IRInst::If { condition, then_branch, else_branch }
        if then_branch.is_empty() && else_branch.is_empty() && effect_free(condition))
}

fn simplify_branch(body: &mut Vec<IRInst>) {
    for instr in body.iter_mut() {
        simplify(instr);
    }
    body.retain(|instr| !empty_if(instr));
}

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        loop {
            let flow = Flow::from_function(function);
            let Some((target, value)) = candidate(function, &flow) else {
                break;
            };
            for (_, instr) in &mut function.body {
                rewrite(instr, target, &value);
            }
            function
                .body
                .retain(|(_, instr)| !is_removed(instr, target));
            for (_, instr) in &mut function.body {
                remove(instr, target);
            }
        }
        for (_, instr) in &mut function.body {
            simplify(instr);
        }
        function.body.retain(|(_, instr)| !empty_if(instr));
    }
}
