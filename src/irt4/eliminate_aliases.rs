//! Remove slot copies when the control-flow graph proves their source stable.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRExpr, IRInst, LoopCondition, Parameter, Program, SyntheticFunction, VariableId, VariableType,
};
use super::variable_flow::Flow;

fn declarations(instr: &IRInst, types: &mut HashMap<VariableId, VariableType>) {
    match instr {
        IRInst::DeclareVariable { variable, ty }
        | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
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
        VariableType::Bool => None,
    }
}

fn assignment(instr: &IRInst, target: VariableId) -> Option<&IRExpr> {
    match instr {
        IRInst::AssignVariable { variable, value }
        | IRInst::DeclareAndAssignVariable {
            variable, value, ..
        } if *variable == target => Some(value),
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

/// A read must follow the copy on every path. For a slot source, no path may
/// change the base before reading the target. Arguments need no such check.
/// Re-entering the copy resets the slot-source check.
fn safe(flow: &Flow, definitions: &[usize], target: VariableId, base: Option<VariableId>) -> bool {
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
        let changed = changed || base.is_some_and(|base| op.write == Some(base));
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
        if let Parameter::Slot { variable, size } = parameter {
            types.insert(*variable, VariableType::Unknown(Some(*size)));
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
            Parameter::Argument { .. } => None,
        })
        .collect();
    let argument_sizes: HashMap<_, _> = function
        .parameters
        .iter()
        .filter_map(|parameter| match parameter {
            Parameter::Argument { ordinal, size } => Some((*ordinal, *size)),
            Parameter::Slot { .. } => None,
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
        if parameters.contains(&target) {
            continue;
        }
        let Some(target_width) = types.get(&target).copied().and_then(width) else {
            continue;
        };
        let Some(value) = function
            .body
            .iter()
            .find_map(|(_, instr)| assignment(instr, target))
            .cloned()
        else {
            continue;
        };
        let base = match &value {
            IRExpr::Argument(ordinal)
                if argument_sizes.get(ordinal) == Some(&target_width)
                    && definitions
                        .iter()
                        .all(|&index| flow.nodes[index].operation.argument == Some(*ordinal)) =>
            {
                None
            }
            _ => {
                let Some(derived) = flow.nodes[definitions[0]].operation.offset else {
                    continue;
                };
                if target == derived.base
                    || definitions
                        .iter()
                        .any(|&index| flow.nodes[index].operation.offset != Some(derived))
                    || types.get(&derived.base).copied().and_then(width) != Some(target_width)
                {
                    continue;
                }
                // Address offsets are only substituted at pointer width, so
                // a narrower assignment keeps its truncation point.
                if !matches!(value, IRExpr::Variable(_)) && target_width != 8 {
                    continue;
                }
                Some(derived.base)
            }
        };
        if !safe(flow, definitions, target, base) {
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
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => replace_expression(inner, target, value),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Data(_)
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
        IRInst::AssignVariable { value: expr, .. }
        | IRInst::DeclareAndAssignVariable { value: expr, .. } => {
            replace_expression(expr, target, value)
        }
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
        IRInst::DeclareVariable { variable, .. }
        | IRInst::AssignVariable { variable, .. }
        | IRInst::DeclareAndAssignVariable { variable, .. }
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
        IRExpr::Data(_) => false,
        IRExpr::BinOp { lhs, rhs, .. } => effect_free(lhs) && effect_free(rhs),
        IRExpr::CastUnknownPtr { address, .. }
        | IRExpr::Convert { value: address, .. }
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

fn value_has_width(
    value: &IRExpr,
    ty: VariableType,
    types: &HashMap<VariableId, VariableType>,
    arguments: &HashMap<usize, usize>,
) -> bool {
    match (value, ty) {
        (IRExpr::Variable(variable), _) => types.get(variable) == Some(&ty),
        (IRExpr::Argument(ordinal), VariableType::Unknown(Some(size))) => {
            arguments.get(ordinal) == Some(&size)
        }
        (IRExpr::Deref(address), VariableType::Unknown(Some(size))) => matches!(
            &**address,
            IRExpr::CastUnknownPtr { size: Some(read_size), .. } if *read_size == size
        ),
        (IRExpr::Convert { target, .. }, VariableType::Unknown(Some(size))) => target.size == size,
        (IRExpr::CU8(_), VariableType::Unknown(Some(1)))
        | (IRExpr::CU32(_), VariableType::Unknown(Some(4)))
        | (IRExpr::CU64(_), VariableType::Unknown(Some(8)))
        | (IRExpr::Bool(_), VariableType::Bool)
        | (IRExpr::Not(_), VariableType::Bool) => true,
        _ => false,
    }
}

fn return_value(
    assignment: &IRInst,
    returning: &IRInst,
    reads: &HashMap<VariableId, usize>,
    writes: &HashMap<VariableId, usize>,
    types: &HashMap<VariableId, VariableType>,
    arguments: &HashMap<usize, usize>,
    parameters: &HashSet<VariableId>,
) -> Option<(VariableId, IRExpr)> {
    // Moving a load or expression across another instruction could change
    // what it reads. Only an adjacent definition and return are considered.
    let IRInst::Return(Some(IRExpr::Variable(target))) = returning else {
        return None;
    };
    if parameters.contains(target)
        || reads.get(target) != Some(&1)
        || writes.get(target) != Some(&1)
    {
        return None;
    }
    let ty = *types.get(target)?;
    let value = match assignment {
        IRInst::AssignVariable { variable, value }
        | IRInst::DeclareAndAssignVariable {
            variable, value, ..
        } if variable == target => value.clone(),
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src,
        } if variable == target => src.clone(),
        IRInst::LoadVariable { variable, address } if variable == target => {
            IRExpr::Deref(Box::new(address.clone()))
        }
        _ => return None,
    };
    value_has_width(&value, ty, types, arguments).then_some((*target, value))
}

struct ReturnUsage {
    reads: HashMap<VariableId, usize>,
    writes: HashMap<VariableId, usize>,
    types: HashMap<VariableId, VariableType>,
    arguments: HashMap<usize, usize>,
    parameters: HashSet<VariableId>,
}

impl ReturnUsage {
    fn from_function(function: &SyntheticFunction, flow: &Flow) -> Self {
        let mut usage = Self {
            reads: HashMap::new(),
            writes: HashMap::new(),
            types: HashMap::new(),
            arguments: HashMap::new(),
            parameters: HashSet::new(),
        };
        for parameter in &function.parameters {
            match parameter {
                Parameter::Argument { ordinal, size } => {
                    usage.arguments.insert(*ordinal, *size);
                }
                Parameter::Slot { variable, size } => {
                    usage.parameters.insert(*variable);
                    usage
                        .types
                        .insert(*variable, VariableType::Unknown(Some(*size)));
                }
            }
        }
        for (_, instr) in &function.body {
            declarations(instr, &mut usage.types);
        }
        for node in &flow.nodes {
            let variables: HashSet<_> = node
                .operation
                .dependencies
                .iter()
                .map(|dependency| dependency.base)
                .collect();
            for variable in variables {
                *usage.reads.entry(variable).or_default() += 1;
            }
            if let Some(variable) = node.operation.write {
                *usage.writes.entry(variable).or_default() += 1;
            }
        }
        usage
    }

    fn value(&self, assignment: &IRInst, returning: &IRInst) -> Option<(VariableId, IRExpr)> {
        return_value(
            assignment,
            returning,
            &self.reads,
            &self.writes,
            &self.types,
            &self.arguments,
            &self.parameters,
        )
    }
}

fn inline_returns_in_branch(
    body: &mut Vec<IRInst>,
    usage: &ReturnUsage,
    removed: &mut HashSet<VariableId>,
) {
    let mut index = 1;
    while index < body.len() {
        if let Some((variable, value)) = usage.value(&body[index - 1], &body[index]) {
            body[index] = IRInst::Return(Some(value));
            body.remove(index - 1);
            removed.insert(variable);
            index = index.saturating_sub(1).max(1);
        } else {
            index += 1;
        }
    }
    for instr in body {
        inline_returns_in_instruction(instr, usage, removed);
    }
}

fn inline_returns_in_body(
    body: &mut Vec<(usize, IRInst)>,
    usage: &ReturnUsage,
    removed: &mut HashSet<VariableId>,
) {
    let mut index = 1;
    while index < body.len() {
        if let Some((variable, value)) = usage.value(&body[index - 1].1, &body[index].1) {
            body[index].1 = IRInst::Return(Some(value));
            body.remove(index - 1);
            removed.insert(variable);
            index = index.saturating_sub(1).max(1);
        } else {
            index += 1;
        }
    }
    for (_, instr) in body {
        inline_returns_in_instruction(instr, usage, removed);
    }
}

fn inline_returns_in_instruction(
    instr: &mut IRInst,
    usage: &ReturnUsage,
    removed: &mut HashSet<VariableId>,
) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            inline_returns_in_branch(then_branch, usage, removed);
            inline_returns_in_branch(else_branch, usage, removed);
        }
        IRInst::While { body, .. } => inline_returns_in_body(body, usage, removed),
        _ => {}
    }
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
        let flow = Flow::from_function(function);
        let usage = ReturnUsage::from_function(function, &flow);
        let mut removed = HashSet::new();
        inline_returns_in_body(&mut function.body, &usage, &mut removed);
        for variable in removed {
            function
                .body
                .retain(|(_, instr)| !is_removed(instr, variable));
            for (_, instr) in &mut function.body {
                remove(instr, variable);
            }
        }
        for (_, instr) in &mut function.body {
            simplify(instr);
        }
        function.body.retain(|(_, instr)| !empty_if(instr));
    }
}
