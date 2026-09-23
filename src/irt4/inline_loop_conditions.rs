//! Move a boolean slot's adjacent assignment into its loop check.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRExpr, IRInst, LoopCondition, LoopId, Parameter, Program, SyntheticFunction, VariableId,
    VariableType,
};

#[derive(Default)]
struct Usage {
    reads: usize,
    writes: usize,
    boolean: bool,
}

fn visit_expression(expr: &IRExpr, visit: &mut impl FnMut(VariableId)) {
    match expr {
        IRExpr::Variable(variable) => visit(*variable),
        IRExpr::BinOp { lhs, rhs, .. } => {
            visit_expression(lhs, visit);
            visit_expression(rhs, visit);
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => visit_expression(inner, visit),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Bool(_) => {}
    }
}

fn read_expression(expr: &IRExpr, usage: &mut HashMap<VariableId, Usage>) {
    visit_expression(expr, &mut |variable| {
        usage.entry(variable).or_default().reads += 1;
    });
}

fn collect(instr: &IRInst, usage: &mut HashMap<VariableId, Usage>) {
    match instr {
        IRInst::Assign { dest, src } => {
            read_expression(src, usage);
            if let IRExpr::Variable(variable) = dest {
                usage.entry(*variable).or_default().writes += 1;
            } else {
                read_expression(dest, usage);
            }
        }
        IRInst::DeclareVariable {
            variable,
            ty: VariableType::Bool,
        } => usage.entry(*variable).or_default().boolean = true,
        IRInst::DeclareVariable { .. } => {}
        IRInst::DeclareAndAssignVariable {
            variable,
            ty,
            value,
        } => {
            if *ty == VariableType::Bool {
                usage.entry(*variable).or_default().boolean = true;
            }
            read_expression(value, usage);
            usage.entry(*variable).or_default().writes += 1;
        }
        IRInst::AssignVariable { variable, value } => {
            read_expression(value, usage);
            usage.entry(*variable).or_default().writes += 1;
        }
        IRInst::LoadVariable { variable, address } => {
            read_expression(address, usage);
            usage.entry(*variable).or_default().writes += 1;
        }
        IRInst::StoreVariable { address, variable } => {
            read_expression(address, usage);
            usage.entry(*variable).or_default().reads += 1;
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => read_expression(value, usage),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            read_expression(condition, usage);
            for instr in then_branch.iter().chain(else_branch) {
                collect(instr, usage);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            match condition {
                LoopCondition::Before { expression, .. }
                | LoopCondition::After { expression, .. } => read_expression(expression, usage),
            }
            for (_, instr) in body {
                collect(instr, usage);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                read_expression(argument, usage);
            }
        }
        IRInst::Return(None)
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => {}
    }
}

fn assignment(instr: &IRInst, target: VariableId) -> Option<&IRExpr> {
    match instr {
        IRInst::AssignVariable { variable, value } if *variable == target => Some(value),
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src,
        } if *variable == target => Some(src),
        _ => None,
    }
}

fn condition_variable(condition: &LoopCondition) -> Option<VariableId> {
    let expression = match condition {
        LoopCondition::Before { expression, .. } | LoopCondition::After { expression, .. } => {
            expression
        }
    };
    match expression {
        IRExpr::Variable(variable) => Some(*variable),
        IRExpr::Not(inner) => match &**inner {
            IRExpr::Variable(variable) => Some(*variable),
            _ => None,
        },
        _ => None,
    }
}

fn reads_variable(expr: &IRExpr, variable: VariableId) -> bool {
    let mut found = false;
    visit_expression(expr, &mut |read| found |= read == variable);
    found
}

fn effect_free(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Deref(_) => false,
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

fn declares_input(instr: &IRInst, inputs: &HashSet<VariableId>) -> bool {
    match instr {
        IRInst::DeclareVariable { variable, .. }
        | IRInst::DeclareAndAssignVariable { variable, .. } => inputs.contains(variable),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .any(|instr| declares_input(instr, inputs)),
        IRInst::While { body, .. } => body.iter().any(|(_, instr)| declares_input(instr, inputs)),
        _ => false,
    }
}

/// A continue to this loop could bypass its trailing assignment.
fn continues_here(instr: &IRInst, label: Option<LoopId>, nested: bool) -> bool {
    match instr {
        IRInst::Continue => !nested,
        IRInst::ContinueLoop(target) => Some(*target) == label,
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => then_branch
            .iter()
            .chain(else_branch)
            .any(|instr| continues_here(instr, label, nested)),
        IRInst::While { body, .. } => body
            .iter()
            .any(|(_, instr)| continues_here(instr, label, true)),
        _ => false,
    }
}

struct Candidate {
    variable: VariableId,
    value: IRExpr,
    before: bool,
    remove_slot: bool,
}

fn candidate(
    previous: Option<&IRInst>,
    instr: &IRInst,
    usage: &HashMap<VariableId, Usage>,
    parameters: &HashSet<VariableId>,
) -> Option<Candidate> {
    let IRInst::While {
        label,
        condition,
        body,
        ..
    } = instr
    else {
        return None;
    };
    let variable = condition_variable(condition)?;
    let stats = usage.get(&variable)?;
    if !stats.boolean || parameters.contains(&variable) {
        return None;
    }
    let value = assignment(&body.last()?.1, variable)?;
    let before = matches!(condition, LoopCondition::Before { .. });
    if before {
        let initial = assignment(previous?, variable)?;
        if initial != value
            || body
                .iter()
                .any(|(_, instr)| continues_here(instr, *label, false))
        {
            return None;
        }
    }
    if stats.writes != if before { 2 } else { 1 }
        || reads_variable(value, variable)
        || (stats.reads != 1 && !effect_free(value))
    {
        return None;
    }
    // A do-while check is outside the body block. Its expression must not
    // depend on a slot declared only inside that block.
    let mut inputs = HashSet::new();
    visit_expression(value, &mut |input| {
        inputs.insert(input);
    });
    if body.iter().any(|(_, instr)| declares_input(instr, &inputs)) {
        return None;
    }
    Some(Candidate {
        variable,
        value: value.clone(),
        before,
        remove_slot: stats.reads == 1,
    })
}

fn inline(instr: &mut IRInst, candidate: &Candidate) {
    let IRInst::While {
        condition, body, ..
    } = instr
    else {
        unreachable!()
    };
    let expression = match condition {
        LoopCondition::Before { expression, .. } | LoopCondition::After { expression, .. } => {
            expression
        }
    };
    *expression = match expression {
        IRExpr::Not(_) => match candidate.value.clone() {
            IRExpr::Not(inner) => *inner,
            value => IRExpr::Not(Box::new(value)),
        },
        _ => candidate.value.clone(),
    };
    if candidate.remove_slot {
        body.pop();
    }
}

fn inline_offset_body(
    body: &mut Vec<(usize, IRInst)>,
    usage: &HashMap<VariableId, Usage>,
    parameters: &HashSet<VariableId>,
) -> Option<VariableId> {
    for index in 0..body.len() {
        let previous = index.checked_sub(1).map(|index| &body[index].1);
        if let Some(found) = candidate(previous, &body[index].1, usage, parameters) {
            inline(&mut body[index].1, &found);
            if found.remove_slot && found.before {
                body.remove(index - 1);
            }
            return Some(found.variable);
        }
        if let Some(variable) = inline_nested(&mut body[index].1, usage, parameters) {
            return Some(variable);
        }
    }
    None
}

fn inline_branch(
    body: &mut Vec<IRInst>,
    usage: &HashMap<VariableId, Usage>,
    parameters: &HashSet<VariableId>,
) -> Option<VariableId> {
    for index in 0..body.len() {
        let previous = index.checked_sub(1).map(|index| &body[index]);
        if let Some(found) = candidate(previous, &body[index], usage, parameters) {
            inline(&mut body[index], &found);
            if found.remove_slot && found.before {
                body.remove(index - 1);
            }
            return Some(found.variable);
        }
        if let Some(variable) = inline_nested(&mut body[index], usage, parameters) {
            return Some(variable);
        }
    }
    None
}

fn inline_nested(
    instr: &mut IRInst,
    usage: &HashMap<VariableId, Usage>,
    parameters: &HashSet<VariableId>,
) -> Option<VariableId> {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => inline_branch(then_branch, usage, parameters)
            .or_else(|| inline_branch(else_branch, usage, parameters)),
        IRInst::While { body, .. } => inline_offset_body(body, usage, parameters),
        _ => None,
    }
}

fn remove_declarations_from_branch(body: &mut Vec<IRInst>, variable: VariableId) {
    body.retain(|instr| {
        !matches!(instr, IRInst::DeclareVariable { variable: declared, .. } if *declared == variable)
    });
    for instr in body {
        remove_nested_declarations(instr, variable);
    }
}

fn remove_declarations_from_offset_body(body: &mut Vec<(usize, IRInst)>, variable: VariableId) {
    body.retain(|(_, instr)| {
        !matches!(instr, IRInst::DeclareVariable { variable: declared, .. } if *declared == variable)
    });
    for (_, instr) in body {
        remove_nested_declarations(instr, variable);
    }
}

fn remove_nested_declarations(instr: &mut IRInst, variable: VariableId) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            remove_declarations_from_branch(then_branch, variable);
            remove_declarations_from_branch(else_branch, variable);
        }
        IRInst::While { body, .. } => remove_declarations_from_offset_body(body, variable),
        _ => {}
    }
}

fn inline_function(function: &mut SyntheticFunction) {
    loop {
        let mut usage = HashMap::new();
        for (_, instr) in &function.body {
            collect(instr, &mut usage);
        }
        let parameters: HashSet<_> = function
            .parameters
            .iter()
            .filter_map(|parameter| match parameter {
                Parameter::Slot { variable, .. } => Some(*variable),
                Parameter::Argument { .. } => None,
            })
            .collect();
        let Some(variable) = inline_offset_body(&mut function.body, &usage, &parameters) else {
            break;
        };
        if usage[&variable].reads == 1 {
            remove_declarations_from_offset_body(&mut function.body, variable);
        }
    }
}

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        inline_function(function);
    }
}
