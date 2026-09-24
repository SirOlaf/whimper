//! Fold local copies and adjacent single-use initializers. Adjacency
//! preserves evaluation order even when an initializer reads memory.

use std::collections::{HashMap, HashSet};

use super::{
    arithmetic::Context,
    effects::Effects,
    ir::{IRExpr, IRInst, LoopCondition, Parameter, Program, VariableId, VariableType},
};

trait Slot {
    fn instruction(&self) -> &IRInst;
    fn instruction_mut(&mut self) -> &mut IRInst;
}

impl Slot for IRInst {
    fn instruction(&self) -> &IRInst {
        self
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        self
    }
}

impl Slot for (usize, IRInst) {
    fn instruction(&self) -> &IRInst {
        &self.1
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        &mut self.1
    }
}

#[derive(Default)]
struct Uses {
    reads: usize,
    writes: usize,
}

fn add(effects: &Effects, uses: &mut HashMap<VariableId, Uses>) {
    for variable in &effects.reads {
        uses.entry(*variable).or_default().reads += 1;
    }
    for variable in &effects.writes {
        uses.entry(*variable).or_default().writes += 1;
    }
}

fn collect(instr: &IRInst, uses: &mut HashMap<VariableId, Uses>) {
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            add(&Effects::of_expression(condition), uses);
            for child in then_branch.iter().chain(else_branch) {
                collect(child, uses);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            let (LoopCondition::Before { expression, .. }
            | LoopCondition::After { expression, .. }) = condition;
            add(&Effects::of_expression(expression), uses);
            for (_, child) in body {
                collect(child, uses);
            }
        }
        IRInst::ForEach {
            variable,
            vector,
            body,
            ..
        } => {
            add(&Effects::of_expression(vector), uses);
            uses.entry(*variable).or_default().writes += 1;
            for (_, child) in body {
                collect(child, uses);
            }
        }
        _ => {
            let mut effects = Effects::default();
            effects.instruction(instr);
            add(&effects, uses);
        }
    }
}

fn copy_destination(instr: &IRInst, source: VariableId) -> Option<VariableId> {
    match instr {
        IRInst::DeclareAndAssignVariable {
            variable,
            value: IRExpr::Variable(read),
            ..
        }
        | IRInst::AssignVariable {
            variable,
            value: IRExpr::Variable(read),
        } if *read == source && *variable != source => Some(*variable),
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: IRExpr::Variable(read),
        } if *read == source && *variable != source => Some(*variable),
        _ => None,
    }
}

fn collect_types(instr: &IRInst, types: &mut HashMap<VariableId, VariableType>) {
    match instr {
        IRInst::DeclareVariable { variable, ty }
        | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
            types.insert(*variable, ty.clone());
        }
        IRInst::ForEach {
            variable,
            element_type,
            body,
            ..
        } => {
            types.insert(*variable, element_type.clone());
            for (_, child) in body {
                collect_types(child, types);
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for child in then_branch.iter().chain(else_branch) {
                collect_types(child, types);
            }
        }
        IRInst::While { body, .. } => {
            for (_, child) in body {
                collect_types(child, types);
            }
        }
        _ => {}
    }
}

fn replace_copy(instr: &mut IRInst, value: IRExpr) {
    match instr {
        IRInst::DeclareAndAssignVariable { value: target, .. }
        | IRInst::AssignVariable { value: target, .. } => *target = value,
        IRInst::Assign { src, .. } => *src = value,
        _ => unreachable!(),
    }
}

fn assignment_value(instr: &IRInst, variable: VariableId) -> Option<&IRExpr> {
    match instr {
        IRInst::AssignVariable {
            variable: dest,
            value,
        }
        | IRInst::Assign {
            dest: IRExpr::Variable(dest),
            src: value,
        } if *dest == variable => Some(value),
        _ => None,
    }
}

fn assignment_value_mut(instr: &mut IRInst, variable: VariableId) -> Option<&mut IRExpr> {
    match instr {
        IRInst::AssignVariable {
            variable: dest,
            value,
        }
        | IRInst::Assign {
            dest: IRExpr::Variable(dest),
            src: value,
        } if *dest == variable => Some(value),
        _ => None,
    }
}

fn replace_read(expr: &mut IRExpr, variable: VariableId, replacement: &IRExpr) {
    match expr {
        IRExpr::Variable(read) if *read == variable => *expr = replacement.clone(),
        IRExpr::BinOp { lhs, rhs, .. } => {
            replace_read(lhs, variable, replacement);
            replace_read(rhs, variable, replacement);
        }
        IRExpr::ElementAddress { base, index, .. } => {
            replace_read(base, variable, replacement);
            replace_read(index, variable, replacement);
        }
        IRExpr::Deref(inner)
        | IRExpr::CStringLength(inner)
        | IRExpr::Not(inner)
        | IRExpr::MemoryAddress { address: inner, .. }
        | IRExpr::Convert { value: inner, .. } => replace_read(inner, variable, replacement),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Data(_)
        | IRExpr::Bool(_) => {}
    }
}

/// An element copied into a local and consumed by the next accumulator
/// update can be read directly. The preceding initializer accounts for the
/// local's only other read, so its value is never needed after the loop.
fn inline_foreach_copy<T: Slot>(
    body: &mut Vec<T>,
    uses: &HashMap<VariableId, Uses>,
    types: &HashMap<VariableId, VariableType>,
    parameters: &HashSet<VariableId>,
) -> bool {
    for index in 2..body.len() {
        let shape = match (
            body[index - 2].instruction(),
            body[index - 1].instruction(),
            body[index].instruction(),
        ) {
            (
                IRInst::DeclareAndAssignVariable {
                    variable: temporary,
                    ..
                },
                IRInst::DeclareAndAssignVariable {
                    variable: accumulator,
                    value: initial,
                    ..
                },
                IRInst::ForEach {
                    variable: element,
                    element_type,
                    body: loop_body,
                    ..
                },
            ) if temporary != accumulator
                && !parameters.contains(temporary)
                && types.get(temporary) == Some(element_type)
                && uses
                    .get(temporary)
                    .is_some_and(|uses| uses.reads == 2 && uses.writes == 2)
                && Effects::of_expression(initial).reads.contains(temporary)
                && loop_body.len() == 2
                && matches!(assignment_value(&loop_body[0].1, *temporary), Some(IRExpr::Variable(source)) if source == element)
                && assignment_value(&loop_body[1].1, *accumulator).is_some_and(|value| {
                    Effects::of_expression(value).reads.contains(temporary)
                }) =>
            {
                Some((*temporary, *accumulator, *element))
            }
            _ => None,
        };
        if let Some((temporary, accumulator, element)) = shape {
            let IRInst::ForEach {
                body: loop_body, ..
            } = body[index].instruction_mut()
            else {
                unreachable!();
            };
            replace_read(
                assignment_value_mut(&mut loop_body[1].1, accumulator).unwrap(),
                temporary,
                &IRExpr::Variable(element),
            );
            loop_body.remove(0);
            return true;
        }
    }
    for slot in body {
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                if inline_foreach_copy(then_branch, uses, types, parameters)
                    || inline_foreach_copy(else_branch, uses, types, parameters)
                {
                    return true;
                }
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                if inline_foreach_copy(body, uses, types, parameters) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn converted_copy(instr: &IRInst, source: VariableId) -> Option<(VariableId, usize)> {
    let (destination, value) = match instr {
        IRInst::DeclareAndAssignVariable {
            variable, value, ..
        }
        | IRInst::AssignVariable { variable, value }
        | IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src: value,
        } => (*variable, value),
        _ => return None,
    };
    match value {
        IRExpr::Convert {
            value,
            source: kind,
            ..
        } if value.as_ref() == &IRExpr::Variable(source) => Some((destination, kind.size)),
        _ => None,
    }
}

fn replace_converted_copy(instr: &mut IRInst, value: IRExpr) {
    let target = match instr {
        IRInst::DeclareAndAssignVariable {
            value: IRExpr::Convert { value: target, .. },
            ..
        }
        | IRInst::AssignVariable {
            value: IRExpr::Convert { value: target, .. },
            ..
        }
        | IRInst::Assign {
            src: IRExpr::Convert { value: target, .. },
            ..
        } => target,
        _ => unreachable!(),
    };
    *target = Box::new(value);
}

fn eliminate<T: Slot>(
    body: &mut Vec<T>,
    uses: &HashMap<VariableId, Uses>,
    types: &HashMap<VariableId, VariableType>,
    parameters: &HashSet<VariableId>,
    context: &Context,
) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < body.len() {
        let candidate = match body[index].instruction() {
            IRInst::DeclareAndAssignVariable {
                variable,
                ty,
                value,
            } if !parameters.contains(variable)
                && uses
                    .get(variable)
                    .is_some_and(|uses| uses.reads == 1 && uses.writes == 1)
                && !Effects::of_expression(value).reads.contains(variable) =>
            {
                Some((*variable, ty, value.clone()))
            }
            _ => None,
        };
        if let Some((variable, ty, value)) = candidate {
            let next = body[index + 1].instruction();
            let direct = copy_destination(next, variable).filter(|destination| {
                types.get(destination) == Some(ty)
                    && !Effects::of_expression(&value).reads.contains(destination)
            });
            let converted = converted_copy(next, variable).filter(|(destination, source_size)| {
                *destination != variable
                    && !Effects::of_expression(&value).reads.contains(destination)
                    && context.value(&IRExpr::Variable(variable)).bits == context.value(&value).bits
                    && context.value(&value).bits == source_size.checked_mul(8)
            });
            if direct.is_some() {
                replace_copy(body[index + 1].instruction_mut(), value);
                body.remove(index);
                changed = true;
                continue;
            }
            if converted.is_some() {
                replace_converted_copy(body[index + 1].instruction_mut(), value);
                body.remove(index);
                changed = true;
                continue;
            }
        }
        index += 1;
    }
    for slot in body {
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                changed |= eliminate(then_branch, uses, types, parameters, context);
                changed |= eliminate(else_branch, uses, types, parameters, context);
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                changed |= eliminate(body, uses, types, parameters, context);
            }
            _ => {}
        }
    }
    changed
}

pub(super) fn run(program: &mut Program) {
    for function in &mut program.functions {
        let context = Context::from_function(function);
        let mut types = HashMap::new();
        for parameter in &function.parameters {
            if let Parameter::Slot { variable, ty } = parameter {
                types.insert(*variable, ty.clone());
            }
        }
        for (_, instr) in &function.body {
            collect_types(instr, &mut types);
        }
        let parameters = function
            .parameters
            .iter()
            .filter_map(|parameter| match parameter {
                Parameter::Slot { variable, .. } => Some(*variable),
                Parameter::Argument { .. } => None,
            })
            .collect();
        loop {
            let mut uses = HashMap::new();
            for (_, instr) in &function.body {
                collect(instr, &mut uses);
            }
            if inline_foreach_copy(&mut function.body, &uses, &types, &parameters) {
                continue;
            }
            if !eliminate(&mut function.body, &uses, &types, &parameters, &context) {
                break;
            }
        }
    }
}
