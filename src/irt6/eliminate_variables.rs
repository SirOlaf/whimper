//! Fold a single-use local into an immediately following copy. Adjacency
//! preserves evaluation order even when the initializer reads memory.

use std::collections::{HashMap, HashSet};

use super::{
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

fn eliminate<T: Slot>(
    body: &mut Vec<T>,
    uses: &HashMap<VariableId, Uses>,
    types: &HashMap<VariableId, VariableType>,
    parameters: &HashSet<VariableId>,
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
        if let Some((variable, ty, value)) = candidate
            && let Some(destination) = copy_destination(body[index + 1].instruction(), variable)
            && types.get(&destination) == Some(ty)
            && !Effects::of_expression(&value).reads.contains(&destination)
        {
            replace_copy(body[index + 1].instruction_mut(), value);
            body.remove(index);
            changed = true;
        } else {
            index += 1;
        }
    }
    for slot in body {
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                changed |= eliminate(then_branch, uses, types, parameters);
                changed |= eliminate(else_branch, uses, types, parameters);
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                changed |= eliminate(body, uses, types, parameters);
            }
            _ => {}
        }
    }
    changed
}

pub(super) fn run(program: &mut Program) {
    for function in &mut program.functions {
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
            if !eliminate(&mut function.body, &uses, &types, &parameters) {
                break;
            }
        }
    }
}
