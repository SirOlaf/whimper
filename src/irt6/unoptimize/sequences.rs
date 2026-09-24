use super::super::{
    arithmetic::Context,
    effects::{Effects, repeatable},
    ir::{IRInst, LoopCondition, VariableId},
    shapes,
};
use super::{
    Options, Report, Rewrite,
    facts::{Facts, writes_disjoint},
    rules::RULES,
};
use std::collections::HashMap;

pub(super) const MAX_REWRITES: usize = 256;
const MAX_LOCAL_ROUNDS: usize = 16;

pub(super) trait InstructionSlot {
    fn instruction(&self) -> &IRInst;
    fn instruction_mut(&mut self) -> &mut IRInst;
    fn offset(&self, fallback: usize) -> usize;
}

impl InstructionSlot for IRInst {
    fn instruction(&self) -> &IRInst {
        self
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        self
    }

    fn offset(&self, fallback: usize) -> usize {
        fallback
    }
}

impl InstructionSlot for (usize, IRInst) {
    fn instruction(&self) -> &IRInst {
        &self.1
    }

    fn instruction_mut(&mut self) -> &mut IRInst {
        &mut self.1
    }

    fn offset(&self, _fallback: usize) -> usize {
        self.0
    }
}

#[derive(Default, PartialEq, Eq)]
pub(super) struct VariableUses {
    reads: usize,
    writes: usize,
}

fn add_uses(effects: &Effects, uses: &mut HashMap<VariableId, VariableUses>) {
    for variable in &effects.reads {
        uses.entry(*variable).or_default().reads += 1;
    }
    for variable in &effects.writes {
        uses.entry(*variable).or_default().writes += 1;
    }
}

pub(super) fn collect_uses(instr: &IRInst, uses: &mut HashMap<VariableId, VariableUses>) {
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            add_uses(&Effects::of_expression(condition), uses);
            for instr in then_branch.iter().chain(else_branch) {
                collect_uses(instr, uses);
            }
        }
        IRInst::While {
            condition, body, ..
        } => {
            let (LoopCondition::Before { expression, .. }
            | LoopCondition::After { expression, .. }) = condition;
            add_uses(&Effects::of_expression(expression), uses);
            for (_, instr) in body {
                collect_uses(instr, uses);
            }
        }
        IRInst::ForEach {
            variable,
            vector,
            body,
            ..
        } => {
            add_uses(&Effects::of_expression(vector), uses);
            uses.entry(*variable).or_default().writes += 1;
            for (_, instr) in body {
                collect_uses(instr, uses);
            }
        }
        _ => {
            let mut effects = Effects::default();
            effects.instruction(instr);
            add_uses(&effects, uses);
        }
    }
}

pub(super) fn collapse_temporary_assignments<T: InstructionSlot>(
    instructions: &mut Vec<T>,
    fallback_offset: usize,
    context: &Context,
    uses: &HashMap<VariableId, VariableUses>,
    report: &mut Report,
) {
    for slot in instructions.iter_mut() {
        let offset = slot.offset(fallback_offset);
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                collapse_temporary_assignments(then_branch, offset, context, uses, report);
                collapse_temporary_assignments(else_branch, offset, context, uses, report);
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                collapse_temporary_assignments(body, offset, context, uses, report);
            }
            _ => {}
        }
    }
    let mut index = 0;
    while index + 2 < instructions.len() {
        if report.rewrites.len() >= MAX_REWRITES {
            report.budget_exhausted = true;
            return;
        }
        let shape = shapes::temporary_binary_assignment(
            instructions[index].instruction(),
            instructions[index + 1].instruction(),
            instructions[index + 2].instruction(),
            context,
        );
        if let Some(shape) = shape
            && matches!(
                uses.get(&shape.temporary),
                Some(VariableUses {
                    reads: 2,
                    writes: 2,
                })
            )
        {
            let offset = instructions[index + 2].offset(fallback_offset);
            *instructions[index + 2].instruction_mut() = shape.replacement;
            instructions.drain(index..index + 2);
            report.rewrites.push(Rewrite {
                offset,
                rule: "temporary-binary-to-assignment",
            });
        } else {
            index += 1;
        }
    }
}

pub(super) fn recover_vector_iterations<T: InstructionSlot>(
    instructions: &mut Vec<T>,
    fallback_offset: usize,
    context: &Context,
    uses: &HashMap<VariableId, VariableUses>,
    report: &mut Report,
) -> bool {
    for slot in instructions.iter_mut() {
        let offset = slot.offset(fallback_offset);
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                if recover_vector_iterations(then_branch, offset, context, uses, report)
                    || recover_vector_iterations(else_branch, offset, context, uses, report)
                {
                    return true;
                }
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                if recover_vector_iterations(body, offset, context, uses, report) {
                    return true;
                }
            }
            _ => {}
        }
    }
    if instructions.len() < 3 || report.rewrites.len() >= MAX_REWRITES {
        return false;
    }
    for loop_index in 2..instructions.len() {
        let element_index = loop_index - 1;
        for counter_index in (0..element_index).rev() {
            let Some(shape) = shapes::vector_iteration(
                instructions[counter_index].instruction(),
                instructions[element_index].instruction(),
                instructions[loop_index].instruction(),
                context,
            ) else {
                continue;
            };
            let mut local_uses = HashMap::new();
            for index in [counter_index, element_index, loop_index] {
                collect_uses(instructions[index].instruction(), &mut local_uses);
            }
            if [shape.counter, shape.element]
                .iter()
                .any(|variable| uses.get(variable) != local_uses.get(variable))
            {
                continue;
            }
            let mut intervening = Effects::default();
            for slot in &instructions[counter_index + 1..element_index] {
                intervening.instruction(slot.instruction());
            }
            if intervening.reads.contains(&shape.counter)
                || intervening.writes.contains(&shape.counter)
                || intervening.reads.contains(&shape.element)
                || intervening.writes.contains(&shape.element)
            {
                continue;
            }
            let offset = match &shape.replacement {
                IRInst::ForEach { entry_offset, .. } => *entry_offset,
                _ => unreachable!(),
            };
            *instructions[loop_index].instruction_mut() = shape.replacement;
            instructions.remove(element_index);
            instructions.remove(counter_index);
            report.rewrites.push(Rewrite {
                offset,
                rule: "zero-terminated-vector-iteration",
            });
            return true;
        }
    }
    false
}

/// Two consecutive checks of the same pure condition can share a branch
/// when neither arm of the first check changes any value read by it.
pub(super) fn merge_adjacent_branches<T: InstructionSlot>(
    instructions: &mut Vec<T>,
    fallback_offset: usize,
    report: &mut Report,
) {
    let mut index = 0;
    while index + 1 < instructions.len() {
        if report.rewrites.len() >= MAX_REWRITES {
            report.budget_exhausted = true;
            return;
        }
        let can_merge = match (
            instructions[index].instruction(),
            instructions[index + 1].instruction(),
        ) {
            (
                IRInst::If {
                    condition: first,
                    then_branch,
                    else_branch,
                },
                IRInst::If {
                    condition: second, ..
                },
            ) if first == second && repeatable(first) => {
                let reads = &Effects::of_expression(first).reads;
                then_branch.iter().chain(else_branch).all(|instruction| {
                    let mut effects = Effects::default();
                    effects.instruction(instruction);
                    effects.writes.is_disjoint(reads)
                })
            }
            _ => false,
        };
        if !can_merge {
            index += 1;
            continue;
        }

        let offset = instructions[index + 1].offset(fallback_offset);
        let (first, second) = instructions.split_at_mut(index + 1);
        let IRInst::If {
            then_branch: first_then,
            else_branch: first_else,
            ..
        } = first[index].instruction_mut()
        else {
            unreachable!();
        };
        let IRInst::If {
            then_branch: second_then,
            else_branch: second_else,
            ..
        } = second[0].instruction_mut()
        else {
            unreachable!();
        };
        first_then.append(second_then);
        first_else.append(second_else);
        instructions.remove(index + 1);
        report.rewrites.push(Rewrite {
            offset,
            rule: "merge-identical-adjacent-branches",
        });
        // Keep this index: a third adjacent check may also be mergeable.
    }

    for slot in instructions {
        let offset = slot.offset(fallback_offset);
        match slot.instruction_mut() {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                merge_adjacent_branches(then_branch, offset, report);
                merge_adjacent_branches(else_branch, offset, report);
            }
            IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
                merge_adjacent_branches(body, offset, report);
            }
            _ => {}
        }
    }
}

pub(super) fn sequence<'a>(
    instructions: impl Iterator<Item = (usize, &'a mut IRInst)>,
    context: &Context,
    mut facts: Facts,
    options: &Options,
    report: &mut Report,
) {
    for (offset, instr) in instructions {
        rewrite(instr, offset, context, &facts, options, report);
        let mut effects = Effects::default();
        effects.instruction(instr);
        facts.invalidate(&effects, |address| writes_disjoint(instr, address));
        facts.observe(instr);
    }
}

fn rewrite_local(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    options: &Options,
    report: &mut Report,
) {
    for round in 0..MAX_LOCAL_ROUNDS {
        if report.rewrites.len() >= MAX_REWRITES {
            report.budget_exhausted = true;
            return;
        }
        let mut changed = false;
        for rule in RULES {
            if let Some(offset) = (rule.apply)(instr, offset, context, facts, options) {
                report.rewrites.push(Rewrite {
                    offset,
                    rule: rule.name,
                });
                changed = true;
                break;
            }
        }
        if !changed {
            break;
        }
        if round + 1 == MAX_LOCAL_ROUNDS {
            report.budget_exhausted = true;
        }
    }
}

fn rewrite(
    instr: &mut IRInst,
    offset: usize,
    context: &Context,
    facts: &Facts,
    options: &Options,
    report: &mut Report,
) {
    rewrite_local(instr, offset, context, facts, options, report);
    let before_children = report.rewrites.len();
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut then_facts = facts.clone();
            then_facts.assume(condition, true, context);
            let mut else_facts = facts.clone();
            else_facts.assume(condition, false, context);
            sequence(
                then_branch.iter_mut().map(|instr| (offset, instr)),
                context,
                then_facts,
                options,
                report,
            );
            sequence(
                else_branch.iter_mut().map(|instr| (offset, instr)),
                context,
                else_facts,
                options,
                report,
            );
        }
        IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
            let mut effects = Effects::default();
            for (_, instr) in body.iter() {
                effects.instruction(instr);
            }
            let mut invariants = facts.clone();
            invariants.invalidate(&effects, |address| {
                body.iter()
                    .all(|(_, instr)| writes_disjoint(instr, address))
            });
            sequence(
                body.iter_mut().map(|(offset, instr)| (*offset, instr)),
                context,
                invariants,
                options,
                report,
            );
        }
        _ => {}
    }
    // A child loop can become a modulo assignment under its surrounding
    // guard. Revisit that guard once its child rewrites are visible.
    if report.rewrites.len() > before_children {
        rewrite_local(instr, offset, context, facts, options, report);
    }
}
