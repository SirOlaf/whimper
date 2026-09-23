//! Fold branch-local constant returns and combine identical early exits.

use std::collections::{HashMap, HashSet};

use super::{
    ir::{IRBinOpKind, IRExpr, IRInst, Program, VariableId, VariableType},
    variable_flow::Flow,
};

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

fn constant_return(
    assignment: &IRInst,
    returning: &IRInst,
    types: &HashMap<VariableId, VariableType>,
) -> Option<(VariableId, IRExpr)> {
    let IRInst::Return(Some(IRExpr::Variable(target))) = returning else {
        return None;
    };
    let value = match assignment {
        IRInst::AssignVariable { variable, value } if variable == target => value,
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src,
        } if variable == target => src,
        _ => return None,
    };
    // Keep the assignment as the width boundary when the literal's width
    // differs from the slot's width.
    let same_width = matches!(
        (types.get(target), value),
        (Some(VariableType::Unknown(Some(1))), IRExpr::CU8(_))
            | (Some(VariableType::Unknown(Some(4))), IRExpr::CU32(_))
            | (Some(VariableType::Unknown(Some(8))), IRExpr::CU64(_))
            | (Some(VariableType::Bool), IRExpr::Bool(_))
    );
    same_width.then(|| (*target, value.clone()))
}

/// A return immediately following an if needs no merge slot when both arms
/// end by assigning that slot. Keep each arm's effects and return its value.
fn joined_return(
    conditional: &IRInst,
    returning: &IRInst,
    types: &HashMap<VariableId, VariableType>,
) -> Option<(VariableId, IRInst)> {
    let IRInst::Return(Some(IRExpr::Variable(target))) = returning else {
        return None;
    };
    let IRInst::If {
        condition,
        then_branch,
        else_branch,
    } = conditional
    else {
        return None;
    };
    let ty = *types.get(target)?;
    let branch = |body: &[IRInst]| -> Option<Vec<IRInst>> {
        let value = match body.last()? {
            IRInst::AssignVariable { variable, value } if variable == target => value,
            IRInst::Assign {
                dest: IRExpr::Variable(variable),
                src,
            } if variable == target => src,
            _ => return None,
        };
        let same_width = match (value, ty) {
            (IRExpr::Variable(variable), _) => types.get(variable) == Some(&ty),
            (IRExpr::Convert { target, .. }, VariableType::Unknown(Some(size))) => {
                target.size == size
            }
            (IRExpr::CU8(_), VariableType::Unknown(Some(1)))
            | (IRExpr::CU32(_), VariableType::Unknown(Some(4)))
            | (IRExpr::CU64(_), VariableType::Unknown(Some(8)))
            | (IRExpr::Bool(_), VariableType::Bool) => true,
            _ => false,
        };
        if !same_width {
            return None;
        }
        let mut body = body.to_vec();
        *body.last_mut()? = IRInst::Return(Some(value.clone()));
        Some(body)
    };
    Some((
        *target,
        IRInst::If {
            condition: condition.clone(),
            then_branch: branch(then_branch)?,
            else_branch: branch(else_branch)?,
        },
    ))
}

fn append_or(left: IRExpr, right: IRExpr) -> IRExpr {
    match right {
        IRExpr::BinOp {
            kind: IRBinOpKind::Or,
            lhs,
            rhs,
        } => append_or(append_or(left, *lhs), *rhs),
        right => IRExpr::BinOp {
            kind: IRBinOpKind::Or,
            lhs: Box::new(left),
            rhs: Box::new(right),
        },
    }
}

fn merge_if(instr: &mut IRInst) {
    let IRInst::If {
        condition,
        then_branch,
        else_branch,
    } = instr
    else {
        return;
    };
    // `Or` is the IR's short-circuit logical disjunction. The second
    // condition is evaluated only after the first condition is false.
    while then_branch.len() == 1 && matches!(then_branch[0], IRInst::Return(_)) {
        let [
            IRInst::If {
                condition: nested_condition,
                then_branch: nested_then,
                else_branch: nested_else,
            },
        ] = else_branch.as_slice()
        else {
            break;
        };
        if !matches!(
            (then_branch.first(), nested_then.first(), nested_then.len()),
            (Some(IRInst::Return(left)), Some(IRInst::Return(right)), 1) if left == right
        ) {
            break;
        }
        *condition = append_or(condition.clone(), nested_condition.clone());
        *else_branch = nested_else.clone();
    }
}

fn simplify_instruction(
    instr: &mut IRInst,
    types: &HashMap<VariableId, VariableType>,
    folded: &mut HashSet<VariableId>,
) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            simplify_branch(then_branch, types, folded);
            simplify_branch(else_branch, types, folded);
            merge_if(instr);
        }
        IRInst::While { body, .. } => simplify_body(body, types, folded),
        _ => {}
    }
}

fn simplify_branch(
    branch: &mut Vec<IRInst>,
    types: &HashMap<VariableId, VariableType>,
    folded: &mut HashSet<VariableId>,
) {
    let mut index = 1;
    while index < branch.len() {
        if let Some((variable, conditional)) =
            joined_return(&branch[index - 1], &branch[index], types)
        {
            branch[index - 1] = conditional;
            branch.remove(index);
            folded.insert(variable);
        } else if let Some((variable, value)) =
            constant_return(&branch[index - 1], &branch[index], types)
        {
            branch[index] = IRInst::Return(Some(value));
            branch.remove(index - 1);
            folded.insert(variable);
        } else {
            index += 1;
        }
    }
    for instr in branch {
        simplify_instruction(instr, types, folded);
    }
}

fn simplify_body(
    body: &mut Vec<(usize, IRInst)>,
    types: &HashMap<VariableId, VariableType>,
    folded: &mut HashSet<VariableId>,
) {
    let mut index = 1;
    while index < body.len() {
        if let Some((variable, conditional)) =
            joined_return(&body[index - 1].1, &body[index].1, types)
        {
            body[index - 1].1 = conditional;
            body.remove(index);
            folded.insert(variable);
        } else if let Some((variable, value)) =
            constant_return(&body[index - 1].1, &body[index].1, types)
        {
            body[index].1 = IRInst::Return(Some(value));
            body.remove(index - 1);
            folded.insert(variable);
        } else {
            index += 1;
        }
    }
    for (_, instr) in body {
        simplify_instruction(instr, types, folded);
    }
}

fn remove_declarations(instr: &mut IRInst, unused: &HashSet<VariableId>) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            then_branch.retain(|instr| !dead_declaration(instr, unused));
            else_branch.retain(|instr| !dead_declaration(instr, unused));
            for instr in then_branch.iter_mut().chain(else_branch) {
                remove_declarations(instr, unused);
            }
        }
        IRInst::While { body, .. } => {
            body.retain(|(_, instr)| !dead_declaration(instr, unused));
            for (_, instr) in body {
                remove_declarations(instr, unused);
            }
        }
        _ => {}
    }
}

fn dead_declaration(instr: &IRInst, unused: &HashSet<VariableId>) -> bool {
    matches!(instr, IRInst::DeclareVariable { variable, .. } if unused.contains(variable))
}

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        let mut types = HashMap::new();
        for (_, instr) in &function.body {
            declarations(instr, &mut types);
        }
        let mut folded = HashSet::new();
        simplify_body(&mut function.body, &types, &mut folded);
        if folded.is_empty() {
            continue;
        }
        let flow = Flow::from_function(function);
        let unused = folded
            .into_iter()
            .filter(|variable| {
                flow.nodes.iter().all(|node| {
                    node.operation.write != Some(*variable) && !node.operation.reads(*variable)
                })
            })
            .collect::<HashSet<_>>();
        function
            .body
            .retain(|(_, instr)| !dead_declaration(instr, &unused));
        for (_, instr) in &mut function.body {
            remove_declarations(instr, &unused);
        }
    }
}
