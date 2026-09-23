//! Place each local declaration in the block shared by all uses of its slot.

use std::collections::{HashMap, HashSet};

use super::ir::{
    IRExpr, IRInst, LoopCondition, Parameter, Program, SyntheticFunction, VariableId, VariableType,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Child {
    Then,
    Else,
    Loop,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Step {
    index: usize,
    child: Child,
}

struct Use {
    scope: Vec<Step>,
    index: usize,
    starts_with_write: bool,
}

fn expression_uses(expr: &IRExpr, variable: VariableId) -> bool {
    match expr {
        IRExpr::Variable(found) => *found == variable,
        IRExpr::BinOp { lhs, rhs, .. } => {
            expression_uses(lhs, variable) || expression_uses(rhs, variable)
        }
        IRExpr::Deref(inner)
        | IRExpr::CastUnknownPtr { address: inner, .. }
        | IRExpr::Convert { value: inner, .. }
        | IRExpr::Not(inner) => expression_uses(inner, variable),
        IRExpr::Argument(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Bool(_) => false,
    }
}

fn direct_use(instr: &IRInst, variable: VariableId) -> bool {
    match instr {
        IRInst::Assign { dest, src } => {
            expression_uses(dest, variable) || expression_uses(src, variable)
        }
        IRInst::AssignVariable {
            variable: written,
            value,
        }
        | IRInst::DeclareAndAssignVariable {
            variable: written,
            value,
            ..
        } => *written == variable || expression_uses(value, variable),
        IRInst::LoadVariable {
            variable: written,
            address,
        } => *written == variable || expression_uses(address, variable),
        IRInst::StoreVariable {
            address,
            variable: read,
        } => *read == variable || expression_uses(address, variable),
        IRInst::Return(Some(value)) | IRInst::Jump(value) => expression_uses(value, variable),
        IRInst::If { condition, .. } => expression_uses(condition, variable),
        IRInst::While { condition, .. } => match condition {
            LoopCondition::Before { expression, .. } | LoopCondition::After { expression, .. } => {
                expression_uses(expression, variable)
            }
        },
        IRInst::CallSynthetic { arguments, .. } => arguments
            .iter()
            .any(|argument| expression_uses(argument, variable)),
        IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::Break
        | IRInst::Continue
        | IRInst::ContinueLoop(_)
        | IRInst::End => false,
    }
}

fn initial_value(instr: &IRInst, variable: VariableId) -> Option<IRExpr> {
    let value = match instr {
        IRInst::AssignVariable {
            variable: written,
            value,
        } if *written == variable => value.clone(),
        IRInst::Assign {
            dest: IRExpr::Variable(written),
            src,
        } if *written == variable => src.clone(),
        IRInst::LoadVariable {
            variable: written,
            address,
        } if *written == variable => IRExpr::Deref(Box::new(address.clone())),
        _ => return None,
    };
    (!expression_uses(&value, variable)).then_some(value)
}

fn collect_instruction(
    instr: &IRInst,
    index: usize,
    scope: &mut Vec<Step>,
    variable: VariableId,
    uses: &mut Vec<Use>,
) {
    if direct_use(instr, variable) {
        uses.push(Use {
            scope: scope.clone(),
            index,
            starts_with_write: initial_value(instr, variable).is_some(),
        });
    }
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            scope.push(Step {
                index,
                child: Child::Then,
            });
            for (index, instr) in then_branch.iter().enumerate() {
                collect_instruction(instr, index, scope, variable, uses);
            }
            scope.last_mut().unwrap().child = Child::Else;
            for (index, instr) in else_branch.iter().enumerate() {
                collect_instruction(instr, index, scope, variable, uses);
            }
            scope.pop();
        }
        IRInst::While { body, .. } => {
            scope.push(Step {
                index,
                child: Child::Loop,
            });
            for (index, (_, instr)) in body.iter().enumerate() {
                collect_instruction(instr, index, scope, variable, uses);
            }
            scope.pop();
        }
        _ => {}
    }
}

fn collect_uses(function: &SyntheticFunction, variable: VariableId) -> Vec<Use> {
    let mut uses = Vec::new();
    let mut scope = Vec::new();
    for (index, (_, instr)) in function.body.iter().enumerate() {
        collect_instruction(instr, index, &mut scope, variable, &mut uses);
    }
    uses
}

fn common_scope(uses: &[Use]) -> Vec<Step> {
    let mut scope = uses[0].scope.clone();
    for site in &uses[1..] {
        let common = scope
            .iter()
            .zip(&site.scope)
            .take_while(|(left, right)| left == right)
            .count();
        scope.truncate(common);
    }
    scope
}

fn first_use(uses: &[Use], scope: &[Step]) -> usize {
    uses.iter()
        .map(|site| {
            if site.scope.len() == scope.len() {
                site.index
            } else {
                site.scope[scope.len()].index
            }
        })
        .min()
        .unwrap()
}

fn collect_declarations(
    instr: &IRInst,
    index: usize,
    scope: &mut Vec<Step>,
    declarations: &mut HashMap<VariableId, (VariableType, Vec<Step>)>,
) {
    match instr {
        IRInst::DeclareVariable { variable, ty } => {
            declarations
                .entry(*variable)
                .or_insert((*ty, scope.clone()));
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            scope.push(Step {
                index,
                child: Child::Then,
            });
            for (index, instr) in then_branch.iter().enumerate() {
                collect_declarations(instr, index, scope, declarations);
            }
            scope.last_mut().unwrap().child = Child::Else;
            for (index, instr) in else_branch.iter().enumerate() {
                collect_declarations(instr, index, scope, declarations);
            }
            scope.pop();
        }
        IRInst::While { body, .. } => {
            scope.push(Step {
                index,
                child: Child::Loop,
            });
            for (index, (_, instr)) in body.iter().enumerate() {
                collect_declarations(instr, index, scope, declarations);
            }
            scope.pop();
        }
        _ => {}
    }
}

fn remove_from_instruction(instr: &mut IRInst, variable: VariableId) {
    match instr {
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            remove_from_branch(then_branch, variable);
            remove_from_branch(else_branch, variable);
        }
        IRInst::While { body, .. } => remove_from_body(body, variable),
        _ => {}
    }
}

fn declaration_of(instr: &IRInst, variable: VariableId) -> bool {
    matches!(instr, IRInst::DeclareVariable { variable: found, .. } if *found == variable)
}

fn remove_from_branch(branch: &mut Vec<IRInst>, variable: VariableId) {
    branch.retain(|instr| !declaration_of(instr, variable));
    for instr in branch {
        remove_from_instruction(instr, variable);
    }
}

fn remove_from_body(body: &mut Vec<(usize, IRInst)>, variable: VariableId) {
    body.retain(|(_, instr)| !declaration_of(instr, variable));
    for (_, instr) in body {
        remove_from_instruction(instr, variable);
    }
}

fn combine(instr: &mut IRInst, variable: VariableId, ty: VariableType) -> bool {
    let Some(value) = initial_value(instr, variable) else {
        return false;
    };
    *instr = IRInst::DeclareAndAssignVariable {
        variable,
        ty,
        value,
    };
    true
}

fn place_in_instruction(
    instr: &mut IRInst,
    step: Step,
    rest: &[Step],
    index: usize,
    variable: VariableId,
    ty: VariableType,
) {
    match (instr, step.child) {
        (IRInst::If { then_branch, .. }, Child::Then) => {
            place_in_branch(then_branch, rest, index, variable, ty)
        }
        (IRInst::If { else_branch, .. }, Child::Else) => {
            place_in_branch(else_branch, rest, index, variable, ty)
        }
        (IRInst::While { body, .. }, Child::Loop) => place_in_body(body, rest, index, variable, ty),
        _ => unreachable!("scope path must point to a structured instruction"),
    }
}

fn place_in_branch(
    branch: &mut Vec<IRInst>,
    path: &[Step],
    index: usize,
    variable: VariableId,
    ty: VariableType,
) {
    if let Some((step, rest)) = path.split_first() {
        place_in_instruction(&mut branch[step.index], *step, rest, index, variable, ty);
    } else if !combine(&mut branch[index], variable, ty) {
        branch.insert(index, IRInst::DeclareVariable { variable, ty });
    }
}

fn place_in_body(
    body: &mut Vec<(usize, IRInst)>,
    path: &[Step],
    index: usize,
    variable: VariableId,
    ty: VariableType,
) {
    if let Some((step, rest)) = path.split_first() {
        place_in_instruction(&mut body[step.index].1, *step, rest, index, variable, ty);
    } else if !combine(&mut body[index].1, variable, ty) {
        let offset = body[index].0;
        body.insert(index, (offset, IRInst::DeclareVariable { variable, ty }));
    }
}

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        let mut declarations = HashMap::new();
        for (index, (_, instr)) in function.body.iter().enumerate() {
            collect_declarations(instr, index, &mut Vec::new(), &mut declarations);
        }
        let parameters: HashSet<_> = function
            .parameters
            .iter()
            .filter_map(|parameter| match parameter {
                Parameter::Slot { variable, .. } => Some(*variable),
                Parameter::Argument { .. } => None,
            })
            .collect();
        let mut declarations = declarations.into_iter().collect::<Vec<_>>();
        declarations.sort_by_key(|(variable, _)| (variable.owner.id, variable.id));
        for (variable, (ty, _)) in declarations {
            let uses = collect_uses(function, variable);
            if parameters.contains(&variable) || uses.is_empty() {
                continue;
            }
            let mut current_declarations = HashMap::new();
            for (index, (_, instr)) in function.body.iter().enumerate() {
                collect_declarations(instr, index, &mut Vec::new(), &mut current_declarations);
            }
            let original_scope = &current_declarations[&variable].1;
            let scope = common_scope(&uses);
            let first = first_use(&uses, &scope);
            let starts_with_write = uses
                .iter()
                .any(|site| site.scope == scope && site.index == first && site.starts_with_write);
            let loop_limit = if starts_with_write {
                None
            } else {
                // A declaration inside a newly entered loop creates a fresh
                // binding on each iteration. Keep loop-carried values outside.
                scope.iter().enumerate().find_map(|(index, step)| {
                    (step.child == Child::Loop && original_scope.get(index) != Some(step))
                        .then_some(index)
                })
            };
            remove_from_body(&mut function.body, variable);
            let uses = collect_uses(function, variable);
            let mut scope = common_scope(&uses);
            if let Some(loop_index) = loop_limit {
                scope.truncate(loop_index);
            }
            let index = first_use(&uses, &scope);
            place_in_body(&mut function.body, &scope, index, variable, ty);
        }
    }
}
