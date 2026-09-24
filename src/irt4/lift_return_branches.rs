//! Turn a returning arm into an early exit and lift the other arm into its block.

use super::ir::{IRInst, Program};

#[derive(Clone, Copy)]
struct Exits {
    falls_through: bool,
    exits_without_return: bool,
}

fn exits(body: &[IRInst]) -> Exits {
    let mut result = Exits {
        falls_through: true,
        exits_without_return: false,
    };
    for instr in body {
        if !result.falls_through {
            break;
        }
        let next = match instr {
            IRInst::Return(_) => Exits {
                falls_through: false,
                exits_without_return: false,
            },
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_exits = exits(then_branch);
                let else_exits = exits(else_branch);
                Exits {
                    falls_through: then_exits.falls_through || else_exits.falls_through,
                    exits_without_return: then_exits.exits_without_return
                        || else_exits.exits_without_return,
                }
            }
            // A loop can run forever or leave through a break/continue. Proving
            // its return behavior needs more than this local branch rewrite.
            IRInst::While { .. }
            | IRInst::Break
            | IRInst::Continue
            | IRInst::ContinueLoop(_)
            | IRInst::CallSynthetic { .. }
            | IRInst::Jump(_)
            | IRInst::End => Exits {
                falls_through: false,
                exits_without_return: true,
            },
            _ => continue,
        };
        result.exits_without_return |= next.exits_without_return;
        result.falls_through = next.falls_through;
    }
    result
}

fn always_returns(body: &[IRInst]) -> bool {
    let exits = exits(body);
    !exits.falls_through && !exits.exits_without_return
}

fn size(body: &[IRInst]) -> usize {
    body.iter()
        .map(|instr| match instr {
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => 1 + size(then_branch) + size(else_branch),
            IRInst::While { body, .. } => {
                1 + body
                    .iter()
                    .map(|(_, instr)| size(std::slice::from_ref(instr)))
                    .sum::<usize>()
            }
            _ => 1,
        })
        .sum()
}

fn rewrite_instruction(instr: IRInst) -> Vec<IRInst> {
    match instr {
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let then_branch = rewrite_branch(then_branch);
            let else_branch = rewrite_branch(else_branch);
            let then_returns = always_returns(&then_branch);
            let else_returns = always_returns(&else_branch);
            // Keep a direct two-return expression intact for later recovery.
            let direct_returns = matches!(then_branch.as_slice(), [IRInst::Return(_)])
                && matches!(else_branch.as_slice(), [IRInst::Return(_)]);
            let guard_then = match (then_returns, else_returns) {
                (true, false) => Some(true),
                (false, true) => Some(false),
                (true, true) if !direct_returns => Some(size(&then_branch) <= size(&else_branch)),
                _ => None,
            };
            match guard_then {
                Some(true) => {
                    let mut result = vec![IRInst::If {
                        condition,
                        then_branch,
                        else_branch: Vec::new(),
                    }];
                    result.extend(else_branch);
                    result
                }
                Some(false) => {
                    let mut result = vec![IRInst::If {
                        condition: super::negate(condition),
                        then_branch: else_branch,
                        else_branch: Vec::new(),
                    }];
                    result.extend(then_branch);
                    result
                }
                None => vec![IRInst::If {
                    condition,
                    then_branch,
                    else_branch,
                }],
            }
        }
        IRInst::While {
            label,
            entry_offset,
            condition,
            body,
        } => vec![IRInst::While {
            label,
            entry_offset,
            condition,
            body: rewrite_body(body),
        }],
        other => vec![other],
    }
}

fn rewrite_branch(branch: Vec<IRInst>) -> Vec<IRInst> {
    branch.into_iter().flat_map(rewrite_instruction).collect()
}

fn rewrite_body(body: Vec<(usize, IRInst)>) -> Vec<(usize, IRInst)> {
    body.into_iter()
        .flat_map(|(offset, instr)| {
            rewrite_instruction(instr)
                .into_iter()
                .map(move |instr| (offset, instr))
        })
        .collect()
}

pub fn run(program: &mut Program) {
    for function in &mut program.functions {
        function.body = rewrite_body(std::mem::take(&mut function.body));
    }
}
