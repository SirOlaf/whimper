//! Infer a likely integer return before partition parameters are collected.
//! A shared RET must receive the value from all of its predecessors, even when
//! those predecessors wrote different slots in the same register alias.

use iced_x86::Register;

use super::ir::{IRExpr, IRInst, Program};

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Unreachable,
    Unknown,
    Register(Register),
}

impl State {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unreachable, state) | (state, Self::Unreachable) => state,
            (Self::Register(a), Self::Register(b)) if a == b => Self::Register(a),
            _ => Self::Unknown,
        }
    }
}

fn write(instr: &IRInst, state: State) -> State {
    if state == State::Unreachable {
        return state;
    }
    match instr {
        IRInst::Assign {
            dest: IRExpr::Reg(register),
            ..
        } if register.full_register() == Register::RAX => {
            if matches!(register, Register::EAX | Register::RAX) {
                State::Register(*register)
            } else {
                // A partial write alone does not establish a return width.
                State::Unknown
            }
        }
        _ => state,
    }
}

fn transfers(instr: &IRInst, state: State, edges: &mut Vec<(usize, State)>) {
    match instr {
        IRInst::CallSynthetic { function, .. } => edges.push((function.id, state)),
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            transfers(then_branch, state, edges);
            transfers(else_branch, state, edges);
        }
        _ => {}
    }
}

fn rewrite(instr: &mut IRInst, state: State) {
    match instr {
        IRInst::Return(value @ None) => {
            if let State::Register(register) = state {
                *value = Some(IRExpr::Reg(register));
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            rewrite(then_branch, state);
            rewrite(else_branch, state);
        }
        _ => {}
    }
}

pub fn run(program: &mut Program) {
    let Some(entry) = program.entry else { return };
    let mut incoming = vec![State::Unreachable; program.functions.len()];
    incoming[entry.id] = State::Unknown;
    let mut pending = vec![entry.id];
    while let Some(id) = pending.pop() {
        let mut state = incoming[id];
        let mut edges = Vec::new();
        for (_, instr) in &program.functions[id].body {
            state = write(instr, state);
            transfers(instr, state, &mut edges);
        }
        for (target, state) in edges {
            let joined = incoming[target].join(state);
            if incoming[target] != joined {
                incoming[target] = joined;
                pending.push(target);
            }
        }
    }
    for (function, mut state) in program.functions.iter_mut().zip(incoming) {
        for (_, instr) in &mut function.body {
            state = write(instr, state);
            rewrite(instr, state);
        }
    }
}
