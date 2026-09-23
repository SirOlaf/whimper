use std::collections::{HashMap, HashSet};

use iced_x86::Register;

use super::ir::{IRExpr, IRInst, Program, SyntheticFunction};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RegisterRequirement {
    register: Register,
    size: usize,
}

fn register_offset(register: Register) -> usize {
    match register {
        Register::AH | Register::BH | Register::CH | Register::DH => 1,
        _ => 0,
    }
}

fn require_bytes(
    register: Register,
    offset: usize,
    size: usize,
    defined: &HashMap<Register, HashSet<usize>>,
    required: &mut HashMap<Register, usize>,
) {
    let family = register.full_register();
    let defined = defined.get(&family);
    for byte in offset..offset + size {
        if !defined.is_some_and(|defined| defined.contains(&byte)) {
            required
                .entry(family)
                .and_modify(|extent| *extent = (*extent).max(byte + 1))
                .or_insert(byte + 1);
        }
    }
}

fn read_expr(
    expr: &IRExpr,
    defined: &HashMap<Register, HashSet<usize>>,
    required: &mut HashMap<Register, usize>,
) {
    match expr {
        IRExpr::Reg(register) => {
            require_bytes(
                *register,
                register_offset(*register),
                register.size(),
                defined,
                required,
            );
        }
        IRExpr::BinOp { lhs, rhs, .. }
        | IRExpr::Eq(lhs, rhs)
        | IRExpr::UnsignedLt(lhs, rhs)
        | IRExpr::Or(lhs, rhs) => {
            read_expr(lhs, defined, required);
            read_expr(rhs, defined, required);
        }
        IRExpr::Deref(inner) | IRExpr::Not(inner) => read_expr(inner, defined, required),
        IRExpr::Flag(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn read_inst(
    instr: &IRInst,
    parameters: &[Vec<RegisterRequirement>],
    defined: &mut HashMap<Register, HashSet<usize>>,
    required: &mut HashMap<Register, usize>,
) {
    match instr {
        IRInst::Assign { dest, src } => {
            read_expr(src, defined, required);
            match dest {
                IRExpr::Reg(register) => {
                    let family = register.full_register();
                    let size = if register.is_gpr32() {
                        family.size()
                    } else {
                        register.size()
                    };
                    let defined = defined.entry(family).or_default();
                    for byte in register_offset(*register)..register_offset(*register) + size {
                        defined.insert(byte);
                    }
                }
                // A memory destination reads its address, but does not define
                // any register. Other destinations are conservatively read.
                dest => read_expr(dest, defined, required),
            }
        }
        IRInst::SetFlagsFrom { expr, .. } | IRInst::Return(Some(expr)) | IRInst::Jump(expr) => {
            read_expr(expr, defined, required)
        }
        IRInst::AssignVariable { value, .. } => read_expr(value, defined, required),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            read_expr(condition, defined, required);
            let mut then_defined = defined.clone();
            let mut else_defined = defined.clone();
            read_inst(then_branch, parameters, &mut then_defined, required);
            read_inst(else_branch, parameters, &mut else_defined, required);
        }
        IRInst::CallSynthetic { function, .. } => {
            for parameter in &parameters[function.id] {
                require_bytes(parameter.register, 0, parameter.size, defined, required);
            }
        }
        IRInst::ClearFlags { .. }
        | IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::End => {}
    }
}

fn required_registers(
    function: &SyntheticFunction,
    parameters: &[Vec<RegisterRequirement>],
) -> Vec<RegisterRequirement> {
    let mut defined = HashMap::new();
    let mut required = HashMap::new();
    for (_, instr) in &function.body {
        read_inst(instr, parameters, &mut defined, &mut required);
    }
    let mut required: Vec<_> = required
        .into_iter()
        .map(|(register, size)| RegisterRequirement { register, size })
        .collect();
    required.sort_by_key(|parameter| parameter.register);
    required
}

fn fill_calls(instr: &mut IRInst, parameters: &[Vec<RegisterRequirement>]) {
    match instr {
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            *arguments = parameters[function.id]
                .iter()
                .map(|parameter| IRExpr::Reg(prefix_register(parameter.register, parameter.size)))
                .collect();
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            fill_calls(then_branch, parameters);
            fill_calls(else_branch, parameters);
        }
        _ => {}
    }
}

fn prefix_register(register: Register, size: usize) -> Register {
    // Use the low-prefix alias so its iced register size carries the argument
    // width. For example, an AH read needs AX to retain byte offset 1.
    Register::values()
        .find(|candidate| {
            candidate.full_register() == register
                && candidate.size() == size
                && register_offset(*candidate) == 0
        })
        .unwrap_or_else(|| panic!("no low {size}-byte alias for {register:?}"))
}

pub fn tr(mut program: Program) -> Program {
    let mut parameters = vec![Vec::<RegisterRequirement>::new(); program.functions.len()];
    // A call can require a register only needed by a deeper callee. Iterate
    // until those requirements have propagated through branches and loops.
    loop {
        let next: Vec<_> = program
            .functions
            .iter()
            .map(|function| required_registers(function, &parameters))
            .collect();
        if next == parameters {
            break;
        }
        parameters = next;
    }

    for (function, registers) in program.functions.iter_mut().zip(&parameters) {
        function.parameters = registers
            .iter()
            .map(|parameter| prefix_register(parameter.register, parameter.size))
            .collect();
        for (_, instr) in &mut function.body {
            fill_calls(instr, &parameters);
        }
    }
    program
}
