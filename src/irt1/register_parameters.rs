use std::collections::{HashMap, HashSet};

use iced_x86::Register;

use super::ir::{IRExpr, IRInst, Parameter, Program, SyntheticFunction};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Location {
    Register(Register),
    Stack(i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Requirement {
    location: Location,
    size: usize,
}

fn register_offset(register: Register) -> usize {
    match register {
        Register::AH | Register::BH | Register::CH | Register::DH => 1,
        _ => 0,
    }
}

fn stack_base(offset: i64, size: usize) -> i64 {
    let base = offset.div_euclid(8) * 8;
    assert!(
        offset + size as i64 <= base + 8,
        "stack access crosses an eight-byte cell"
    );
    base
}

fn stack_ranges_expr(expr: &IRExpr, ranges: &mut Vec<(i64, usize)>) {
    match expr {
        IRExpr::Stack { offset, size } => ranges.push((*offset, *size)),
        IRExpr::BinOp { lhs, rhs, .. } => {
            stack_ranges_expr(lhs, ranges);
            stack_ranges_expr(rhs, ranges);
        }
        IRExpr::Deref { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::SignExtend { value: inner, .. }
        | IRExpr::Not(inner) => stack_ranges_expr(inner, ranges),
        _ => {}
    }
}

fn stack_ranges_inst(instr: &IRInst, ranges: &mut Vec<(i64, usize)>) {
    match instr {
        IRInst::Assign { dest, src } => {
            stack_ranges_expr(dest, ranges);
            stack_ranges_expr(src, ranges);
        }
        IRInst::SetFlagsFrom { expr, .. }
        | IRInst::Return(Some(expr))
        | IRInst::Jump(expr)
        | IRInst::AssignVariable { value: expr, .. } => stack_ranges_expr(expr, ranges),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            stack_ranges_expr(condition, ranges);
            stack_ranges_inst(then_branch, ranges);
            stack_ranges_inst(else_branch, ranges);
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for argument in arguments {
                stack_ranges_expr(argument, ranges);
            }
        }
        _ => {}
    }
}

fn require_bytes(
    location: Location,
    offset: usize,
    size: usize,
    defined: &HashMap<Location, HashSet<usize>>,
    required: &mut HashMap<Location, usize>,
    stack_widths: &HashMap<i64, usize>,
) {
    let known = defined.get(&location);
    for byte in offset..offset + size {
        if !known.is_some_and(|known| known.contains(&byte)) {
            let extent = if let Location::Stack(offset) = location {
                stack_widths[&offset]
            } else {
                byte + 1
            };
            required
                .entry(location)
                .and_modify(|size| *size = (*size).max(extent))
                .or_insert(extent);
        }
    }
}

fn read_expr(
    expr: &IRExpr,
    defined: &HashMap<Location, HashSet<usize>>,
    required: &mut HashMap<Location, usize>,
    stack_widths: &HashMap<i64, usize>,
) {
    match expr {
        IRExpr::Reg(register) => require_bytes(
            Location::Register(register.full_register()),
            register_offset(*register),
            register.size(),
            defined,
            required,
            stack_widths,
        ),
        IRExpr::Stack { offset, size } => {
            let base = stack_base(*offset, *size);
            require_bytes(
                Location::Stack(base),
                (*offset - base) as usize,
                *size,
                defined,
                required,
                stack_widths,
            );
        }
        IRExpr::BinOp { lhs, rhs, .. } => {
            read_expr(lhs, defined, required, stack_widths);
            read_expr(rhs, defined, required, stack_widths);
        }
        IRExpr::Deref { address: inner, .. }
        | IRExpr::ExtractBytes { value: inner, .. }
        | IRExpr::ZeroExtend { value: inner, .. }
        | IRExpr::SignExtend { value: inner, .. }
        | IRExpr::Not(inner) => read_expr(inner, defined, required, stack_widths),
        IRExpr::Flag(_)
        | IRExpr::CU8(_)
        | IRExpr::CU32(_)
        | IRExpr::CU64(_)
        | IRExpr::Variable(_)
        | IRExpr::Bool(_) => {}
    }
}

fn define(
    location: Location,
    offset: usize,
    size: usize,
    defined: &mut HashMap<Location, HashSet<usize>>,
) {
    let bytes = defined.entry(location).or_default();
    for byte in offset..offset + size {
        bytes.insert(byte);
    }
}

fn read_inst(
    instr: &IRInst,
    parameters: &[Vec<Requirement>],
    defined: &mut HashMap<Location, HashSet<usize>>,
    required: &mut HashMap<Location, usize>,
    stack_widths: &HashMap<i64, usize>,
) {
    match instr {
        IRInst::Assign { dest, src } => {
            read_expr(src, defined, required, stack_widths);
            match dest {
                IRExpr::Reg(register) => {
                    let size = if register.is_gpr32() {
                        register.full_register().size()
                    } else {
                        register.size()
                    };
                    define(
                        Location::Register(register.full_register()),
                        register_offset(*register),
                        size,
                        defined,
                    );
                }
                IRExpr::Stack { offset, size } => {
                    let base = stack_base(*offset, *size);
                    // A partial write preserves the rest of the cell.
                    if *size < stack_widths[&base] {
                        for byte in 0..stack_widths[&base] {
                            if byte < (*offset - base) as usize
                                || byte >= (*offset - base) as usize + *size
                            {
                                require_bytes(
                                    Location::Stack(base),
                                    byte,
                                    1,
                                    defined,
                                    required,
                                    stack_widths,
                                );
                            }
                        }
                    }
                    define(
                        Location::Stack(base),
                        (*offset - base) as usize,
                        *size,
                        defined,
                    );
                }
                other => read_expr(other, defined, required, stack_widths),
            }
        }
        IRInst::SetFlagsFrom { expr, .. } | IRInst::Return(Some(expr)) | IRInst::Jump(expr) => {
            read_expr(expr, defined, required, stack_widths)
        }
        IRInst::AssignVariable { value, .. } => read_expr(value, defined, required, stack_widths),
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            read_expr(condition, defined, required, stack_widths);
            let mut then_defined = defined.clone();
            let mut else_defined = defined.clone();
            read_inst(
                then_branch,
                parameters,
                &mut then_defined,
                required,
                stack_widths,
            );
            read_inst(
                else_branch,
                parameters,
                &mut else_defined,
                required,
                stack_widths,
            );
        }
        IRInst::CallSynthetic { function, .. } => {
            for parameter in &parameters[function.id] {
                require_bytes(
                    parameter.location,
                    0,
                    parameter.size,
                    defined,
                    required,
                    stack_widths,
                );
            }
        }
        IRInst::InvalidateFlags { .. }
        | IRInst::ClearFlags { .. }
        | IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::End => {}
    }
}

fn required_values(
    function: &SyntheticFunction,
    parameters: &[Vec<Requirement>],
    stack_widths: &HashMap<i64, usize>,
) -> Vec<Requirement> {
    let mut defined = HashMap::new();
    let mut required = HashMap::new();
    for (_, instr) in &function.body {
        read_inst(instr, parameters, &mut defined, &mut required, stack_widths);
    }
    let mut required: Vec<_> = required
        .into_iter()
        .map(|(location, size)| Requirement { location, size })
        .collect();
    required.sort_by_key(|item| match item.location {
        Location::Register(register) => (0, register as i64),
        Location::Stack(offset) => (1, offset),
    });
    required
}

fn prefix_register(register: Register, size: usize) -> Register {
    Register::values()
        .find(|candidate| {
            candidate.full_register() == register
                && candidate.size() == size
                && register_offset(*candidate) == 0
        })
        .unwrap_or_else(|| panic!("no low {size}-byte alias for {register:?}"))
}

fn fill_calls(instr: &mut IRInst, parameters: &[Vec<Requirement>]) {
    match instr {
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            *arguments = parameters[function.id]
                .iter()
                .map(|parameter| match parameter.location {
                    Location::Register(register) => {
                        IRExpr::Reg(prefix_register(register, parameter.size))
                    }
                    Location::Stack(offset) => IRExpr::Stack {
                        offset,
                        size: parameter.size,
                    },
                })
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

pub fn tr(mut program: Program) -> Program {
    let mut stack_widths = HashMap::new();
    for function in &program.functions {
        for (_, instr) in &function.body {
            let mut ranges = Vec::new();
            stack_ranges_inst(instr, &mut ranges);
            for (offset, size) in ranges {
                let base = stack_base(offset, size);
                let extent = (offset - base) as usize + size;
                stack_widths
                    .entry(base)
                    .and_modify(|width: &mut usize| *width = (*width).max(extent))
                    .or_insert(extent);
            }
        }
    }
    program.stack_widths = stack_widths.clone();
    let mut parameters = vec![Vec::<Requirement>::new(); program.functions.len()];
    loop {
        let next: Vec<_> = program
            .functions
            .iter()
            .map(|function| required_values(function, &parameters, &stack_widths))
            .collect();
        if next == parameters {
            break;
        }
        parameters = next;
    }
    for (function, required) in program.functions.iter_mut().zip(&parameters) {
        function.parameters = required
            .iter()
            .map(|parameter| match parameter.location {
                Location::Register(register) => {
                    Parameter::Register(prefix_register(register, parameter.size))
                }
                Location::Stack(offset) => Parameter::Stack {
                    offset,
                    size: parameter.size,
                },
            })
            .collect();
        for (_, instr) in &mut function.body {
            fill_calls(instr, &parameters);
        }
    }
    program
}
