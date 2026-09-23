use std::collections::HashSet;

use iced_x86::Register;

use super::ir::{IRExpr, IRInst, Program, SyntheticFunction};

// A 32-bit GPR write zero-extends to the full 64-bit register in x86-64.
// Tracking the full register also makes reads through differently sized aliases agree.
fn written_register(register: Register) -> Option<Register> {
    (register.is_gpr32() || register == register.full_register()).then(|| register.full_register())
}

fn read_expr(expr: &IRExpr, defined: &HashSet<Register>, required: &mut HashSet<Register>) {
    match expr {
        IRExpr::Reg(register) => {
            let register = register.full_register();
            if !defined.contains(&register) {
                required.insert(register);
            }
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
    parameters: &[Vec<Register>],
    defined: &mut HashSet<Register>,
    required: &mut HashSet<Register>,
) {
    match instr {
        IRInst::Assign { dest, src } => {
            read_expr(src, defined, required);
            match dest {
                IRExpr::Reg(register) => {
                    if let Some(register) = written_register(*register) {
                        defined.insert(register);
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
            for register in &parameters[function.id] {
                if !defined.contains(register) {
                    required.insert(*register);
                }
            }
        }
        IRInst::ClearFlags { .. }
        | IRInst::Return(None)
        | IRInst::DeclareVariable { .. }
        | IRInst::End => {}
    }
}

fn required_registers(function: &SyntheticFunction, parameters: &[Vec<Register>]) -> Vec<Register> {
    let mut defined = HashSet::new();
    let mut required = HashSet::new();
    for (_, instr) in &function.body {
        read_inst(instr, parameters, &mut defined, &mut required);
    }
    let mut required: Vec<_> = required.into_iter().collect();
    required.sort();
    required
}

fn fill_calls(instr: &mut IRInst, parameters: &[Vec<Register>]) {
    match instr {
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            *arguments = parameters[function.id]
                .iter()
                .copied()
                .map(IRExpr::Reg)
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
    let mut parameters = vec![Vec::new(); program.functions.len()];
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
        function.parameters = registers.clone();
        for (_, instr) in &mut function.body {
            fill_calls(instr, &parameters);
        }
    }
    program
}
