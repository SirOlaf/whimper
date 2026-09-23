//! A readable, TypeScript-like view of tier 1 for manual debugging.

use std::fmt::Write;

use crate::irt0::ir::NativeFlag;

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, Program, SyntheticFunctionId, VariableId, VariableType,
};

fn function_name(id: SyntheticFunctionId) -> String {
    format!("fn_{}", id.id)
}

fn variable_name(id: VariableId) -> String {
    format!("v{}", id.id)
}

fn flags(flags: &std::collections::HashSet<NativeFlag>) -> String {
    let mut names: Vec<_> = flags.iter().map(|flag| format!("{flag:?}")).collect();
    names.sort();
    names
        .into_iter()
        .map(|name| format!("\"{name}\""))
        .collect::<Vec<_>>()
        .join(", ")
}

// Higher numbers bind more tightly. The levels follow TypeScript operators
// used below, so an expression keeps its IR grouping when printed.
fn precedence(expr: &IRExpr) -> u8 {
    match expr {
        IRExpr::Or(..) => 1,
        IRExpr::BinOp {
            kind: IRBinOpKind::And,
            ..
        } => 2,
        IRExpr::Eq(..) => 3,
        IRExpr::BinOp {
            kind: IRBinOpKind::Shl,
            ..
        } => 4,
        IRExpr::BinOp { .. } => 5,
        IRExpr::Not(..) => 6,
        _ => 7,
    }
}

fn expression(expr: &IRExpr, parent_precedence: u8) -> String {
    let own_precedence = precedence(expr);
    let rendered = match expr {
        IRExpr::BinOp { kind, lhs, rhs } => {
            let operator = match kind {
                IRBinOpKind::Add => "+",
                IRBinOpKind::Sub => "-",
                IRBinOpKind::Shl => "<<",
                IRBinOpKind::And => "&",
            };
            format!(
                "{} {operator} {}",
                expression(lhs, own_precedence),
                expression(rhs, own_precedence + 1)
            )
        }
        IRExpr::Deref(address) => format!("memory[{}]", expression(address, 0)),
        IRExpr::Reg(reg) => format!("{reg:?}"),
        IRExpr::Flag(flag) => format!("flags.{flag:?}"),
        IRExpr::CU8(value) => format!("0x{value:x}"),
        IRExpr::CU32(value) => format!("0x{value:x}"),
        IRExpr::CU64(value) => format!("0x{value:x}"),
        IRExpr::Variable(variable) => variable_name(*variable),
        IRExpr::Bool(value) => value.to_string(),
        IRExpr::Eq(lhs, rhs) => format!(
            "{} === {}",
            expression(lhs, own_precedence),
            expression(rhs, own_precedence + 1)
        ),
        IRExpr::UnsignedLt(lhs, rhs) => {
            format!("unsignedLt({}, {})", expression(lhs, 0), expression(rhs, 0))
        }
        IRExpr::Or(lhs, rhs) => format!(
            "{} || {}",
            expression(lhs, own_precedence),
            expression(rhs, own_precedence + 1)
        ),
        IRExpr::Not(inner) => format!("!{}", expression(inner, own_precedence)),
    };
    if own_precedence < parent_precedence {
        format!("({rendered})")
    } else {
        rendered
    }
}

fn instruction(output: &mut String, instr: &IRInst, indent: usize) {
    let padding = "    ".repeat(indent);
    match instr {
        IRInst::Assign { dest, src } => {
            writeln!(
                output,
                "{padding}{} = {};",
                expression(dest, 0),
                expression(src, 0)
            )
            .unwrap();
        }
        IRInst::SetFlagsFrom { flags: set, expr } => {
            writeln!(
                output,
                "{padding}setFlagsFrom([{}], {});",
                flags(set),
                expression(expr, 0)
            )
            .unwrap();
        }
        IRInst::ClearFlags { flags: set } => {
            writeln!(output, "{padding}clearFlags([{}]);", flags(set)).unwrap();
        }
        IRInst::Return(Some(value)) => {
            writeln!(output, "{padding}return {};", expression(value, 0)).unwrap();
        }
        IRInst::Return(None) => {
            writeln!(output, "{padding}return;").unwrap();
        }
        IRInst::DeclareVariable { variable, ty } => {
            let ty = match ty {
                VariableType::Bool => "boolean",
            };
            writeln!(output, "{padding}let {}: {ty};", variable_name(*variable)).unwrap();
        }
        IRInst::AssignVariable { variable, value } => {
            writeln!(
                output,
                "{padding}{} = {};",
                variable_name(*variable),
                expression(value, 0)
            )
            .unwrap();
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            writeln!(output, "{padding}if ({}) {{", expression(condition, 0)).unwrap();
            instruction(output, then_branch, indent + 1);
            writeln!(output, "{padding}}} else {{").unwrap();
            instruction(output, else_branch, indent + 1);
            writeln!(output, "{padding}}}").unwrap();
        }
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            let arguments = arguments
                .iter()
                .map(|argument| expression(argument, 0))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(
                output,
                "{padding}return {}({arguments});",
                function_name(*function)
            )
            .unwrap();
        }
        IRInst::Jump(target) => {
            writeln!(output, "{padding}jump({});", expression(target, 0)).unwrap();
        }
        IRInst::End => {
            writeln!(output, "{padding}end();").unwrap();
        }
    }
}

/// Render the complete tier 1 program, including its entry and source offsets.
pub fn render(program: &Program) -> String {
    let mut output = String::new();
    match program.entry {
        Some(entry) => writeln!(output, "// entry: {}", function_name(entry)).unwrap(),
        None => writeln!(output, "// entry: none").unwrap(),
    }

    for (index, function) in program.functions.iter().enumerate() {
        let id = SyntheticFunctionId { id: index };
        let parameters = function
            .parameters
            .iter()
            .map(|register| format!("{register:?}"))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            output,
            "\nfunction {}({parameters}) {{ // 0x{:x}",
            function_name(id),
            function.entry_offset
        )
        .unwrap();
        if !function.external_flags.is_empty() {
            writeln!(
                output,
                "    // external flags: [{}]",
                flags(&function.external_flags)
            )
            .unwrap();
        }
        let mut previous_offset = Some(function.entry_offset);
        for (offset, instr) in &function.body {
            if previous_offset != Some(*offset) {
                writeln!(output, "    // 0x{offset:x}").unwrap();
                previous_offset = Some(*offset);
            }
            instruction(&mut output, instr, 1);
        }
        writeln!(output, "}}").unwrap();
    }
    output
}
