//! A readable view of tier 3 for manual debugging.

use std::fmt::Write;

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, Parameter, Program, SyntheticFunctionId, VariableId, VariableType,
};

fn function_name(id: SyntheticFunctionId) -> String {
    format!("fn_{}", id.id)
}

fn variable_name(id: VariableId) -> String {
    format!("v{}", id.id)
}

// Higher numbers bind more tightly. The levels follow TypeScript operators
// used below, so an expression keeps its IR grouping when printed.
fn precedence(expr: &IRExpr) -> u8 {
    match expr {
        IRExpr::BinOp {
            kind: IRBinOpKind::Or,
            ..
        } => 1,
        IRExpr::BinOp {
            kind: IRBinOpKind::And,
            ..
        } => 2,
        IRExpr::BinOp {
            kind: IRBinOpKind::Eq,
            ..
        } => 3,
        IRExpr::BinOp {
            kind: IRBinOpKind::Shl,
            ..
        } => 4,
        IRExpr::BinOp {
            kind: IRBinOpKind::UnsignedLt | IRBinOpKind::SignedGt,
            ..
        } => 7,
        IRExpr::BinOp { .. } => 5,
        IRExpr::Not(..) | IRExpr::Deref(..) | IRExpr::CastUnknownPtr { .. } => 6,
        _ => 7,
    }
}

fn binary_operand(expr: &IRExpr, parent_precedence: u8) -> String {
    if matches!(expr, IRExpr::BinOp { .. }) {
        format!("({})", expression(expr, 0))
    } else {
        expression(expr, parent_precedence)
    }
}

fn expression(expr: &IRExpr, parent_precedence: u8) -> String {
    let own_precedence = precedence(expr);
    let rendered = match expr {
        IRExpr::BinOp { kind, lhs, rhs } => {
            let operator = match kind {
                IRBinOpKind::Add => Some("+"),
                IRBinOpKind::Sub => Some("-"),
                IRBinOpKind::Shl => Some("<<"),
                IRBinOpKind::And => Some("&"),
                IRBinOpKind::Or => Some("||"),
                IRBinOpKind::Eq => Some("==="),
                IRBinOpKind::SignedGt => Some(">"),
                IRBinOpKind::UnsignedLt => None,
            };
            match operator {
                Some(operator) => format!(
                    "{} {operator} {}",
                    binary_operand(lhs, own_precedence),
                    binary_operand(rhs, own_precedence + 1)
                ),
                None => format!(
                    "unsignedLt({}, {})",
                    binary_operand(lhs, 0),
                    binary_operand(rhs, 0)
                ),
            }
        }
        IRExpr::Deref(address) => format!("*({})", expression(address, 0)),
        IRExpr::CastUnknownPtr { address, size } => match size {
            Some(size) => format!("(Unknown<{size}>*)({})", expression(address, 0)),
            None => format!("(Unknown*)({})", expression(address, 0)),
        },
        IRExpr::Argument(ordinal) => format!("arg{ordinal}"),
        IRExpr::ExtractBytes {
            value,
            offset,
            size,
        } => format!("extractBytes<{offset}, {size}>({})", expression(value, 0)),
        IRExpr::ZeroExtend { value, size } => {
            format!("zeroExtend<{size}>({})", expression(value, 0))
        }
        IRExpr::ReplaceBytes {
            original,
            value,
            offset,
            size,
        } => format!(
            "replaceBytes<{offset}, {size}>({}, {})",
            expression(original, 0),
            expression(value, 0)
        ),
        IRExpr::CU8(value) => format!("0x{value:x}"),
        IRExpr::CU32(value) => format!("0x{value:x}"),
        IRExpr::CU64(value) => format!("0x{value:x}"),
        IRExpr::Variable(variable) => variable_name(*variable),
        IRExpr::Bool(value) => value.to_string(),
        IRExpr::Not(inner) => format!("!{}", binary_operand(inner, own_precedence)),
    };
    if own_precedence < parent_precedence {
        format!("({rendered})")
    } else {
        rendered
    }
}

fn instruction(output: &mut String, instr: &IRInst, indent: usize, address_comments: bool) {
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
        IRInst::Return(Some(value)) => {
            writeln!(output, "{padding}return {};", expression(value, 0)).unwrap();
        }
        IRInst::Return(None) => {
            writeln!(output, "{padding}return;").unwrap();
        }
        IRInst::DeclareVariable { variable, ty } => {
            let ty = match ty {
                VariableType::Unknown(Some(size)) => format!("Unknown<{size}>"),
                VariableType::Unknown(None) => "Unknown".to_string(),
                VariableType::Register(register) => format!("Register<{register:?}>"),
                VariableType::Bool => "Bool".to_string(),
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
        IRInst::LoadVariable { variable, address } => {
            writeln!(
                output,
                "{padding}{} = *({});",
                variable_name(*variable),
                expression(address, 0)
            )
            .unwrap();
        }
        IRInst::StoreVariable { address, variable } => {
            writeln!(
                output,
                "{padding}*({}) = {};",
                expression(address, 0),
                variable_name(*variable)
            )
            .unwrap();
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            writeln!(output, "{padding}if ({}) {{", expression(condition, 0)).unwrap();
            for instr in then_branch {
                instruction(output, instr, indent + 1, address_comments);
            }
            if !else_branch.is_empty() {
                writeln!(output, "{padding}}} else {{").unwrap();
                for instr in else_branch {
                    instruction(output, instr, indent + 1, address_comments);
                }
            }
            writeln!(output, "{padding}}}").unwrap();
        }
        IRInst::Loop {
            label,
            entry_offset,
            body,
        } => {
            let label = label.map_or_else(String::new, |label| format!("loop_{}: ", label.id));
            writeln!(output, "{padding}{label}loop {{").unwrap();
            let nested_padding = "    ".repeat(indent + 1);
            let mut previous_offset = Some(*entry_offset);
            for (offset, instr) in body {
                if address_comments && previous_offset != Some(*offset) {
                    writeln!(output, "{nested_padding}// 0x{offset:x}").unwrap();
                    previous_offset = Some(*offset);
                }
                instruction(output, instr, indent + 1, address_comments);
            }
            writeln!(output, "{padding}}}").unwrap();
        }
        IRInst::Continue => {
            writeln!(output, "{padding}continue;").unwrap();
        }
        IRInst::ContinueLoop(label) => {
            writeln!(output, "{padding}continue loop_{};", label.id).unwrap();
        }
        IRInst::Break => {
            writeln!(output, "{padding}break;").unwrap();
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

/// Render the complete tier 3 program, optionally including source address comments.
pub fn render(program: &Program, address_comments: bool) -> String {
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
            .map(|parameter| match parameter {
                Parameter::Native { ordinal, register } => {
                    format!("arg{ordinal}: Register<{register:?}>")
                }
                Parameter::Slot { variable, register } => {
                    format!("{}: Register<{register:?}>", variable_name(*variable))
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        write!(output, "\nfunction {}({parameters}) {{", function_name(id)).unwrap();
        if address_comments {
            write!(output, " // 0x{:x}", function.entry_offset).unwrap();
        }
        writeln!(output).unwrap();
        let mut previous_offset = Some(function.entry_offset);
        for (offset, instr) in &function.body {
            if address_comments && previous_offset != Some(*offset) {
                writeln!(output, "    // 0x{offset:x}").unwrap();
                previous_offset = Some(*offset);
            }
            instruction(&mut output, instr, 1, address_comments);
        }
        writeln!(output, "}}").unwrap();
    }
    output
}
