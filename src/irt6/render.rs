//! A readable view of tier 6 for manual debugging.

use std::{collections::HashMap, fmt::Write};

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, Parameter, Program, StructDefinition,
    SyntheticFunction, SyntheticFunctionId, VariableId, VariableType, field_address,
};

struct RenderTypes<'a> {
    arguments: HashMap<usize, VariableType>,
    variables: HashMap<VariableId, VariableType>,
    structs: &'a [StructDefinition],
}

impl<'a> RenderTypes<'a> {
    fn collect_instruction(&mut self, instr: &IRInst) {
        match instr {
            IRInst::DeclareVariable { variable, ty }
            | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
                self.variables.insert(*variable, ty.clone());
            }
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                for instr in then_branch.iter().chain(else_branch) {
                    self.collect_instruction(instr);
                }
            }
            IRInst::While { body, .. } => {
                for (_, instr) in body {
                    self.collect_instruction(instr);
                }
            }
            IRInst::ForEach {
                variable,
                element_type,
                body,
                ..
            } => {
                self.variables.insert(*variable, element_type.clone());
                for (_, instr) in body {
                    self.collect_instruction(instr);
                }
            }
            _ => {}
        }
    }

    fn from_function(function: &SyntheticFunction, structs: &'a [StructDefinition]) -> Self {
        let mut slots = Self {
            arguments: HashMap::new(),
            variables: HashMap::new(),
            structs,
        };
        for parameter in &function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    slots.arguments.insert(*ordinal, ty.clone());
                }
                Parameter::Slot { variable, ty } => {
                    slots.variables.insert(*variable, ty.clone());
                }
            }
        }
        for (_, instr) in &function.body {
            slots.collect_instruction(instr);
        }
        slots
    }

    fn direct_type(&self, expr: &IRExpr) -> Option<VariableType> {
        match expr {
            IRExpr::Argument(ordinal) => self.arguments.get(ordinal).cloned(),
            IRExpr::Variable(variable) => self.variables.get(variable).cloned(),
            _ => None,
        }
    }

    fn integer_type(&self, expr: &IRExpr) -> Option<super::ir::IntegerType> {
        use super::ir::IntegerType;
        match expr {
            IRExpr::Convert { target, .. } => Some(*target),
            IRExpr::CU8(_) => Some(IntegerType {
                size: 1,
                signed: false,
            }),
            IRExpr::CU32(_) => Some(IntegerType {
                size: 4,
                signed: false,
            }),
            IRExpr::CU64(_) => Some(IntegerType {
                size: 8,
                signed: false,
            }),
            _ => match self.direct_type(expr) {
                Some(VariableType::Integer(bits)) => Some(IntegerType {
                    size: bits / 8,
                    signed: true,
                }),
                Some(VariableType::UnsignedInteger(bits)) => Some(IntegerType {
                    size: bits / 8,
                    signed: false,
                }),
                _ => None,
            },
        }
    }

    fn integer_offset(&self, expr: &IRExpr) -> bool {
        if matches!(
            self.direct_type(expr),
            Some(VariableType::Integer(_) | VariableType::UnsignedInteger(_))
        ) {
            return true;
        }
        match expr {
            IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_) | IRExpr::Convert { .. } => true,
            IRExpr::BinOp {
                kind:
                    IRBinOpKind::Add | IRBinOpKind::Sub | IRBinOpKind::UnsignedMod | IRBinOpKind::Shl,
                lhs,
                rhs,
            } => self.integer_offset(lhs) && self.integer_offset(rhs),
            _ => false,
        }
    }

    fn pointer_address(&self, expr: &IRExpr) -> bool {
        if matches!(
            self.direct_type(expr),
            Some(VariableType::UnknownPointer | VariableType::Pointer(_) | VariableType::Vector(_))
        ) {
            return true;
        }
        match expr {
            IRExpr::BinOp {
                kind: IRBinOpKind::Add,
                lhs,
                rhs,
            } => {
                (self.pointer_address(lhs) && self.integer_offset(rhs))
                    || (self.integer_offset(lhs) && self.pointer_address(rhs))
            }
            _ => false,
        }
    }

    fn struct_field<'b>(&self, address: &'b IRExpr) -> Option<(&'b IRExpr, usize)> {
        let (base, offset) = field_address(address)?;
        let Some(VariableType::Pointer(pointee)) = self.direct_type(base) else {
            return None;
        };
        let VariableType::Struct(id) = *pointee else {
            return None;
        };
        self.structs
            .get(id.id)?
            .fields
            .iter()
            .any(|field| field.offset == offset)
            .then_some((base, offset))
    }
}

fn function_name(id: SyntheticFunctionId) -> String {
    format!("fn_{}", id.id)
}

fn variable_name(id: VariableId) -> String {
    format!("v{}", id.id)
}

fn type_name(ty: VariableType, structs: &[StructDefinition]) -> String {
    match ty {
        VariableType::Unknown(Some(size)) => format!("Unknown{size}"),
        VariableType::Unknown(None) => "Unknown".to_string(),
        VariableType::UnknownPointer => "Unknown*".to_string(),
        VariableType::Pointer(pointee) => format!("{}*", type_name(*pointee, structs)),
        VariableType::Vector(element) => format!("vec<{}>", type_name(*element, structs)),
        VariableType::Struct(id) => structs.get(id.id).map_or_else(
            || format!("AStruct{}", id.id),
            |definition| definition.name.clone(),
        ),
        VariableType::Bool => "Bool".to_string(),
        VariableType::Integer(bits) => format!("i{bits}"),
        VariableType::UnsignedInteger(bits) => format!("u{bits}"),
    }
}

fn dereference(address: &IRExpr, types: &RenderTypes) -> String {
    if let IRExpr::ElementAddress { base, index, .. } = address {
        let index = match index.as_ref() {
            IRExpr::Convert {
                value,
                source,
                target,
            } if !source.signed
                && !target.signed
                && target.size >= source.size
                && types.integer_type(value) == Some(*source) =>
            {
                value.as_ref()
            }
            other => other,
        };
        format!(
            "{}[{}]",
            expression(base, 10, types),
            expression(index, 0, types)
        )
    } else if let Some((base, offset)) = types.struct_field(address) {
        format!("{}->_0x{offset:x}", expression(base, 9, types))
    } else {
        format!("*({})", expression(address, 0, types))
    }
}

// Higher numbers bind more tightly. Unsigned comparisons use the relational
// level, so an expression keeps its IR grouping when printed.
fn precedence(expr: &IRExpr) -> u8 {
    match expr {
        IRExpr::BinOp {
            kind: IRBinOpKind::Or,
            ..
        } => 1,
        IRExpr::BinOp {
            kind: IRBinOpKind::LogicalAnd,
            ..
        } => 2,
        IRExpr::BinOp {
            kind: IRBinOpKind::And | IRBinOpKind::BitOr,
            ..
        } => 3,
        IRExpr::BinOp {
            kind: IRBinOpKind::Eq | IRBinOpKind::Ne,
            ..
        } => 4,
        IRExpr::BinOp {
            kind:
                IRBinOpKind::SignedGt
                | IRBinOpKind::SignedLe
                | IRBinOpKind::UnsignedLt
                | IRBinOpKind::UnsignedGe,
            ..
        } => 5,
        IRExpr::BinOp {
            kind: IRBinOpKind::Shl | IRBinOpKind::Shr,
            ..
        } => 6,
        IRExpr::BinOp {
            kind: IRBinOpKind::Mul | IRBinOpKind::UnsignedMod,
            ..
        } => 8,
        IRExpr::BinOp { .. } => 7,
        IRExpr::Not(..)
        | IRExpr::Deref(..)
        | IRExpr::MemoryAddress { .. }
        | IRExpr::ElementAddress { .. } => 9,
        _ => 10,
    }
}

fn binary_operator(kind: &IRBinOpKind) -> &'static str {
    match kind {
        IRBinOpKind::Add => "+",
        IRBinOpKind::Sub => "-",
        IRBinOpKind::Mul => "*",
        IRBinOpKind::UnsignedMod => "u%",
        IRBinOpKind::Shl => "<<",
        IRBinOpKind::Shr => ">>>",
        IRBinOpKind::BitOr => "|",
        IRBinOpKind::And => "&",
        IRBinOpKind::LogicalAnd => "&&",
        IRBinOpKind::Or => "||",
        IRBinOpKind::Eq => "===",
        IRBinOpKind::SignedGt => ">",
        IRBinOpKind::SignedLe => "<=",
        IRBinOpKind::Ne => "!==",
        IRBinOpKind::UnsignedLt => "u<",
        IRBinOpKind::UnsignedGe => "u>=",
    }
}

fn binary_operand(expr: &IRExpr, parent_precedence: u8, types: &RenderTypes) -> String {
    if matches!(expr, IRExpr::BinOp { .. }) {
        format!("({})", expression(expr, 0, types))
    } else {
        expression(expr, parent_precedence, types)
    }
}

fn expression(expr: &IRExpr, parent_precedence: u8, types: &RenderTypes) -> String {
    // MemoryAddress carries the access width; a pointer-typed address needs
    // no cast in the output.
    if let IRExpr::MemoryAddress { address, .. } = expr
        && types.pointer_address(address)
    {
        return expression(address, parent_precedence, types);
    }
    let own_precedence = precedence(expr);
    let rendered = match expr {
        IRExpr::BinOp { kind, lhs, rhs } => {
            let operator = binary_operator(kind);
            format!(
                "{} {operator} {}",
                binary_operand(lhs, own_precedence, types),
                binary_operand(rhs, own_precedence + 1, types)
            )
        }
        IRExpr::Deref(address) => dereference(address, types),
        IRExpr::ElementAddress { .. } => format!("&{}", dereference(expr, types)),
        IRExpr::MemoryAddress { address, .. } => {
            format!("(Unknown*)({})", expression(address, 0, types))
        }
        IRExpr::Argument(ordinal) => format!("arg{ordinal}"),
        IRExpr::Convert {
            value,
            source,
            target,
        } => {
            let input = expression(value, 0, types);
            if types.integer_type(value) == Some(*source) || target.size <= source.size {
                format!("{target}({input})")
            } else {
                format!("{target}({source}({input}))")
            }
        }
        IRExpr::CU8(value) => format!("0x{value:x}"),
        IRExpr::CU32(value) => format!("0x{value:x}"),
        IRExpr::CU64(value) => format!("0x{value:x}"),
        IRExpr::Variable(variable) => variable_name(*variable),
        IRExpr::Bool(value) => value.to_string(),
        IRExpr::Not(inner) => format!("!{}", binary_operand(inner, own_precedence, types)),
    };
    if own_precedence < parent_precedence {
        format!("({rendered})")
    } else {
        rendered
    }
}

fn instruction(
    output: &mut String,
    instr: &IRInst,
    indent: usize,
    types: &RenderTypes,
    address_comments: bool,
) {
    let padding = "    ".repeat(indent);
    match instr {
        IRInst::Assign { dest, src } => {
            writeln!(
                output,
                "{padding}{} = {};",
                expression(dest, 0, types),
                expression(src, 0, types)
            )
            .unwrap();
        }
        IRInst::CompoundAssign { dest, kind, value } => {
            writeln!(
                output,
                "{padding}{} {}= {};",
                expression(dest, 0, types),
                binary_operator(kind),
                expression(value, 0, types)
            )
            .unwrap();
        }
        IRInst::Return(Some(value)) => {
            writeln!(output, "{padding}return {};", expression(value, 0, types)).unwrap();
        }
        IRInst::Return(None) => {
            writeln!(output, "{padding}return;").unwrap();
        }
        IRInst::DeclareVariable { variable, ty } => {
            let ty = type_name(ty.clone(), types.structs);
            writeln!(output, "{padding}let {}: {ty};", variable_name(*variable)).unwrap();
        }
        IRInst::DeclareAndAssignVariable {
            variable,
            ty,
            value,
        } => {
            let ty = type_name(ty.clone(), types.structs);
            writeln!(
                output,
                "{padding}let {}: {ty} = {};",
                variable_name(*variable),
                expression(value, 0, types)
            )
            .unwrap();
        }
        IRInst::AssignVariable { variable, value } => {
            writeln!(
                output,
                "{padding}{} = {};",
                variable_name(*variable),
                expression(value, 0, types)
            )
            .unwrap();
        }
        IRInst::LoadVariable { variable, address } => {
            writeln!(
                output,
                "{padding}{} = {};",
                variable_name(*variable),
                dereference(address, types)
            )
            .unwrap();
        }
        IRInst::StoreVariable { address, variable } => {
            writeln!(
                output,
                "{padding}{} = {};",
                dereference(address, types),
                variable_name(*variable)
            )
            .unwrap();
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            writeln!(
                output,
                "{padding}if ({}) {{",
                expression(condition, 0, types)
            )
            .unwrap();
            for instr in then_branch {
                instruction(output, instr, indent + 1, types, address_comments);
            }
            if !else_branch.is_empty() {
                writeln!(output, "{padding}}} else {{").unwrap();
                for instr in else_branch {
                    instruction(output, instr, indent + 1, types, address_comments);
                }
            }
            writeln!(output, "{padding}}}").unwrap();
        }
        IRInst::While {
            label,
            entry_offset,
            condition,
            body,
        } => {
            let label = label.map_or_else(String::new, |label| format!("loop_{}: ", label.id));
            match condition {
                LoopCondition::Before {
                    offset,
                    expression: check,
                } => {
                    if address_comments && offset != entry_offset {
                        writeln!(output, "{padding}// 0x{offset:x}").unwrap();
                    }
                    writeln!(
                        output,
                        "{padding}{label}while ({}) {{",
                        expression(check, 0, types)
                    )
                    .unwrap();
                }
                LoopCondition::After { .. } => {
                    writeln!(output, "{padding}{label}do {{").unwrap();
                }
            }
            let nested_padding = "    ".repeat(indent + 1);
            let mut previous_offset = Some(*entry_offset);
            for (offset, instr) in body {
                if address_comments && previous_offset != Some(*offset) {
                    writeln!(output, "{nested_padding}// 0x{offset:x}").unwrap();
                    previous_offset = Some(*offset);
                }
                instruction(output, instr, indent + 1, types, address_comments);
            }
            match condition {
                LoopCondition::Before { .. } => writeln!(output, "{padding}}}").unwrap(),
                LoopCondition::After {
                    offset,
                    expression: check,
                } => {
                    if address_comments && previous_offset != Some(*offset) {
                        writeln!(output, "{nested_padding}// 0x{offset:x}").unwrap();
                    }
                    writeln!(
                        output,
                        "{padding}}} while ({});",
                        expression(check, 0, types)
                    )
                    .unwrap();
                }
            }
        }
        IRInst::ForEach {
            entry_offset,
            condition_offset,
            advance_offset,
            load_offset,
            variable,
            element_type,
            vector,
            start,
            index_bits,
            body,
        } => {
            if address_comments {
                writeln!(output, "{padding}// 0x{entry_offset:x}").unwrap();
                writeln!(output, "{padding}// u{index_bits} index wraps; advance 0x{advance_offset:x}, load 0x{load_offset:x}").unwrap();
            }
            if address_comments && condition_offset != entry_offset {
                writeln!(output, "{padding}// 0x{condition_offset:x}").unwrap();
            }
            writeln!(
                output,
                "{padding}for {}: {} in {}[{start}..] {{",
                variable_name(*variable),
                type_name(element_type.clone(), types.structs),
                expression(vector, 10, types),
            )
            .unwrap();
            let nested_padding = "    ".repeat(indent + 1);
            let mut previous_offset = Some(*entry_offset);
            for (offset, instr) in body {
                if address_comments && previous_offset != Some(*offset) {
                    writeln!(output, "{nested_padding}// 0x{offset:x}").unwrap();
                    previous_offset = Some(*offset);
                }
                instruction(output, instr, indent + 1, types, address_comments);
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
                .map(|argument| expression(argument, 0, types))
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
            writeln!(output, "{padding}jump({});", expression(target, 0, types)).unwrap();
        }
        IRInst::End => {
            writeln!(output, "{padding}end();").unwrap();
        }
    }
}

/// Render the complete tier 6 program, optionally including source address comments.
pub fn render(program: &Program, address_comments: bool) -> String {
    let mut output = String::new();
    match program.entry {
        Some(entry) => writeln!(output, "// entry: {}", function_name(entry)).unwrap(),
        None => writeln!(output, "// entry: none").unwrap(),
    }

    for (index, function) in program.functions.iter().enumerate() {
        let types = RenderTypes::from_function(function, &program.structs);
        let id = SyntheticFunctionId { id: index };
        let parameters = function
            .parameters
            .iter()
            .map(|parameter| match parameter {
                Parameter::Argument { ordinal, ty } => {
                    format!("arg{ordinal}: {}", type_name(ty.clone(), &program.structs))
                }
                Parameter::Slot { variable, ty } => {
                    format!(
                        "{}: {}",
                        variable_name(*variable),
                        type_name(ty.clone(), &program.structs)
                    )
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
            instruction(&mut output, instr, 1, &types, address_comments);
        }
        writeln!(output, "}}").unwrap();
    }
    output
}
