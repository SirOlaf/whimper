//! Tier 6 owns its complete program IR. Arithmetic analysis and recovery are
//! separate from the lossless tier 5 translation.
pub mod arithmetic;
mod effects;
pub mod ir;
pub mod render;
pub mod shapes;
pub mod unoptimize;

use crate::irt5::ir as t5;

use self::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, LoopId, Parameter, Program, StructDefinition,
    StructField, StructId, SyntheticFunction, SyntheticFunctionId, VariableId, VariableType,
};

fn function_id(id: t5::SyntheticFunctionId) -> SyntheticFunctionId {
    SyntheticFunctionId { id: id.id }
}

fn variable_id(source: t5::VariableId) -> VariableId {
    VariableId {
        owner: function_id(source.owner),
        id: source.id,
    }
}

fn variable_type(ty: t5::VariableType) -> VariableType {
    match ty {
        t5::VariableType::Unknown(size) => VariableType::Unknown(size),
        t5::VariableType::Bool => VariableType::Bool,
        t5::VariableType::UnknownPointer => VariableType::UnknownPointer,
        t5::VariableType::Pointer(inner) => VariableType::Pointer(Box::new(variable_type(*inner))),
        t5::VariableType::Vector(inner) => VariableType::Vector(Box::new(variable_type(*inner))),
        t5::VariableType::Struct(id) => VariableType::Struct(StructId { id: id.id }),
        t5::VariableType::Integer(bits) => VariableType::Integer(bits),
        t5::VariableType::UnsignedInteger(bits) => VariableType::UnsignedInteger(bits),
    }
}

fn parameter(parameter: &t5::Parameter) -> Parameter {
    match parameter {
        t5::Parameter::Argument { ordinal, ty } => Parameter::Argument {
            ordinal: *ordinal,
            ty: variable_type(ty.clone()),
        },
        t5::Parameter::Slot { variable, ty } => Parameter::Slot {
            variable: variable_id(*variable),
            ty: variable_type(ty.clone()),
        },
    }
}

fn bin_op(kind: &t5::IRBinOpKind) -> IRBinOpKind {
    match kind {
        t5::IRBinOpKind::Add => IRBinOpKind::Add,
        t5::IRBinOpKind::Sub => IRBinOpKind::Sub,
        t5::IRBinOpKind::Mul => IRBinOpKind::Mul,
        t5::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t5::IRBinOpKind::Shr => IRBinOpKind::Shr,
        t5::IRBinOpKind::BitOr => IRBinOpKind::BitOr,
        t5::IRBinOpKind::And => IRBinOpKind::And,
        t5::IRBinOpKind::Or => IRBinOpKind::Or,
        t5::IRBinOpKind::Eq => IRBinOpKind::Eq,
        t5::IRBinOpKind::SignedGt => IRBinOpKind::SignedGt,
        t5::IRBinOpKind::Ne => IRBinOpKind::Ne,
        t5::IRBinOpKind::UnsignedLt => IRBinOpKind::UnsignedLt,
        t5::IRBinOpKind::UnsignedGe => IRBinOpKind::UnsignedGe,
    }
}

fn expression(expr: &t5::IRExpr) -> IRExpr {
    match expr {
        t5::IRExpr::BinOp { kind, lhs, rhs } => IRExpr::BinOp {
            kind: bin_op(kind),
            lhs: Box::new(expression(lhs)),
            rhs: Box::new(expression(rhs)),
        },
        t5::IRExpr::Deref(address) => IRExpr::Deref(Box::new(expression(address))),
        t5::IRExpr::MemoryAddress { address, size } => IRExpr::MemoryAddress {
            address: Box::new(expression(address)),
            size: *size,
        },
        t5::IRExpr::ElementAddress {
            base,
            index,
            element_size,
        } => IRExpr::ElementAddress {
            base: Box::new(expression(base)),
            index: Box::new(expression(index)),
            element_size: *element_size,
        },
        t5::IRExpr::Argument(ordinal) => IRExpr::Argument(*ordinal),
        t5::IRExpr::Convert {
            value,
            source,
            target,
        } => IRExpr::Convert {
            value: Box::new(expression(value)),
            source: self::ir::IntegerType {
                size: source.size,
                signed: source.signed,
            },
            target: self::ir::IntegerType {
                size: target.size,
                signed: target.signed,
            },
        },
        t5::IRExpr::CU8(value) => IRExpr::CU8(*value),
        t5::IRExpr::CU32(value) => IRExpr::CU32(*value),
        t5::IRExpr::CU64(value) => IRExpr::CU64(*value),
        t5::IRExpr::Variable(variable) => IRExpr::Variable(variable_id(*variable)),
        t5::IRExpr::Bool(value) => IRExpr::Bool(*value),
        t5::IRExpr::Not(inner) => IRExpr::Not(Box::new(expression(inner))),
    }
}

fn condition(condition: &t5::LoopCondition) -> LoopCondition {
    match condition {
        t5::LoopCondition::Before {
            offset,
            expression: value,
        } => LoopCondition::Before {
            offset: *offset,
            expression: expression(value),
        },
        t5::LoopCondition::After {
            offset,
            expression: value,
        } => LoopCondition::After {
            offset: *offset,
            expression: expression(value),
        },
    }
}

fn instruction(instr: &t5::IRInst) -> IRInst {
    match instr {
        t5::IRInst::Assign { dest, src } => IRInst::Assign {
            dest: expression(dest),
            src: expression(src),
        },
        t5::IRInst::Return(value) => IRInst::Return(value.as_ref().map(expression)),
        t5::IRInst::DeclareVariable { variable, ty } => IRInst::DeclareVariable {
            variable: variable_id(*variable),
            ty: variable_type(ty.clone()),
        },
        t5::IRInst::DeclareAndAssignVariable {
            variable,
            ty,
            value,
        } => IRInst::DeclareAndAssignVariable {
            variable: variable_id(*variable),
            ty: variable_type(ty.clone()),
            value: expression(value),
        },
        t5::IRInst::AssignVariable { variable, value } => IRInst::AssignVariable {
            variable: variable_id(*variable),
            value: expression(value),
        },
        t5::IRInst::LoadVariable { variable, address } => IRInst::LoadVariable {
            variable: variable_id(*variable),
            address: expression(address),
        },
        t5::IRInst::StoreVariable { address, variable } => IRInst::StoreVariable {
            address: expression(address),
            variable: variable_id(*variable),
        },
        t5::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => IRInst::If {
            condition: expression(condition),
            then_branch: then_branch.iter().map(instruction).collect(),
            else_branch: else_branch.iter().map(instruction).collect(),
        },
        t5::IRInst::While {
            label,
            entry_offset,
            condition: check,
            body,
        } => IRInst::While {
            label: label.map(|id| LoopId { id: id.id }),
            entry_offset: *entry_offset,
            condition: condition(check),
            body: body
                .iter()
                .map(|(offset, instr)| (*offset, instruction(instr)))
                .collect(),
        },
        t5::IRInst::Break => IRInst::Break,
        t5::IRInst::Continue => IRInst::Continue,
        t5::IRInst::ContinueLoop(id) => IRInst::ContinueLoop(LoopId { id: id.id }),
        t5::IRInst::CallSynthetic {
            function,
            arguments,
        } => IRInst::CallSynthetic {
            function: function_id(*function),
            arguments: arguments.iter().map(expression).collect(),
        },
        t5::IRInst::Jump(value) => IRInst::Jump(expression(value)),
        t5::IRInst::End => IRInst::End,
    }
}

pub fn lift(source: &t5::Program) -> Program {
    Program {
        entry: source.entry.map(function_id),
        structs: source
            .structs
            .iter()
            .map(|definition| StructDefinition {
                name: definition.name.clone(),
                fields: definition
                    .fields
                    .iter()
                    .map(|field| StructField {
                        offset: field.offset,
                        ty: variable_type(field.ty.clone()),
                    })
                    .collect(),
            })
            .collect(),
        functions: source
            .functions
            .iter()
            .map(|function| SyntheticFunction {
                entry_offset: function.entry_offset,
                parameters: function.parameters.iter().map(parameter).collect(),
                body: function
                    .body
                    .iter()
                    .map(|(offset, instr)| (*offset, instruction(instr)))
                    .collect(),
            })
            .collect(),
    }
}
