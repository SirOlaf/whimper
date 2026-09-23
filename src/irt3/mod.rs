mod cfg;
pub mod inline_functions;
pub mod inline_trivial_loops;
pub mod inline_variables;
pub mod ir;
pub mod render;
mod return_slots;

use crate::irt2::ir as t2;

use self::ir::{
    IRBinOpKind, IRExpr, IRInst, Parameter, Program, SyntheticFunction, SyntheticFunctionId,
    VariableId, VariableType,
};

fn function_id(id: t2::SyntheticFunctionId) -> SyntheticFunctionId {
    SyntheticFunctionId { id: id.id }
}

fn variable_id(id: t2::VariableId) -> VariableId {
    VariableId {
        owner: function_id(id.owner),
        id: id.id,
    }
}

fn parameter(parameter: &t2::Parameter) -> Parameter {
    match parameter {
        t2::Parameter::Native { ordinal, register } => Parameter::Native {
            ordinal: *ordinal,
            register: *register,
        },
        t2::Parameter::Slot { variable, register } => Parameter::Slot {
            variable: variable_id(*variable),
            register: *register,
        },
    }
}

fn variable_type(ty: t2::VariableType) -> VariableType {
    match ty {
        t2::VariableType::Unknown(size) => VariableType::Unknown(size),
        t2::VariableType::Register(register) => VariableType::Register(register),
        t2::VariableType::Bool => VariableType::Bool,
    }
}

fn bin_op(kind: &t2::IRBinOpKind) -> IRBinOpKind {
    match kind {
        t2::IRBinOpKind::Add => IRBinOpKind::Add,
        t2::IRBinOpKind::Sub => IRBinOpKind::Sub,
        t2::IRBinOpKind::Mul => IRBinOpKind::Mul,
        t2::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t2::IRBinOpKind::Shr => IRBinOpKind::Shr,
        t2::IRBinOpKind::BitOr => IRBinOpKind::BitOr,
        t2::IRBinOpKind::And => IRBinOpKind::And,
        t2::IRBinOpKind::Or => IRBinOpKind::Or,
        t2::IRBinOpKind::Eq => IRBinOpKind::Eq,
        t2::IRBinOpKind::SignedGt => IRBinOpKind::SignedGt,
        t2::IRBinOpKind::UnsignedLt => IRBinOpKind::UnsignedLt,
    }
}

fn expression(expr: &t2::IRExpr) -> IRExpr {
    match expr {
        t2::IRExpr::BinOp { kind, lhs, rhs } => IRExpr::BinOp {
            kind: bin_op(kind),
            lhs: Box::new(expression(lhs)),
            rhs: Box::new(expression(rhs)),
        },
        t2::IRExpr::Deref(address) => IRExpr::Deref(Box::new(expression(address))),
        t2::IRExpr::CastUnknownPtr { address, size } => IRExpr::CastUnknownPtr {
            address: Box::new(expression(address)),
            size: *size,
        },
        t2::IRExpr::Argument(ordinal) => IRExpr::Argument(*ordinal),
        t2::IRExpr::Convert {
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
        t2::IRExpr::CU8(value) => IRExpr::CU8(*value),
        t2::IRExpr::CU32(value) => IRExpr::CU32(*value),
        t2::IRExpr::CU64(value) => IRExpr::CU64(*value),
        t2::IRExpr::Variable(variable) => IRExpr::Variable(variable_id(*variable)),
        t2::IRExpr::Bool(value) => IRExpr::Bool(*value),
        t2::IRExpr::Not(inner) => IRExpr::Not(Box::new(expression(inner))),
    }
}

fn instruction(instr: &t2::IRInst) -> IRInst {
    match instr {
        t2::IRInst::Assign { dest, src } => IRInst::Assign {
            dest: expression(dest),
            src: expression(src),
        },
        t2::IRInst::Return(value) => IRInst::Return(value.as_ref().map(expression)),
        t2::IRInst::DeclareVariable { variable, ty } => IRInst::DeclareVariable {
            variable: variable_id(*variable),
            ty: variable_type(*ty),
        },
        t2::IRInst::AssignVariable { variable, value } => IRInst::AssignVariable {
            variable: variable_id(*variable),
            value: expression(value),
        },
        t2::IRInst::LoadVariable { variable, address } => IRInst::LoadVariable {
            variable: variable_id(*variable),
            address: expression(address),
        },
        t2::IRInst::StoreVariable { address, variable } => IRInst::StoreVariable {
            address: expression(address),
            variable: variable_id(*variable),
        },
        t2::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => IRInst::If {
            condition: expression(condition),
            then_branch: then_branch.iter().map(instruction).collect(),
            else_branch: else_branch.iter().map(instruction).collect(),
        },
        t2::IRInst::CallSynthetic {
            function,
            arguments,
        } => IRInst::CallSynthetic {
            function: function_id(*function),
            arguments: arguments.iter().map(expression).collect(),
        },
        t2::IRInst::Jump(target) => IRInst::Jump(expression(target)),
        t2::IRInst::End => IRInst::End,
    }
}

pub fn lift(source: &t2::Program) -> Program {
    let program = Program {
        entry: source.entry.map(function_id),
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
    };
    let program = inline_variables::tr(program);
    let program = inline_trivial_loops::tr(program);
    let program = inline_variables::tr(program);
    return_slots::tr(inline_functions::tr(program))
}
