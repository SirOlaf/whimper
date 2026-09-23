mod infer_types;
pub mod ir;
pub mod render;

use crate::irt4::ir as t4;

use self::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, LoopId, Parameter, Program, SyntheticFunction,
    SyntheticFunctionId, VariableId, VariableType,
};

fn function_id(id: t4::SyntheticFunctionId) -> SyntheticFunctionId {
    SyntheticFunctionId { id: id.id }
}

fn variable_id(id: t4::VariableId) -> VariableId {
    VariableId {
        owner: function_id(id.owner),
        id: id.id,
    }
}

fn variable_type(ty: t4::VariableType) -> VariableType {
    match ty {
        t4::VariableType::Unknown(size) => VariableType::Unknown(size),
        t4::VariableType::Bool => VariableType::Bool,
    }
}

fn parameter(parameter: &t4::Parameter) -> Parameter {
    match parameter {
        t4::Parameter::Argument { ordinal, size } => Parameter::Argument {
            ordinal: *ordinal,
            ty: VariableType::Unknown(Some(*size)),
        },
        t4::Parameter::Slot { variable, size } => Parameter::Slot {
            variable: variable_id(*variable),
            ty: VariableType::Unknown(Some(*size)),
        },
    }
}

fn bin_op(kind: &t4::IRBinOpKind) -> IRBinOpKind {
    match kind {
        t4::IRBinOpKind::Add => IRBinOpKind::Add,
        t4::IRBinOpKind::Sub => IRBinOpKind::Sub,
        t4::IRBinOpKind::Shl => IRBinOpKind::Shl,
        t4::IRBinOpKind::And => IRBinOpKind::And,
        t4::IRBinOpKind::Or => IRBinOpKind::Or,
        t4::IRBinOpKind::Eq => IRBinOpKind::Eq,
        t4::IRBinOpKind::UnsignedLt => IRBinOpKind::UnsignedLt,
    }
}

fn expression(expr: &t4::IRExpr) -> IRExpr {
    match expr {
        t4::IRExpr::BinOp { kind, lhs, rhs } => IRExpr::BinOp {
            kind: bin_op(kind),
            lhs: Box::new(expression(lhs)),
            rhs: Box::new(expression(rhs)),
        },
        t4::IRExpr::Deref(address) => IRExpr::Deref(Box::new(expression(address))),
        t4::IRExpr::CastUnknownPtr { address, size } => IRExpr::MemoryAddress {
            address: Box::new(expression(address)),
            size: *size,
        },
        t4::IRExpr::Argument(ordinal) => IRExpr::Argument(*ordinal),
        t4::IRExpr::ExtractBytes {
            value,
            offset,
            size,
        } => IRExpr::ExtractBytes {
            value: Box::new(expression(value)),
            offset: *offset,
            size: *size,
        },
        t4::IRExpr::ZeroExtend { value, size } => IRExpr::ZeroExtend {
            value: Box::new(expression(value)),
            size: *size,
        },
        t4::IRExpr::ReplaceBytes {
            original,
            value,
            offset,
            size,
        } => IRExpr::ReplaceBytes {
            original: Box::new(expression(original)),
            value: Box::new(expression(value)),
            offset: *offset,
            size: *size,
        },
        t4::IRExpr::CU8(value) => IRExpr::CU8(*value),
        t4::IRExpr::CU32(value) => IRExpr::CU32(*value),
        t4::IRExpr::CU64(value) => IRExpr::CU64(*value),
        t4::IRExpr::Variable(variable) => IRExpr::Variable(variable_id(*variable)),
        t4::IRExpr::Bool(value) => IRExpr::Bool(*value),
        t4::IRExpr::Not(inner) => IRExpr::Not(Box::new(expression(inner))),
    }
}

fn condition(condition: &t4::LoopCondition) -> LoopCondition {
    match condition {
        t4::LoopCondition::Before {
            offset,
            expression: value,
        } => LoopCondition::Before {
            offset: *offset,
            expression: expression(value),
        },
        t4::LoopCondition::After {
            offset,
            expression: value,
        } => LoopCondition::After {
            offset: *offset,
            expression: expression(value),
        },
    }
}

fn instruction(instr: &t4::IRInst) -> IRInst {
    match instr {
        t4::IRInst::Assign { dest, src } => IRInst::Assign {
            dest: expression(dest),
            src: expression(src),
        },
        t4::IRInst::Return(value) => IRInst::Return(value.as_ref().map(expression)),
        t4::IRInst::DeclareVariable { variable, ty } => IRInst::DeclareVariable {
            variable: variable_id(*variable),
            ty: variable_type(*ty),
        },
        t4::IRInst::DeclareAndAssignVariable {
            variable,
            ty,
            value,
        } => IRInst::DeclareAndAssignVariable {
            variable: variable_id(*variable),
            ty: variable_type(*ty),
            value: expression(value),
        },
        t4::IRInst::AssignVariable { variable, value } => IRInst::AssignVariable {
            variable: variable_id(*variable),
            value: expression(value),
        },
        t4::IRInst::LoadVariable { variable, address } => IRInst::LoadVariable {
            variable: variable_id(*variable),
            address: expression(address),
        },
        t4::IRInst::StoreVariable { address, variable } => IRInst::StoreVariable {
            address: expression(address),
            variable: variable_id(*variable),
        },
        t4::IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => IRInst::If {
            condition: expression(condition),
            then_branch: then_branch.iter().map(instruction).collect(),
            else_branch: else_branch.iter().map(instruction).collect(),
        },
        t4::IRInst::While {
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
        t4::IRInst::Break => IRInst::Break,
        t4::IRInst::Continue => IRInst::Continue,
        t4::IRInst::ContinueLoop(id) => IRInst::ContinueLoop(LoopId { id: id.id }),
        t4::IRInst::CallSynthetic {
            function,
            arguments,
        } => IRInst::CallSynthetic {
            function: function_id(*function),
            arguments: arguments.iter().map(expression).collect(),
        },
        t4::IRInst::Jump(value) => IRInst::Jump(expression(value)),
        t4::IRInst::End => IRInst::End,
    }
}

pub fn lift(source: &t4::Program) -> Program {
    let mut program = Program {
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
    infer_types::run(&mut program);
    program
}
