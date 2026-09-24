//! Infer a function result from the final, recovered Tier 6 expressions.
//! Literals carry a width but no signedness; a typed return may supply that
//! missing evidence. Synthetic calls are tail transfers, so their returns
//! participate in the caller's agreement check.

use std::collections::{HashMap, HashSet};

use super::effects::Effects;
use super::ir::{
    DataId, DataVariable, IRBinOpKind, IRExpr, IRInst, Parameter, Program, StructDefinition,
    SyntheticFunction, SyntheticFunctionId, VariableId, VariableType, field_address,
};

#[derive(Clone)]
enum Value {
    Void,
    Unknown,
    Literal(usize),
    Typed(VariableType),
    Conflict,
}

impl Value {
    fn join(self, other: Self) -> Self {
        use Value::*;
        match (self, other) {
            (Conflict, _) | (_, Conflict) => Conflict,
            (Void, Void) => Void,
            (Void, _) | (_, Void) => Conflict,
            (Unknown, _) | (_, Unknown) => Unknown,
            (Literal(left), Literal(right)) if left == right => Literal(left),
            (Literal(size), Typed(VariableType::Integer(bits)))
            | (Typed(VariableType::Integer(bits)), Literal(size))
                if bits == size * 8 =>
            {
                Typed(VariableType::Integer(bits))
            }
            (Literal(size), Typed(VariableType::UnsignedInteger(bits)))
            | (Typed(VariableType::UnsignedInteger(bits)), Literal(size))
                if bits == size * 8 =>
            {
                Typed(VariableType::UnsignedInteger(bits))
            }
            (Typed(VariableType::Integer(left)), Typed(VariableType::UnsignedInteger(right)))
            | (Typed(VariableType::UnsignedInteger(left)), Typed(VariableType::Integer(right)))
                if left == right =>
            {
                Typed(VariableType::UnsignedInteger(left))
            }
            (Typed(left), Typed(right)) if left == right => Typed(left),
            _ => Conflict,
        }
    }

    fn result_type(self) -> Option<VariableType> {
        match self {
            Self::Typed(ty) => Some(ty),
            Self::Literal(size) => Some(VariableType::Integer(size * 8)),
            _ => None,
        }
    }
}

struct Types<'a> {
    arguments: HashMap<usize, VariableType>,
    variables: HashMap<VariableId, VariableType>,
    data: HashMap<DataId, VariableType>,
    structs: &'a [StructDefinition],
}

impl<'a> Types<'a> {
    fn new(
        function: &SyntheticFunction,
        structs: &'a [StructDefinition],
        data: &[DataVariable],
    ) -> Self {
        let mut types = Self {
            arguments: HashMap::new(),
            variables: HashMap::new(),
            data: data.iter().map(|item| (item.id, item.ty.clone())).collect(),
            structs,
        };
        for parameter in &function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    types.arguments.insert(*ordinal, ty.clone());
                }
                Parameter::Slot { variable, ty } => {
                    types.variables.insert(*variable, ty.clone());
                }
            }
        }
        for (_, instr) in &function.body {
            types.declarations(instr);
        }
        types
    }

    fn declarations(&mut self, instr: &IRInst) {
        match instr {
            IRInst::DeclareVariable { variable, ty }
            | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
                self.variables.insert(*variable, ty.clone());
            }
            IRInst::ForEach {
                variable,
                element_type,
                body,
                ..
            } => {
                self.variables.insert(*variable, element_type.clone());
                for (_, child) in body {
                    self.declarations(child);
                }
            }
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                for child in then_branch.iter().chain(else_branch) {
                    self.declarations(child);
                }
            }
            IRInst::While { body, .. } => {
                for (_, child) in body {
                    self.declarations(child);
                }
            }
            _ => {}
        }
    }

    fn direct(&self, expr: &IRExpr) -> Option<VariableType> {
        match expr {
            IRExpr::Argument(ordinal) => self.arguments.get(ordinal).cloned(),
            IRExpr::Variable(variable) => self.variables.get(variable).cloned(),
            IRExpr::Data(data) => self.data.get(data).cloned(),
            _ => None,
        }
    }

    fn known(&self, ty: Option<VariableType>) -> Value {
        match ty {
            Some(VariableType::Unknown(_)) | None => Value::Unknown,
            Some(ty) => Value::Typed(ty),
        }
    }

    fn dereference(&self, address: &IRExpr) -> Value {
        if let IRExpr::ElementAddress {
            base, element_size, ..
        } = address
        {
            let ty = match self.direct(base) {
                Some(VariableType::Vector(element) | VariableType::Pointer(element)) => {
                    Some(*element)
                }
                Some(VariableType::CString) if *element_size == 1 => Some(VariableType::Integer(8)),
                _ => None,
            };
            return self.known(ty);
        }
        if let Some((base, offset)) = field_address(address)
            && let Some(VariableType::Pointer(pointee)) = self.direct(base)
            && let VariableType::Struct(id) = *pointee
        {
            let ty = self.structs.get(id.id).and_then(|definition| {
                definition
                    .fields
                    .iter()
                    .find(|field| field.offset == offset)
                    .map(|field| field.ty.clone())
            });
            return self.known(ty);
        }
        let pointee = match address {
            IRExpr::MemoryAddress { address, size } => self.direct(address).and_then(|ty| {
                if let VariableType::Pointer(pointee) = ty {
                    let width = match pointee.as_ref() {
                        VariableType::Integer(bits) | VariableType::UnsignedInteger(bits) => {
                            Some(bits / 8)
                        }
                        VariableType::Bool => Some(1),
                        _ => None,
                    };
                    (size.is_none() || *size == width).then_some(*pointee)
                } else {
                    None
                }
            }),
            other => self.direct(other).and_then(|ty| {
                if let VariableType::Pointer(pointee) = ty {
                    Some(*pointee)
                } else {
                    None
                }
            }),
        };
        self.known(pointee)
    }

    fn expression(&self, expr: &IRExpr) -> Value {
        use IRBinOpKind::*;
        match expr {
            IRExpr::Argument(_) | IRExpr::Variable(_) | IRExpr::Data(_) => {
                self.known(self.direct(expr))
            }
            IRExpr::CU8(_) => Value::Literal(1),
            IRExpr::CU32(_) => Value::Literal(4),
            IRExpr::CU64(_) => Value::Literal(8),
            IRExpr::Bool(_) | IRExpr::Not(_) => Value::Typed(VariableType::Bool),
            IRExpr::Convert { target, .. } => {
                let bits = target.size * 8;
                Value::Typed(if target.signed {
                    VariableType::Integer(bits)
                } else {
                    VariableType::UnsignedInteger(bits)
                })
            }
            IRExpr::BinOp { kind, lhs, rhs } => match kind {
                Eq | SignedGt | SignedLe | Ne | UnsignedLt | UnsignedGe | LogicalAnd | Or => {
                    Value::Typed(VariableType::Bool)
                }
                Shl | Shr => self.expression(lhs),
                UnsignedMod => match self.expression(lhs) {
                    Value::Typed(
                        VariableType::Integer(bits) | VariableType::UnsignedInteger(bits),
                    ) => Value::Typed(VariableType::UnsignedInteger(bits)),
                    Value::Literal(size) => Value::Typed(VariableType::UnsignedInteger(size * 8)),
                    _ => Value::Unknown,
                },
                Add | Sub | Mul | BitOr | And => {
                    let left = self.expression(lhs);
                    let right = self.expression(rhs);
                    match (kind, &left, &right) {
                        (Add | Sub, Value::Typed(ty), Value::Literal(_))
                            if matches!(
                                ty,
                                VariableType::Pointer(_) | VariableType::UnknownPointer
                            ) =>
                        {
                            left
                        }
                        _ => match left.join(right) {
                            Value::Conflict => Value::Unknown,
                            value => value,
                        },
                    }
                }
            },
            IRExpr::Deref(address) => self.dereference(address),
            IRExpr::ElementAddress { base, .. } => {
                let ty = match self.direct(base) {
                    Some(VariableType::Vector(element) | VariableType::Pointer(element)) => {
                        Some(VariableType::Pointer(element))
                    }
                    Some(VariableType::CString) => {
                        Some(VariableType::Pointer(Box::new(VariableType::Integer(8))))
                    }
                    _ => None,
                };
                self.known(ty)
            }
            IRExpr::CStringLength(_) => Value::Typed(VariableType::UnsignedInteger(64)),
            IRExpr::MemoryAddress { .. } => Value::Typed(VariableType::UnknownPointer),
        }
    }

    fn lowered_type(&self, expr: &IRExpr) -> VariableType {
        self.expression(expr)
            .result_type()
            .or_else(|| self.direct(expr))
            .or_else(|| match expr {
                IRExpr::Deref(address) => match address.as_ref() {
                    IRExpr::MemoryAddress { size, .. } => Some(VariableType::Unknown(*size)),
                    _ => None,
                },
                _ => None,
            })
            .unwrap_or(VariableType::Unknown(None))
    }
}

fn observe(current: &mut Option<Value>, next: Value) {
    *current = Some(match current.take() {
        Some(previous) => previous.join(next),
        None => next,
    });
}

fn function_returns(
    program: &Program,
    id: SyntheticFunctionId,
    seen: &mut HashSet<usize>,
) -> Option<Value> {
    if !seen.insert(id.id) {
        return None;
    }
    let Some(function) = program.functions.get(id.id) else {
        return Some(Value::Unknown);
    };
    let types = Types::new(function, &program.structs, &program.data);
    let mut returns = None;
    for (_, instr) in &function.body {
        instruction_returns(instr, &types, program, seen, &mut returns);
    }
    returns
}

fn instruction_returns(
    instr: &IRInst,
    types: &Types,
    program: &Program,
    seen: &mut HashSet<usize>,
    returns: &mut Option<Value>,
) {
    match instr {
        IRInst::Return(Some(value)) => observe(returns, types.expression(value)),
        IRInst::Return(None) => observe(returns, Value::Void),
        IRInst::CallSynthetic { function, .. } => {
            if let Some(value) = function_returns(program, *function, seen) {
                observe(returns, value);
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for child in then_branch.iter().chain(else_branch) {
                instruction_returns(child, types, program, seen, returns);
            }
        }
        IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
            for (_, child) in body {
                instruction_returns(child, types, program, seen, returns);
            }
        }
        _ => {}
    }
}

fn lower_return(
    instr: &mut IRInst,
    types: &Types,
    owner: SyntheticFunctionId,
    next_id: &mut usize,
) -> Option<IRInst> {
    match instr {
        IRInst::Return(value) => {
            let value = value.take()?;
            let ty = types.lowered_type(&value);
            let variable = VariableId {
                owner,
                id: *next_id,
            };
            *next_id += 1;
            Some(IRInst::DeclareAndAssignVariable {
                variable,
                ty,
                value,
            })
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            lower_flat(then_branch, types, owner, next_id);
            lower_flat(else_branch, types, owner, next_id);
            None
        }
        IRInst::While { body, .. } | IRInst::ForEach { body, .. } => {
            lower_with_offsets(body, types, owner, next_id);
            None
        }
        _ => None,
    }
}

fn lower_flat(
    body: &mut Vec<IRInst>,
    types: &Types,
    owner: SyntheticFunctionId,
    next_id: &mut usize,
) {
    let mut index = 0;
    while index < body.len() {
        if let Some(assignment) = lower_return(&mut body[index], types, owner, next_id) {
            body.insert(index, assignment);
            index += 1;
        }
        index += 1;
    }
}

fn lower_with_offsets(
    body: &mut Vec<(usize, IRInst)>,
    types: &Types,
    owner: SyntheticFunctionId,
    next_id: &mut usize,
) {
    let mut index = 0;
    while index < body.len() {
        if let Some(assignment) = lower_return(&mut body[index].1, types, owner, next_id) {
            body.insert(index, (body[index].0, assignment));
            index += 1;
        }
        index += 1;
    }
}

fn next_variable_id(function: &SyntheticFunction) -> usize {
    let mut effects = Effects::default();
    for (_, instr) in &function.body {
        effects.instruction(instr);
    }
    let max_used = effects
        .reads
        .iter()
        .chain(&effects.writes)
        .map(|variable| variable.id)
        .chain(
            function
                .parameters
                .iter()
                .filter_map(|parameter| match parameter {
                    Parameter::Slot { variable, .. } => Some(variable.id),
                    Parameter::Argument { .. } => None,
                }),
        )
        .max();
    max_used.map_or(0, |id| id + 1)
}

pub fn run(program: &mut Program) {
    let inferred = (0..program.functions.len())
        .map(|id| function_returns(program, SyntheticFunctionId { id }, &mut HashSet::new()))
        .collect::<Vec<_>>();
    for (id, (function, result)) in program.functions.iter_mut().zip(inferred).enumerate() {
        let conflicting = matches!(result, Some(Value::Conflict));
        function.return_type = result.and_then(Value::result_type);
        if conflicting {
            // Retain each candidate's computation as a local assignment at
            // the original return site, then leave the return value empty.
            let types = Types::new(function, &program.structs, &program.data);
            let mut next_id = next_variable_id(function);
            lower_with_offsets(
                &mut function.body,
                &types,
                SyntheticFunctionId { id },
                &mut next_id,
            );
        }
    }
}
