//! Fold scalar values across partitions before they become loop/merge slots.
//! Memory reads are never constants, even at a constant data address.

use std::collections::{HashMap, HashSet};

use super::{
    ir::{
        DataId, IRBinOpKind, IRExpr, IRInst, Parameter, Program, SyntheticFunction, VariableId,
        VariableType,
    },
    values,
};

#[derive(Clone, PartialEq, Eq)]
enum Value {
    Unseen,
    Constant(IRExpr),
    Dynamic,
}

impl Value {
    fn join(&mut self, other: Self) -> bool {
        let next = match (&*self, other) {
            (_, Self::Unseen) => self.clone(),
            (Self::Unseen, value) => value,
            (Self::Constant(a), Self::Constant(b)) if *a == b => self.clone(),
            _ => Self::Dynamic,
        };
        let changed = *self != next;
        *self = next;
        changed
    }
}

struct Types {
    variables: HashMap<VariableId, usize>,
    arguments: HashMap<usize, usize>,
    data: HashMap<DataId, usize>,
}

impl Types {
    fn new(function: &SyntheticFunction, data: &[super::ir::DataVariable]) -> Self {
        let mut result = Self {
            variables: HashMap::new(),
            arguments: HashMap::new(),
            data: data
                .iter()
                .filter_map(|item| match item.ty {
                    VariableType::Unknown(Some(size)) => Some((item.id, size)),
                    _ => None,
                })
                .collect(),
        };
        for parameter in &function.parameters {
            match parameter {
                Parameter::Slot { variable, register } => {
                    result.variables.insert(*variable, register.size());
                }
                Parameter::Value { variable, size } => {
                    result.variables.insert(*variable, *size);
                }
                Parameter::Native { ordinal, register } => {
                    result.arguments.insert(*ordinal, register.size());
                }
                Parameter::Input { ordinal, size } => {
                    result.arguments.insert(*ordinal, *size);
                }
            }
        }
        for (_, instr) in &function.body {
            if let IRInst::DeclareVariable { variable, ty } = instr {
                let size = match ty {
                    VariableType::Register(register) => Some(register.size()),
                    VariableType::Unknown(size) => *size,
                    VariableType::Bool => Some(1),
                };
                if let Some(size) = size {
                    result.variables.insert(*variable, size);
                }
            }
        }
        result
    }

    fn fold(&self, expr: &IRExpr, known: &HashMap<VariableId, Value>) -> IRExpr {
        match expr {
            IRExpr::Variable(variable) => match known.get(variable) {
                Some(Value::Constant(value)) => value.clone(),
                _ => expr.clone(),
            },
            IRExpr::BinOp { kind, lhs, rhs } => {
                // Determine operation width before substituting its operands.
                let size = if values::constant(lhs).is_some()
                    && !matches!(kind, IRBinOpKind::Shl | IRBinOpKind::Shr)
                {
                    values::width(rhs, &self.variables, &self.arguments, &self.data)
                } else {
                    values::width(lhs, &self.variables, &self.arguments, &self.data)
                };
                let left = self.fold(lhs, known);
                let right = self.fold(rhs, known);
                match size {
                    Some(size) => values::binary(kind.clone(), left, right, size),
                    None => IRExpr::BinOp {
                        kind: kind.clone(),
                        lhs: Box::new(left),
                        rhs: Box::new(right),
                    },
                }
            }
            IRExpr::Convert {
                value,
                source,
                target,
            } => values::convert(
                self.fold(value, known),
                source.size,
                target.size,
                source.signed,
            ),
            IRExpr::Not(value) => match self.fold(value, known) {
                IRExpr::Bool(value) => IRExpr::Bool(!value),
                value => IRExpr::Not(Box::new(value)),
            },
            IRExpr::Deref(address) => IRExpr::Deref(Box::new(self.fold(address, known))),
            IRExpr::CastUnknownPtr { address, size } => IRExpr::CastUnknownPtr {
                address: Box::new(self.fold(address, known)),
                size: *size,
            },
            _ => expr.clone(),
        }
    }

    fn evaluate(&self, expr: &IRExpr, known: &HashMap<VariableId, Value>) -> Value {
        let folded = self.fold(expr, known);
        if values::constant(&folded).is_some() {
            return Value::Constant(folded);
        }
        match expr {
            IRExpr::Variable(variable) => known.get(variable).cloned().unwrap_or(Value::Dynamic),
            IRExpr::Convert { value, .. } | IRExpr::Not(value) => match self.evaluate(value, known)
            {
                Value::Unseen => Value::Unseen,
                _ => Value::Dynamic,
            },
            IRExpr::BinOp { lhs, rhs, .. } => {
                match (self.evaluate(lhs, known), self.evaluate(rhs, known)) {
                    (Value::Dynamic, _) | (_, Value::Dynamic) => Value::Dynamic,
                    (Value::Unseen, _) | (_, Value::Unseen) => Value::Unseen,
                    _ => Value::Dynamic,
                }
            }
            _ => Value::Dynamic,
        }
    }
}

fn analyze(
    instr: &IRInst,
    known: &mut HashMap<VariableId, Value>,
    types: &Types,
    edges: &mut Vec<(usize, Vec<Value>)>,
) {
    match instr {
        IRInst::AssignVariable { variable, value } => {
            known.insert(*variable, types.evaluate(value, known));
        }
        IRInst::LoadVariable { variable, .. } => {
            known.insert(*variable, Value::Dynamic);
        }
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src,
        } => {
            known.insert(*variable, types.evaluate(src, known));
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for branch in [then_branch, else_branch] {
                let mut local = known.clone();
                for instr in branch {
                    analyze(instr, &mut local, types, edges);
                }
            }
        }
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            edges.push((
                function.id,
                arguments
                    .iter()
                    .map(|arg| types.evaluate(arg, known))
                    .collect(),
            ));
        }
        _ => {}
    }
}

fn rewrite(
    instr: IRInst,
    known: &mut HashMap<VariableId, Value>,
    types: &Types,
    removed_parameters: &[HashSet<usize>],
) -> Option<IRInst> {
    Some(match instr {
        IRInst::AssignVariable { variable, value } => {
            let value = types.fold(&value, known);
            let state = types.evaluate(&value, known);
            let constant = matches!(state, Value::Constant(_));
            known.insert(variable, state);
            if constant {
                return None;
            }
            IRInst::AssignVariable { variable, value }
        }
        IRInst::Assign {
            dest: IRExpr::Variable(variable),
            src,
        } => {
            return rewrite(
                IRInst::AssignVariable {
                    variable,
                    value: src,
                },
                known,
                types,
                removed_parameters,
            );
        }
        IRInst::Assign { dest, src } => IRInst::Assign {
            dest: types.fold(&dest, known),
            src: types.fold(&src, known),
        },
        IRInst::LoadVariable { variable, address } => {
            let address = types.fold(&address, known);
            known.insert(variable, Value::Dynamic);
            IRInst::LoadVariable { variable, address }
        }
        IRInst::StoreVariable { address, variable } => {
            let address = types.fold(&address, known);
            match types.fold(&IRExpr::Variable(variable), known) {
                IRExpr::Variable(variable) => IRInst::StoreVariable { address, variable },
                src => IRInst::Assign {
                    dest: IRExpr::Deref(Box::new(address)),
                    src,
                },
            }
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let branch = |body: Vec<IRInst>| {
                let mut local = known.clone();
                body.into_iter()
                    .filter_map(|instr| rewrite(instr, &mut local, types, removed_parameters))
                    .collect()
            };
            IRInst::If {
                condition: types.fold(&condition, known),
                then_branch: branch(then_branch),
                else_branch: branch(else_branch),
            }
        }
        IRInst::CallSynthetic {
            function,
            arguments,
        } => IRInst::CallSynthetic {
            function,
            arguments: arguments
                .into_iter()
                .enumerate()
                .filter(|(index, _)| !removed_parameters[function.id].contains(index))
                .map(|(_, arg)| types.fold(&arg, known))
                .collect(),
        },
        IRInst::Return(value) => IRInst::Return(value.map(|value| types.fold(&value, known))),
        IRInst::Jump(value) => IRInst::Jump(types.fold(&value, known)),
        instr => instr,
    })
}

pub(super) fn run(program: &mut Program) {
    let Some(entry) = program.entry else { return };
    let types: Vec<_> = program
        .functions
        .iter()
        .map(|function| Types::new(function, &program.data))
        .collect();
    let mut incoming: Vec<Vec<_>> = program
        .functions
        .iter()
        .map(|function| vec![Value::Unseen; function.parameters.len()])
        .collect();
    incoming[entry.id].fill(Value::Dynamic);
    let mut reachable = HashSet::from([entry.id]);
    let mut pending = vec![entry.id];
    while let Some(id) = pending.pop() {
        let function = &program.functions[id];
        let mut known = HashMap::new();
        for (parameter, value) in function.parameters.iter().zip(&incoming[id]) {
            if let Parameter::Slot { variable, .. } | Parameter::Value { variable, .. } = parameter
            {
                known.insert(*variable, value.clone());
            }
        }
        let mut edges = Vec::new();
        for (_, instr) in &function.body {
            analyze(instr, &mut known, &types[id], &mut edges);
        }
        for (target, arguments) in edges {
            let mut changed = reachable.insert(target);
            for (value, argument) in incoming[target].iter_mut().zip(arguments) {
                changed |= value.join(argument);
            }
            if changed {
                pending.push(target);
            }
        }
    }
    let removed: Vec<HashSet<_>> = incoming
        .iter()
        .map(|values| {
            values
                .iter()
                .enumerate()
                .filter_map(|(index, value)| matches!(value, Value::Constant(_)).then_some(index))
                .collect()
        })
        .collect();
    for (id, function) in program.functions.iter_mut().enumerate() {
        if !reachable.contains(&id) {
            continue;
        }
        let mut known = HashMap::new();
        function.parameters = std::mem::take(&mut function.parameters)
            .into_iter()
            .enumerate()
            .filter_map(|(index, parameter)| {
                if let Parameter::Slot { variable, .. } | Parameter::Value { variable, .. } =
                    &parameter
                {
                    known.insert(*variable, incoming[id][index].clone());
                }
                (!removed[id].contains(&index)).then_some(parameter)
            })
            .collect();
        function.body = std::mem::take(&mut function.body)
            .into_iter()
            .filter_map(|(offset, instr)| {
                rewrite(instr, &mut known, &types[id], &removed).map(|instr| (offset, instr))
            })
            .collect();
        // All local constant definitions were substituted at their uses. Their
        // now-unused declarations must not become phantom higher-tier slots.
        let mut used = HashSet::new();
        for (_, instr) in &function.body {
            used_variables(instr, &mut used);
        }
        function.body.retain(|(_, instr)| {
            !matches!(instr, IRInst::DeclareVariable { variable, .. }
            if !used.contains(variable))
        });
    }
}

fn used_variables(instr: &IRInst, used: &mut HashSet<VariableId>) {
    fn expression(expr: &IRExpr, used: &mut HashSet<VariableId>) {
        match expr {
            IRExpr::Variable(variable) => {
                used.insert(*variable);
            }
            IRExpr::BinOp { lhs, rhs, .. } => {
                expression(lhs, used);
                expression(rhs, used);
            }
            IRExpr::Convert { value, .. }
            | IRExpr::Not(value)
            | IRExpr::Deref(value)
            | IRExpr::CastUnknownPtr { address: value, .. } => expression(value, used),
            _ => {}
        }
    }
    match instr {
        IRInst::Assign { dest, src } => {
            expression(dest, used);
            expression(src, used);
        }
        IRInst::AssignVariable { variable, value } => {
            used.insert(*variable);
            expression(value, used);
        }
        IRInst::LoadVariable { variable, address }
        | IRInst::StoreVariable { variable, address } => {
            used.insert(*variable);
            expression(address, used);
        }
        IRInst::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression(condition, used);
            for instr in then_branch.iter().chain(else_branch) {
                used_variables(instr, used);
            }
        }
        IRInst::CallSynthetic { arguments, .. } => {
            for arg in arguments {
                expression(arg, used);
            }
        }
        IRInst::Return(Some(value)) | IRInst::Jump(value) => expression(value, used),
        _ => {}
    }
}
