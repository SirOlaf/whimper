//! An auxiliary, width-aware arithmetic IR consumed by the shape analyzer.
//!
//! Sums live in Z/(2^bits): subtraction becomes a negative coefficient, constant
//! shifts become scaling, and like terms combine. Unsupported expressions are
//! retained as opaque atoms. Loads and potentially trapping operations are never
//! folded or reordered. This is a projection, not a replacement program IR.

use std::{
    collections::{BTreeMap, HashMap},
    fmt,
};

use super::{
    effects::repeatable,
    ir::{IRBinOpKind, IRExpr, IRInst, Parameter, SyntheticFunction, VariableId, VariableType},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Value {
    pub bits: Option<usize>,
    pub kind: Kind,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Constant(u64),
    Atom(IRExpr),
    /// Coefficients and the constant are reduced modulo the explicit width.
    Sum {
        terms: Vec<(Value, u64)>,
        constant: u64,
    },
    Binary {
        kind: IRBinOpKind,
        lhs: Box<Value>,
        rhs: Box<Value>,
    },
    Not(Box<Value>),
}

pub type Bindings = HashMap<VariableId, Value>;

#[derive(Default)]
pub struct Context {
    variables: HashMap<VariableId, VariableType>,
    arguments: HashMap<usize, VariableType>,
}

fn type_bits(ty: &VariableType) -> Option<usize> {
    match ty {
        VariableType::Integer(bits) | VariableType::UnsignedInteger(bits)
            if matches!(bits, 8 | 16 | 32 | 64) =>
        {
            Some(*bits)
        }
        VariableType::Unknown(Some(bytes)) if matches!(bytes, 1 | 2 | 4 | 8) => Some(bytes * 8),
        // Pointer arithmetic must not accidentally become integer arithmetic.
        _ => None,
    }
}

fn integer_bits(bits: Option<usize>) -> Option<usize> {
    bits.filter(|bits| matches!(bits, 8 | 16 | 32 | 64))
}

fn access_bits(bytes: usize) -> Option<usize> {
    bytes
        .checked_mul(8)
        .and_then(|bits| integer_bits(Some(bits)))
}

impl Context {
    pub fn direct_type(&self, expr: &IRExpr) -> Option<&VariableType> {
        match expr {
            IRExpr::Variable(variable) => self.variables.get(variable),
            IRExpr::Argument(ordinal) => self.arguments.get(ordinal),
            _ => None,
        }
    }

    pub fn from_function(function: &SyntheticFunction) -> Self {
        let mut context = Self::default();
        for parameter in &function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    context.arguments.insert(*ordinal, ty.clone());
                }
                Parameter::Slot { variable, ty } => {
                    context.variables.insert(*variable, ty.clone());
                }
            }
        }
        fn collect(context: &mut Context, instr: &IRInst) {
            match instr {
                IRInst::DeclareVariable { variable, ty }
                | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
                    context.variables.insert(*variable, ty.clone());
                }
                IRInst::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    for instr in then_branch.iter().chain(else_branch) {
                        collect(context, instr);
                    }
                }
                IRInst::While { body, .. } => {
                    for (_, instr) in body {
                        collect(context, instr);
                    }
                }
                IRInst::ForEach {
                    variable,
                    element_type,
                    body,
                    ..
                } => {
                    context.variables.insert(*variable, element_type.clone());
                    for (_, instr) in body {
                        collect(context, instr);
                    }
                }
                _ => {}
            }
        }
        for (_, instr) in &function.body {
            collect(&mut context, instr);
        }
        context
    }

    pub fn value(&self, expr: &IRExpr) -> Value {
        self.with_bindings(expr, &Bindings::new())
    }

    pub fn with_bindings(&self, expr: &IRExpr, bindings: &Bindings) -> Value {
        let atom = |bits| Value {
            bits,
            kind: Kind::Atom(expr.clone()),
        };
        match expr {
            IRExpr::Variable(variable) => bindings
                .get(variable)
                .cloned()
                .unwrap_or_else(|| atom(self.variables.get(variable).and_then(type_bits))),
            IRExpr::Argument(ordinal) => atom(self.arguments.get(ordinal).and_then(type_bits)),
            IRExpr::CU8(value) => Value::constant(*value as u64, 8),
            IRExpr::CU32(value) => Value::constant(*value as u64, 32),
            IRExpr::CU64(value) => Value::constant(*value, 64),
            IRExpr::BinOp { kind, lhs, rhs } => {
                let mut left = self.with_bindings(lhs, bindings);
                let mut right = self.with_bindings(rhs, bindings);
                // Literal operands adopt the operation width, not the width of
                // the immediate's encoding. Shift counts are independent.
                if *kind != IRBinOpKind::Shl {
                    if matches!(
                        lhs.as_ref(),
                        IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_)
                    ) {
                        if let (Kind::Constant(value), Some(bits)) =
                            (&left.kind, integer_bits(right.bits))
                        {
                            left = Value::constant(*value, bits);
                        }
                    } else if matches!(
                        rhs.as_ref(),
                        IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_)
                    ) {
                        if let (Kind::Constant(value), Some(bits)) =
                            (&right.kind, integer_bits(left.bits))
                        {
                            right = Value::constant(*value, bits);
                        }
                    }
                }
                let bits = if *kind == IRBinOpKind::Shl || left.bits == right.bits {
                    left.bits
                } else {
                    None
                };
                let comparison = matches!(
                    kind,
                    IRBinOpKind::Eq
                        | IRBinOpKind::Ne
                        | IRBinOpKind::SignedGt
                        | IRBinOpKind::SignedLe
                        | IRBinOpKind::UnsignedLt
                        | IRBinOpKind::UnsignedGe
                        | IRBinOpKind::LogicalAnd
                        | IRBinOpKind::Or
                );
                // Infer the result width from operands even for effectful
                // operations, but preserve their original evaluation intact.
                if !repeatable(expr) {
                    return atom(if comparison { Some(1) } else { bits });
                }
                if let Some(bits) = integer_bits(bits) {
                    match kind {
                        IRBinOpKind::Add => return sum(bits, [(left, 1), (right, 1)]),
                        IRBinOpKind::Sub => return sum(bits, [(left, 1), (right, u64::MAX)]),
                        IRBinOpKind::Mul => {
                            if let Kind::Constant(factor) = right.kind {
                                return sum(bits, [(left, factor)]);
                            }
                            if let Kind::Constant(factor) = left.kind {
                                return sum(bits, [(right, factor)]);
                            }
                        }
                        IRBinOpKind::Shl => {
                            if let Kind::Constant(shift) = right.kind
                                && shift < bits as u64
                            {
                                return sum(bits, [(left, 1u64 << shift)]);
                            }
                        }
                        _ => {}
                    }
                }
                Value {
                    bits: if comparison { Some(1) } else { bits },
                    kind: Kind::Binary {
                        kind: kind.clone(),
                        lhs: Box::new(left),
                        rhs: Box::new(right),
                    },
                }
            }
            IRExpr::Not(inner) if repeatable(expr) => self.with_bindings(inner, bindings).negated(),
            IRExpr::Convert { target, .. } => atom(access_bits(target.size)),
            IRExpr::Deref(address) => {
                let bits = match address.as_ref() {
                    IRExpr::MemoryAddress { size, .. } => size.and_then(access_bits),
                    IRExpr::ElementAddress { element_size, .. } => access_bits(*element_size),
                    _ => None,
                };
                atom(bits)
            }
            _ => atom(None),
        }
    }
}

fn mask(bits: usize) -> u64 {
    u64::MAX >> (64 - bits)
}

fn sum(bits: usize, values: impl IntoIterator<Item = (Value, u64)>) -> Value {
    let mut terms = BTreeMap::<Value, u64>::new();
    let mut constant = 0u64;
    for (value, coefficient) in values {
        match value.kind {
            Kind::Constant(value) => {
                constant = constant.wrapping_add(value.wrapping_mul(coefficient))
            }
            Kind::Sum {
                terms: nested,
                constant: bias,
            } => {
                constant = constant.wrapping_add(bias.wrapping_mul(coefficient));
                for (term, factor) in nested {
                    let entry = terms.entry(term).or_default();
                    *entry = entry.wrapping_add(factor.wrapping_mul(coefficient));
                }
            }
            _ => {
                let entry = terms.entry(value).or_default();
                *entry = entry.wrapping_add(coefficient);
            }
        }
    }
    constant &= mask(bits);
    let terms = terms
        .into_iter()
        .filter_map(|(term, coefficient)| {
            let coefficient = coefficient & mask(bits);
            (coefficient != 0).then_some((term, coefficient))
        })
        .collect::<Vec<_>>();
    if terms.is_empty() {
        return Value::constant(constant, bits);
    }
    if constant == 0 && terms.len() == 1 && terms[0].1 == 1 {
        return terms[0].0.clone();
    }
    Value {
        bits: Some(bits),
        kind: Kind::Sum { terms, constant },
    }
}

impl Value {
    fn constant(value: u64, bits: usize) -> Self {
        Self {
            bits: Some(bits),
            kind: Kind::Constant(value & mask(bits)),
        }
    }

    pub fn subtract(&self, rhs: &Self) -> Option<Self> {
        let bits = self.bits.filter(|bits| matches!(bits, 8 | 16 | 32 | 64))?;
        (rhs.bits == Some(bits)).then(|| sum(bits, [(self.clone(), 1), (rhs.clone(), u64::MAX)]))
    }

    pub fn negated(self) -> Self {
        match self.kind {
            Kind::Not(inner) => *inner,
            Kind::Binary { kind, lhs, rhs } => {
                if matches!(kind, IRBinOpKind::Or | IRBinOpKind::LogicalAnd) {
                    return Self {
                        bits: Some(1),
                        kind: Kind::Binary {
                            kind: if kind == IRBinOpKind::Or {
                                IRBinOpKind::LogicalAnd
                            } else {
                                IRBinOpKind::Or
                            },
                            lhs: Box::new(lhs.negated()),
                            rhs: Box::new(rhs.negated()),
                        },
                    };
                }
                let opposite = match kind {
                    IRBinOpKind::Eq => Some(IRBinOpKind::Ne),
                    IRBinOpKind::Ne => Some(IRBinOpKind::Eq),
                    IRBinOpKind::SignedGt => Some(IRBinOpKind::SignedLe),
                    IRBinOpKind::SignedLe => Some(IRBinOpKind::SignedGt),
                    IRBinOpKind::UnsignedLt => Some(IRBinOpKind::UnsignedGe),
                    IRBinOpKind::UnsignedGe => Some(IRBinOpKind::UnsignedLt),
                    _ => None,
                };
                let value = Self {
                    bits: self.bits,
                    kind: Kind::Binary {
                        kind: opposite.clone().unwrap_or(kind),
                        lhs,
                        rhs,
                    },
                };
                if opposite.is_some() {
                    value
                } else {
                    Self {
                        bits: Some(1),
                        kind: Kind::Not(Box::new(value)),
                    }
                }
            }
            _ => Self {
                bits: Some(1),
                kind: Kind::Not(Box::new(self)),
            },
        }
    }

    pub fn reads(&self, variable: VariableId) -> bool {
        match &self.kind {
            Kind::Atom(expr) => super::effects::Effects::of_expression(expr)
                .reads
                .contains(&variable),
            Kind::Sum { terms, .. } => terms.iter().any(|(value, _)| value.reads(variable)),
            Kind::Binary { lhs, rhs, .. } => lhs.reads(variable) || rhs.reads(variable),
            Kind::Not(inner) => inner.reads(variable),
            Kind::Constant(_) => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            Kind::Constant(value) => write!(f, "0x{value:x}"),
            Kind::Atom(IRExpr::Variable(variable)) => write!(f, "v{}", variable.id),
            Kind::Atom(IRExpr::Argument(ordinal)) => write!(f, "arg{ordinal}"),
            Kind::Atom(expr) => write!(f, "opaque({expr:?})"),
            Kind::Sum { terms, constant } => {
                write!(f, "(")?;
                for (index, (term, coefficient)) in terms.iter().enumerate() {
                    let negative = *coefficient > mask(self.bits.unwrap()) / 2;
                    let magnitude = if negative {
                        coefficient.wrapping_neg() & mask(self.bits.unwrap())
                    } else {
                        *coefficient
                    };
                    if index > 0 {
                        write!(f, " {} ", if negative { "-" } else { "+" })?;
                    } else if negative {
                        write!(f, "-")?;
                    }
                    if magnitude != 1 {
                        write!(f, "{magnitude}*")?;
                    }
                    write!(f, "{term}")?;
                }
                if *constant != 0 {
                    write!(f, " + 0x{constant:x}")?;
                }
                write!(f, ") mod 2^{}", self.bits.unwrap())
            }
            Kind::Binary { kind, lhs, rhs } => write!(f, "{kind:?}({lhs}, {rhs})"),
            Kind::Not(inner) => write!(f, "!({inner})"),
        }
    }
}
