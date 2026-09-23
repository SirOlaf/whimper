#[derive(Debug, Clone)]
pub struct Program {
    pub entry: Option<SyntheticFunctionId>,
    pub functions: Vec<SyntheticFunction>,
    /// Named and inferred struct definitions used by tier 5 types.
    pub structs: Vec<StructDefinition>,
}

/// One shared partition lifted into a synthetic function.
#[derive(Debug, Clone)]
pub struct SyntheticFunction {
    pub entry_offset: usize,
    pub parameters: Vec<Parameter>,
    pub body: Vec<(usize, IRInst)>,
}

#[derive(Debug, Clone)]
pub enum Parameter {
    /// An incoming value supplied by the caller of the entry function.
    Argument { ordinal: usize, ty: VariableType },
    /// An incoming value passed by a synthetic predecessor.
    Slot {
        variable: VariableId,
        ty: VariableType,
    },
}

/// The identity of a synthetic function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SyntheticFunctionId {
    pub id: usize,
}

/// Variable numbers are assigned densely within each synthetic function
/// when tier 4 is translated into tier 5.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariableId {
    pub owner: SyntheticFunctionId,
    pub id: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructId {
    pub id: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<StructField>,
}

/// Identifies a loop when a recovered back edge crosses another loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoopId {
    pub id: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VariableType {
    /// A value with an optional known width in bytes.
    Unknown(Option<usize>),
    /// A pointer whose pointee type has not been recovered.
    UnknownPointer,
    /// A pointer whose pointee type is supported by tier 5 evidence.
    Pointer(Box<VariableType>),
    /// An address of homogeneous elements with unknown length. This is not
    /// an owning container and implies neither a capacity nor bounds checks.
    Vector(Box<VariableType>),
    /// A struct definition in this tier's program.
    Struct(StructId),
    Bool,
    /// Integer-shaped, with no signedness evidence. Width is in bits.
    Integer(usize),
    /// An unsigned comparison establishes how the value is interpreted.
    UnsignedInteger(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub offset: usize,
    pub ty: VariableType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRBinOpKind {
    Add,
    Sub,
    Mul,
    Shl,
    /// Logical right shift, with the width of the left operand.
    Shr,
    BitOr,
    And,
    Or,
    Eq,
    SignedGt,
    Ne,
    UnsignedLt,
    UnsignedGe,
}

/// An integer interpretation, independent of a machine register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntegerType {
    pub size: usize,
    pub signed: bool,
}

impl std::fmt::Display for IntegerType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            if self.signed { "i" } else { "u" },
            self.size * 8
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRExpr {
    BinOp {
        kind: IRBinOpKind,
        lhs: Box<IRExpr>,
        rhs: Box<IRExpr>,
    },
    Deref(Box<IRExpr>),
    /// A memory address and its access width, independent of its pointer type.
    MemoryAddress {
        address: Box<IRExpr>,
        /// Memory access width in bytes, not the pointee type's size.
        size: Option<usize>,
    },
    /// Address of an element, without reading it. Address arithmetic wraps
    /// at 64 bits; `index` retains its original integer conversions.
    ElementAddress {
        base: Box<IRExpr>,
        index: Box<IRExpr>,
        /// Both the element stride and memory access width, in bytes.
        element_size: usize,
    },
    Argument(usize),
    /// Numeric conversion: interpret the input using `source`, then convert
    /// to `target`, truncating modulo its width. No register alias semantics.
    Convert {
        value: Box<IRExpr>,
        source: IntegerType,
        target: IntegerType,
    },
    CU8(u8),
    CU32(u32),
    CU64(u64),
    Variable(VariableId),
    Bool(bool),
    Not(Box<IRExpr>),
}

/// A direct slot and its constant byte offset in a memory address.
pub(crate) fn field_address(expr: &IRExpr) -> Option<(&IRExpr, usize)> {
    match expr {
        IRExpr::MemoryAddress { address, .. } => field_address(address),
        IRExpr::Argument(_) | IRExpr::Variable(_) => Some((expr, 0)),
        IRExpr::BinOp { kind, lhs, rhs } => {
            let constant = |expr: &IRExpr| match expr {
                IRExpr::CU8(value) => Some(*value as usize),
                IRExpr::CU32(value) => Some(*value as usize),
                IRExpr::CU64(value) if *value <= isize::MAX as u64 => usize::try_from(*value).ok(),
                _ => None,
            };
            match kind {
                IRBinOpKind::Add => {
                    if let (Some((base, offset)), Some(extra)) = (field_address(lhs), constant(rhs))
                    {
                        offset.checked_add(extra).map(|offset| (base, offset))
                    } else if let (Some(extra), Some((base, offset))) =
                        (constant(lhs), field_address(rhs))
                    {
                        offset.checked_add(extra).map(|offset| (base, offset))
                    } else {
                        None
                    }
                }
                IRBinOpKind::Sub => {
                    let (base, offset) = field_address(lhs)?;
                    offset
                        .checked_sub(constant(rhs)?)
                        .map(|offset| (base, offset))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub enum LoopCondition {
    /// Check before entering the body and after each iteration.
    Before { offset: usize, expression: IRExpr },
    /// Check after each iteration; the body runs at least once.
    After { offset: usize, expression: IRExpr },
}

#[derive(Debug, Clone)]
pub enum IRInst {
    Assign {
        dest: IRExpr,
        src: IRExpr,
    },
    Return(Option<IRExpr>),

    DeclareVariable {
        variable: VariableId,
        ty: VariableType,
    },
    DeclareAndAssignVariable {
        variable: VariableId,
        ty: VariableType,
        value: IRExpr,
    },
    AssignVariable {
        variable: VariableId,
        value: IRExpr,
    },
    /// Read a non-absolute address into a local Unknown slot.
    LoadVariable {
        variable: VariableId,
        address: IRExpr,
    },
    /// Write a local Unknown slot back to a non-absolute address.
    StoreVariable {
        address: IRExpr,
        variable: VariableId,
    },

    /// Structured branches may fall through to a shared continuation.
    If {
        condition: IRExpr,
        then_branch: Vec<IRInst>,
        else_branch: Vec<IRInst>,
    },

    /// Repeat while the condition holds. Before checks model `while`, and
    /// After checks model `do ... while`. Break resumes after the loop.
    /// Source offsets are retained for the top-level instructions in the loop.
    While {
        label: Option<LoopId>,
        entry_offset: usize,
        condition: LoopCondition,
        body: Vec<(usize, IRInst)>,
    },

    /// Exit the enclosing Loop.
    Break,

    /// Continue at the beginning of the enclosing Loop.
    Continue,

    /// Continue a specific enclosing loop, including across nested loops.
    ContinueLoop(LoopId),

    /// Tail call into a shared synthetic function; the caller does not resume.
    CallSynthetic {
        function: SyntheticFunctionId,
        arguments: Vec<IRExpr>,
    },

    /// A jump outside the locally lifted function.
    Jump(IRExpr),

    /// The source ends without another instruction.
    End,
}
