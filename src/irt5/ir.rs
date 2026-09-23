#[derive(Debug, Clone)]
pub struct Program {
    pub entry: Option<SyntheticFunctionId>,
    pub functions: Vec<SyntheticFunction>,
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

/// Variable numbers are local to their owning synthetic function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariableId {
    pub owner: SyntheticFunctionId,
    pub id: usize,
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
    Bool,
    /// Integer-shaped, with no signedness evidence. Width is in bits.
    Integer(usize),
    /// An unsigned comparison establishes how the value is interpreted.
    UnsignedInteger(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRBinOpKind {
    Add,
    Sub,
    Shl,
    And,
    Or,
    Eq,
    UnsignedLt,
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
    Argument(usize),
    ExtractBytes {
        value: Box<IRExpr>,
        offset: usize,
        size: usize,
    },
    ZeroExtend {
        value: Box<IRExpr>,
        size: usize,
    },
    ReplaceBytes {
        original: Box<IRExpr>,
        value: Box<IRExpr>,
        offset: usize,
        size: usize,
    },
    CU8(u8),
    CU32(u32),
    CU64(u64),
    Variable(VariableId),
    Bool(bool),
    Not(Box<IRExpr>),
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
