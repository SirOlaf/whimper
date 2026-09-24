use iced_x86::Register;

#[derive(Debug, Clone)]
pub struct Program {
    pub entry_address: usize,
    pub entry: Option<SyntheticFunctionId>,
    pub data: Vec<DataVariable>,
    pub functions: Vec<SyntheticFunction>,
}

/// A program-wide data slot. The address is also its stable identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataVariable {
    pub id: DataId,
    pub address: u64,
    pub name: String,
    pub ty: VariableType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DataId {
    pub id: u64,
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
    Input {
        ordinal: usize,
        size: usize,
    },
    /// An incoming machine register at the true entry point. The register
    /// alias carries the width, and its full register identifies the family.
    Native {
        ordinal: usize,
        register: Register,
    },
    /// An incoming register value passed by a synthetic predecessor. The
    /// register alias carries the width, and its full register identifies the family.
    Slot {
        variable: VariableId,
        register: Register,
    },
    /// A value passed between control-flow partitions with no native identity.
    Value {
        variable: VariableId,
        size: usize,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableType {
    Unknown(Option<usize>),
    /// A slot associated with this exact machine register.
    Register(Register),
    Bool,
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
    UnsignedLt,
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
    /// A byte address explicitly cast to a pointer for a memory operation.
    CastUnknownPtr {
        address: Box<IRExpr>,
        size: Option<usize>,
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
    Data(DataId),
    Bool(bool),
    Not(Box<IRExpr>),
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

    /// Each arm is a terminal transfer: a synthetic call, jump, or end.
    If {
        condition: IRExpr,
        then_branch: Vec<IRInst>,
        else_branch: Vec<IRInst>,
    },

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
