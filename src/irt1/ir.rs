use std::collections::HashSet;

use iced_x86::Register;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum NativeFlag {
    Carry,
    Parity,
    AuxCarry,
    Zero,
    Sign,
    Trap,
    InterruptEnable,
    Direction,
    Overflow,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub entry: Option<SyntheticFunctionId>,
    pub functions: Vec<SyntheticFunction>,
}

/// One shared partition lifted into a synthetic function.
#[derive(Debug, Clone)]
pub struct SyntheticFunction {
    pub entry_offset: usize,
    /// Register aliases whose low bytes are used by this function or a callee.
    pub parameters: Vec<Register>,
    /// Flags read in this body before this body defines them.
    pub external_flags: HashSet<NativeFlag>,
    pub body: Vec<(usize, IRInst)>,
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
    Bool,
}

#[derive(Debug, Clone)]
pub enum IRBinOpKind {
    Add,
    Sub,
    Shl,
    And,
    Or,
    Eq,
    UnsignedLt,
}

#[derive(Debug, Clone)]
pub enum IRExpr {
    BinOp {
        kind: IRBinOpKind,
        lhs: Box<IRExpr>,
        rhs: Box<IRExpr>,
    },
    Deref(Box<IRExpr>),
    Reg(Register),
    Flag(NativeFlag),
    CU8(u8),
    CU32(u32),
    CU64(u64),
    Variable(VariableId),
    Bool(bool),
    Not(Box<IRExpr>),
}

#[derive(Debug, Clone)]
pub enum IRInst {
    Assign {
        dest: IRExpr,
        src: IRExpr,
    },
    SetFlagsFrom {
        flags: HashSet<NativeFlag>,
        expr: IRExpr,
    },
    ClearFlags {
        flags: HashSet<NativeFlag>,
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

    /// Each arm is a terminal transfer: a synthetic call, jump, or end.
    If {
        condition: IRExpr,
        then_branch: Box<IRInst>,
        else_branch: Box<IRInst>,
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
