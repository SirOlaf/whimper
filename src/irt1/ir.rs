use std::collections::HashSet;

use crate::irt0::ir::{IRExpr as IRT0Expr, IRInst as IRT0Inst, NativeFlag};

#[derive(Debug, Clone)]
pub struct Program {
    pub entry: Option<SyntheticFunctionId>,
    pub functions: Vec<SyntheticFunction>,
}

/// One shared partition lifted into a synthetic function.
#[derive(Debug, Clone)]
pub struct SyntheticFunction {
    pub entry_offset: usize,
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
pub enum IRExpr {
    Native(IRT0Expr),
    Variable(VariableId),
    Bool(bool),
    Eq(Box<IRExpr>, Box<IRExpr>),
    UnsignedLt(Box<IRExpr>, Box<IRExpr>),
    Or(Box<IRExpr>, Box<IRExpr>),
    Not(Box<IRExpr>),
}

#[derive(Debug, Clone)]
pub enum IRInst {
    /// A tier 0 instruction that does not branch.
    Linear(IRT0Inst),

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
    },

    /// A jump outside the locally lifted function.
    Jump(IRT0Expr),

    /// The source ends without another instruction.
    End,
}
