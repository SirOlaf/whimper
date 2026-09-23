use std::collections::HashSet;

use crate::irt0::ir::{IRExpr, IRInst as IRT0Inst, NativeFlag};

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

/// The identity of a synthetic function, independent of its future arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SyntheticFunctionId {
    pub id: usize,
}

#[derive(Debug, Clone)]
pub enum IRInst {
    /// A tier 0 instruction that does not branch.
    Linear(IRT0Inst),

    /// Each arm is a terminal transfer: a synthetic call, jump, or end.
    If {
        condition: IRExpr,
        then_branch: Box<IRInst>,
        else_branch: Box<IRInst>,
    },

    /// Tail call into a shared synthetic function; the caller does not resume.
    CallSynthetic { function: SyntheticFunctionId },

    /// A jump outside the locally lifted function.
    Jump(IRExpr),

    /// The source ends without another instruction.
    End,
}
