//! Shape recognizers consume Tier 6 IR and normalized arithmetic values.

mod assignment;
mod boolean;
mod cstring;
mod loops;
mod modulo;
mod vector;
pub mod visit;

use super::{
    arithmetic::{Context, Kind, Value},
    effects::{Effects, repeatable},
    ir::{IRBinOpKind, IRExpr, IRInst, LoopCondition, VariableId, VariableType},
};

pub use assignment::{compound_assignment, temporary_binary_assignment};
pub use boolean::{boolean_return, de_morgan};
pub use cstring::cstring_empty_check;
pub use loops::{LoopAnalysis, analyze};
pub use modulo::guarded_modulo;
pub use vector::vector_iteration;

fn unsigned_constant(expr: &IRExpr) -> Option<u64> {
    match expr {
        IRExpr::CU8(value) => Some(*value as u64),
        IRExpr::CU32(value) => Some(*value as u64),
        IRExpr::CU64(value) => Some(*value),
        _ => None,
    }
}

/// Add new read-only shape collectors to this list so they share one walk.
pub fn collect_loop_analyses(program: &super::ir::Program) -> Vec<LoopAnalysis> {
    let mut loops = loops::Collector::default();
    visit::walk(program, &mut [&mut loops]);
    loops.0
}
