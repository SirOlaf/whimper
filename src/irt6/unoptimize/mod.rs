//! Small, ordered rewrite rules with a bounded local fixed point.
//!
//! Entry facts are invalidated by writes. Loop bodies retain only invariant
//! facts. Each successful rewrite restarts rule selection; a recognizer can
//! therefore rely on shapes established by earlier, independent rules.

mod facts;
mod report;
mod rules;
mod sequences;

use std::collections::HashMap;

use super::{
    arithmetic::Context,
    eliminate_variables, infer_returns, infer_types,
    ir::Program,
    relocate_variables,
    shapes::{self, LoopAnalysis},
};
use facts::Facts;
use sequences::{
    MAX_REWRITES, collapse_temporary_assignments, collect_uses, recover_vector_iterations, sequence,
};

#[derive(Debug, Clone, Copy)]
pub struct Options {
    /// Allow rewrites that rely on assumptions about otherwise unknown values.
    pub allow_assumptions: bool,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            allow_assumptions: true,
        }
    }
}

#[derive(Debug)]
pub struct Rewrite {
    pub offset: usize,
    pub rule: &'static str,
}

#[derive(Debug, Default)]
pub struct Report {
    pub before: Vec<LoopAnalysis>,
    pub rewrites: Vec<Rewrite>,
    pub remaining: Vec<LoopAnalysis>,
    pub budget_exhausted: bool,
}

pub fn run(program: &mut Program) -> Report {
    run_with_options(program, Options::default())
}

pub fn run_with_options(program: &mut Program, options: Options) -> Report {
    let mut report = Report {
        before: shapes::collect_loop_analyses(program),
        ..Report::default()
    };
    for function in &mut program.functions {
        let context = Context::from_function(function);
        sequence(
            function
                .body
                .iter_mut()
                .map(|(offset, instr)| (*offset, instr)),
            &context,
            Facts::default(),
            &options,
            &mut report,
        );
        let mut uses = HashMap::new();
        for (_, instr) in &function.body {
            collect_uses(instr, &mut uses);
        }
        collapse_temporary_assignments(
            &mut function.body,
            function.entry_offset,
            &context,
            &uses,
            &mut report,
        );
        // Collapsing a temporary can expose the modulo assignment directly
        // inside its guard, so run the local rules on the resulting IR.
        sequence(
            function
                .body
                .iter_mut()
                .map(|(offset, instr)| (*offset, instr)),
            &context,
            Facts::default(),
            &options,
            &mut report,
        );
        loop {
            let mut uses = HashMap::new();
            for (_, instr) in &function.body {
                collect_uses(instr, &mut uses);
            }
            if !recover_vector_iterations(
                &mut function.body,
                function.entry_offset,
                &context,
                &uses,
                &mut report,
            ) || report.rewrites.len() >= MAX_REWRITES
            {
                break;
            }
        }
    }
    infer_types::run(program);
    for function in &mut program.functions {
        let context = Context::from_function(function);
        sequence(
            function
                .body
                .iter_mut()
                .map(|(offset, instr)| (*offset, instr)),
            &context,
            Facts::default(),
            &options,
            &mut report,
        );
    }
    // Type promotion exposes CString length checks. Re-scope locals after
    // those rewrites, then collapse copies made adjacent by the move.
    relocate_variables::run(program);
    infer_returns::run(program);
    eliminate_variables::run(program);
    report.remaining = shapes::collect_loop_analyses(program);
    report
}
