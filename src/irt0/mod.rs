mod ir;
mod prune_flags;

pub fn lift(code: &[u8]) -> ir::Program {
    let program = ir::lift_to_irt0(code, 0);
    prune_flags::tr(program)
}
