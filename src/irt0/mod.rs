pub mod ir;
pub mod prune_flags;

pub fn lift(code: &[u8], base_offset: usize) -> ir::Program {
    let program = ir::lift_to_irt0(code, base_offset);
    prune_flags::tr(program)
}
