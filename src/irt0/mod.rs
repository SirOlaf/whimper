pub mod ir;

pub fn lift(code: &[u8], base_offset: usize) -> ir::Program {
    ir::lift_to_irt0(code, base_offset)
}
