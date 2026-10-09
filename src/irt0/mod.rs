pub mod ir;

pub fn lift(code: &[u8], base_address: usize) -> ir::Program {
    ir::lift(code, base_address)
}
