# Tier 0: native instruction lifting

Tier 0 is the only IR tier that decodes x86_64 bytes with `iced-x86`. `ir.rs` owns a linear program of offset-tagged operations and expressions; registers and flags are still explicit. One native instruction can produce several IR operations, and `prune_flags.rs` removes unused flag writes.

Lift each supported native instruction fully here. Return Tier 0 IR, never an `iced_x86::Instruction`, to the next tier.
