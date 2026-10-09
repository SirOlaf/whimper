# Whimper

Whimper is a work-in-progress Rust decompiler for x86_64 PE code. `iced-x86` decodes machine instructions and the representation is progressively lifted through multiple stages.

## Repository rules

- Every tier owns a complete IR in its `ir.rs`. Translate the previous tier's program into that IR at the tier boundary; do not reuse previous-tier nodes or type aliases as the new tier's representation.
- Lift native instructions into Tier 0 operations. Higher tiers consume IR only: do not pass `iced_x86::Instruction` through the pipeline or decode, inspect, or match native instructions there. Register identities may remain as IR data in the early tiers while their semantics are being lifted.
- Preserve program behavior and relevant source offsets as transformations raise the representation. Keep unsupported behavior explicit rather than silently dropping it.
- Do not write tests for this work; manual confirmation is sufficient.
