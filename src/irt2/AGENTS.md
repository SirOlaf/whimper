# Tier 2: register and memory semantics

Tier 2 lifts Tier 1 into its own IR with local value slots, numeric conversions, integer arithmetic, and explicit memory loads and stores. Resolve byte extraction, extension, and partial-register replacement here; these operations must not become nodes in higher tiers. Fold scalar constants and propagate them across partitions without treating memory at constant addresses as a constant. Native register identities remain as parameter and slot metadata while register effects are translated into expressions and assignments.

Translate Tier 1 nodes into Tier 2 nodes. Do not inspect native instructions or carry Tier 1 IR objects into the resulting program.
