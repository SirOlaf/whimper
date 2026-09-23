# Tier 2: register and memory semantics

Tier 2 lifts Tier 1 into its own IR with local value slots, explicit byte extraction and replacement for register aliases, and explicit memory loads and stores. Native register identities remain as parameter and slot metadata while register effects are translated into expressions and assignments.

Translate Tier 1 nodes into Tier 2 nodes. Do not inspect native instructions or carry Tier 1 IR objects into the resulting program.
