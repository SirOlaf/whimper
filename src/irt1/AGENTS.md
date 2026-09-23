# Tier 1: control-flow partitions and conditions

Tier 1 lifts the linear Tier 0 program into its own IR of synthetic functions. Local jumps and fallthrough become transfers between shared partitions; flag-dependent conditions become Boolean expressions, and incoming register values become parameters. Register identities can still occur as IR data.

Consume only Tier 0 IR. Keep native instruction decoding and matching in Tier 0, and ensure each Tier 1 program is represented entirely by Tier 1 types.
