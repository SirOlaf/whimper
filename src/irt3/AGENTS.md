# Tier 3: structured control flow

Tier 3 owns the IR used to recover loops and simplify synthetic functions. Its lift copies Tier 2 into Tier 3 types, then inlines trivial loops, variables, and functions and handles return slots. Structured branches and loops coexist with transfers that have not yet been recovered.

Work from Tier 2 IR and preserve source offsets and control-flow meaning. Native instructions must never appear in Tier 3.
