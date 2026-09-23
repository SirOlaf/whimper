# Tier 4: source-like control flow

Tier 4 owns an IR with conditional `while` loops, declarations, and simplified expressions. Its lift translates Tier 3 nodes, then eliminates aliases, moves loop conditions into loop headers, simplifies branches and binary operations, and places declarations.

Keep these transformations on Tier 4 IR. Native instructions and previous-tier nodes must not survive the lift.
