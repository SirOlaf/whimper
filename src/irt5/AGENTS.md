# Tier 5: inferred types

Tier 5 owns an IR with program-local struct definitions and variable types for integers, pointers, structs, Boolean values, and unresolved values. Its lift translates Tier 4, assigns dense variable IDs, and infers types from the available IR evidence.

Infer only what the IR supports; retain unknown types when evidence is insufficient. Do not consult native instructions or embed Tier 4 nodes in Tier 5.
