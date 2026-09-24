# Tier 6: operation recovery

Tier 6 owns a complete IR translated from Tier 5. `unoptimize/` applies local rewrites to recover higher-level operations; `arithmetic.rs`, `effects.rs`, and `shapes/` provide the matching and proof information. See `README.md` here for the current rules and constraints.

Recognize operations from Tier 6 IR, not native instructions. Preserve effects, types, and source metadata; leave unmatched code representable in this tier.
