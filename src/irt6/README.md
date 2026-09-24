# Tier 6: operation recovery

Tier 6 is the starting point for a peephole unoptimizer. Small rules establish
recognizable shapes, then operation recognizers replace those shapes when their
preconditions hold. Unrecognized code remains representable and executable in
the tier's IR.

## Representations

`ir.rs` defines the complete Tier 6 program, including its own functions, IDs,
types, structs, expressions, memory operations, and structured control flow.
`mod.rs` exhaustively translates Tier 5 into these owned definitions. No Tier 5
nodes or type aliases survive the boundary. Translation and recovery are separate:

```rust
let mut program = irt6::lift(&tier5);
let report = irt6::unoptimize::run(&mut program);
```

`run` enables assumption-based rewrites by default. Use `run_with_options` with
`Options { allow_assumptions: false }` to disable them, or pass
`--no-assumptions` to the command-line example.

`arithmetic.rs` is an auxiliary expression IR. `Context` reads local type
information; `Value` represents expressions with explicit integer widths and
canonical sums. The normalizer applies these small algebraic rules:

- Convert subtraction into a negative coefficient.
- Flatten addition and subtraction at the same width.
- Convert constant left shifts smaller than the width into scaling.
- Convert multiplication by a constant into scaling at the operand width.
- Combine equal terms, remove zero coefficients, and fold constants modulo
  `2^bits`.
- Normalize negated comparisons.

For example, `x - s`, `x + (0 - s)`, and `(x + a) - (s + a)` produce the same
sum when their operands have the same integer width. This provides algebraic
matching without enumerating expression trees for each operation recognizer.

Unknown widths, pointers, numeric conversions, memory reads, and operations
that can trap remain opaque where a rewrite is unsupported. The original Tier 6
expression is retained. Arithmetic normalization never crosses a load or invents
memory equivalence. Constants use the operation width when paired with a known
integer operand; casts and differing nonliteral widths are not erased.

`shapes/loops.rs` uses these values directly to compare a loop update with its expected
recurrence. The arithmetic dump prints the same `LoopAnalysis` and `Value` objects
used for recognition. It is an analysis view, not a parser or a second source of
truth. `stride_source` retains the matched source operand for reconstruction.

## Rules and proof constraints

`unoptimize/rules.rs` registers ordered rules. `unoptimize/facts.rs` tracks
branch facts and cached loads; `unoptimize/sequences.rs` drives local and
multi-instruction rewrites; `unoptimize/report.rs` formats the analysis. Each
successful rewrite restarts rule
selection at that node, then the driver descends into structured children. A
local limit of 16 rewrites and a total limit of 256 bound code growth. Hitting a
limit keeps valid IR and records the stop in the report. This initial driver is
a deterministic normalization pipeline; it does not yet search alternative
equivalent programs. Parents are revisited after child rewrites, and a second
pass follows temporary-assignment collapse so newly exposed shapes can match.

The first restructuring rule proves that a surrounding branch implies the first
check of a `do ... while`, then changes it to a `while`. A prefix of pure local
declarations may connect the branch's operands to the loop's operands. Temporary
bindings capture those values for the proof. Labels and nested control flow
prevent this initial rotation rule from firing.

The first operation rule recognizes `while (x u>= s) { x = x - s; }`. It requires
a known common integer width, an invariant stride, and exactly one update with
no other effects. The replacement is `x = x u% s`. Unsigned modulo is a binary
operator whose width comes from its operands and whose divisor must be nonzero.
It renders with multiplicative precedence.

The guarded-modulo rule removes `if (x u>= s) { x = x u% s; }` when the skipped
path already leaves the destination equal to `x`. It also handles the opposite
branch of `x u< s`. A variable destination can be its own dividend; a memory
destination can match a prior load from the same address. Known nonoverlapping
field writes preserve that load fact, while other memory writes invalidate it.
The false path has `x < s`, so `s` is nonzero and `x u% s` equals `x`.

The compound-assignment rule recognizes `a = a op b` for assignable binary
operators and renders the replacement as `a op= b`. It also recognizes
`a = b + a` and `a = b & a` for variable destinations. Memory destinations
match only the left operand and require a repeatable address expression.

The vector-iteration rule recognizes a zero-terminated traversal of a typed
vector. It removes a counter and repeated element load only when both locals
are confined to the matched loop, the counter increments by one, and the
body cannot change the vector or divert control flow. Tier 6 retains the
counter width and the offsets of the implicit advance and load. The rendered
`for v: T in vector[start..]` denotes iteration through successive elements
until the first zero element, with the original counter wrap behavior.

After operation recovery, Tier 6 propagates `CString` from recovered
zero-terminated byte iterations through direct copies and synthetic call
arguments. This evidence is unavailable to Tier 5, which retains `vec<i8>`.
Once promoted, a still-valid cached read of byte zero compared with zero can
be represented as `string.len() == 0`. The length expression scans memory for
the terminator and is treated as a memory read by later analyses.

After the type-aware rewrites, `relocate_variables.rs` moves a local into the
only branch that uses it when its declaration is immediately before the `if`.
Pure initializers can cross the condition. A read of byte zero can also cross
an equality check against the same CString's length: that check necessarily
reads byte zero on either outcome. Other memory reads and trapping expressions
stay in place. `eliminate_variables.rs` folds a single-use local into an
adjacent copy of the same type or a width-matched conversion, preserving the
initializer's evaluation point. It also recognizes a loop element copied to
a byte local solely for the next accumulator update. When the local has no
other uses after that update, the accumulator reads the element directly;
the local's initial value can then be folded into the adjacent conversion.

The boolean-return rule replaces an `if` whose two branches only return zero
and one with a return of the condition's boolean value or its negation. The
constants must have the same width. The condition is still evaluated once,
including any memory reads it performs.

The De Morgan rule pushes a negation through chained logical `||` and `&&`
expressions. Tier 6 represents logical `&&` separately from bitwise `&`, so
short-circuit evaluation and operand order remain intact. The rule also flips
comparisons when their exact complement is available, such as signed `>` to
signed `<=`.

The final branch pass combines adjacent `if` statements with identical pure
conditions when neither arm of the first branch writes a value read by that
condition. It appends the second branch's corresponding arm to the first,
retaining the order of effects while removing the redundant check.

Branch facts identify known zero strides. Writes invalidate dependent facts;
only invariant facts enter loop bodies. A known zero stride prevents recovery.
Otherwise, the rule assumes a nonzero stride on terminating executions: a zero
stride would make the matched loop infinite, so no fallback loop is generated.
With `allow_assumptions` disabled, only a proven nonzero stride can be rewritten.

`effects.rs` provides conservative variable, memory, control-flow, and trapping
effects shared by the rules. Different pointer expressions do not imply that
their memory is disjoint.

## Extending recovery

Add algebraic identities to `arithmetic.rs` with explicit width and effect
conditions. Add control restructuring rules to the rule registry; keep their
entry, control-flow, and scope proofs local. Add operation recognizers in the
corresponding `shapes/` module, returning the operands and unmet constraints.
For analyses that inspect nested IR, implement `shapes::visit::Analyzer` and
register the collector in `shapes/mod.rs`; the shared visitor walks instructions
and expressions once with source offsets and a function-local arithmetic
context. Reconstruction belongs in a rewrite rule and must preserve effects
and source metadata under its documented assumptions.
