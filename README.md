# The Whimper decompiler

Currently WIP and unusable. Eventually it may translate x86_64 machine code into typescript, for use by the [VN Web Engine](https://github.com/SirOlaf/vn-web-engine)

## Loading a PE image

Place an x86_64 PE32+ executable in `samplebinary/`. The program selects the first
PE file there by filename, loads its headers and every section at its preferred
virtual address, and zero-fills section memory beyond the raw file data. The
loaded image exposes both executable bytes and mapped data by virtual address.
The sample binary remains ignored by Git.

`cargo run -- --list-sections` prints the mapped section ranges and entry point.
`cargo run -- --read 0x1401c8000 16` reads 16 mapped bytes at a virtual address
and prints them as hex, including zero-filled data where applicable.
By default, `cargo run` decompiles the byte-string hash function at
`0x14008d690` in the sample image. Use `--address 0x...` to select a different
virtual address, and `--length 0x...` if the function is not followed by `INT3`
padding. `--entry` selects the PE entry point.
Use `--tier 1` through `--tier 6` to inspect a tier directly; add
`--address-comments` to retain source addresses in the rendered view.

Tier 5 recovers unknown-length arrays from dynamic memory accesses with a clear
base, consistent element widths and types, and compatible index scaling. The
default function's byte accesses infer `arg1: vec<i8>` and render as
`arg1[0x0]`, `arg1[0x1]`, and `arg1[u64(v2)]`. Here `vec<T>` describes an address
of elements; it does not imply ownership, a known length, or bounds checks.
Conflicting accesses, ambiguous bases, and unsupported address calculations
retain their pointer representation. Tier 6 translates the recovered element
addresses into its own IR, preserving access widths and integer conversions.

The IR lifter still supports only a small subset of x86_64 instructions, so
selecting arbitrary functions may fail. External jumps are not yet resolved as
tail calls; the full image is now available for that analysis.
