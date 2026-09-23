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
By default, `cargo run` decompiles the existing example function at
`0x140095be0` in the sample image. Use `--address 0x...` to select a different
virtual address, and `--length 0x...` if the function is not followed by `INT3`
padding. `--entry` selects the PE entry point.

The IR lifter still supports only a small subset of x86_64 instructions, so
selecting arbitrary functions may fail. External jumps are not yet resolved as
tail calls; the full image is now available for that analysis.
