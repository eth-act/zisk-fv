**Not a test, and it exposes a coverage boundary.** The mutation is inside the ROM
row generator (`sel[j] = 1` for `j` in the access window), yet `MemAlignRom.lean`
is byte-identical.

The reason is in `tools/pil-extract/src/mem_align_rom.rs`: for this virtual AIR the
extractor reads only four things out of `mem_align_rom.pil` — the `OFFSET` and
`WIDTH` fixed columns, the `spsize` / `one_word_combinations` /
`two_word_combinations` constants, and a regex check that the `lookup_proves`
tuple still has its six-column shape — and then **re-implements the row builder in
Rust** (`build_rows`). The `pc`, `delta_pc`, `delta_addr` and `flags` of every ROM
row are therefore computed by the extractor, not read from ZisK. A divergence in
ZisK's own row builder cannot reach Lean, because Lean is being shown the
extractor's version of that builder.
