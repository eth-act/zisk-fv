`arith_table_data.rs` is the 74-row lookup table that tells the Arith state
machine which flag combination is legal for each opcode; the extractor parses it
straight from ZisK's Rust source into `ArithTable.lean`. Changing the last field
of a row changes the flags admitted for that opcode.

**Missed, and `Extraction.ArithTable` is never even opened.** The only generated
file that changes is `ArithTable.lean`, and `lakefile.toml` does not list
`Extraction.ArithTable` in the `Extraction` library's `globs`, so Lean never
elaborates it — the build log shows `Extraction.LookupWiring`, `Extraction.Main`
and the two Mem modules rebuilt, and no `Extraction.ArithTable`. It could not
elaborate anyway: `tools/pil-extract/src/arith_table.rs:109` emits
`import ZiskFv.Fundamentals.Goldilocks`, a module that does not exist.

The model's own copy of the same table, `ZiskFv/AirsClean/ArithTable.lean:109`, is
74 rows of literal `#v[…]` whose docstring claims they are "Verbatim from
`build/extraction/Extraction/ArithTable.lean`". Nothing compiled checks that
claim, so ZisK's table and the modelled table can drift apart silently.
