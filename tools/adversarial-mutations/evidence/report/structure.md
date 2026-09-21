
---

## Where the generated constraints actually enter the Lean build

This is measured from the tree, and it explains every verdict above.

`lakefile.toml` compiles fourteen of the eighteen generated modules. **Four are
generated and never compiled at all**: `Buses.lean`, `MemoryBuses.lean`,
`BinaryExtension.lean` is compiled but unread, and `ArithTable.lean` /
`MemAirFacts.md` sit outside the `globs` list. Nothing downstream can react to a
change in an artifact Lean never elaborates.

Thirteen `import Extraction.*` lines exist in the whole `ZiskFv` tree, in ten
modules. Seven of those ten — the six `*MirrorWeld.lean` files and
`Binary/Wiring.lean` — are imported **only** by the root aggregator `ZiskFv.lean`.
Three are load-bearing: `Mem/RangeWiring.lean`, `MemAlign/Bridge.lean` and
`MemAlignRomTable.lean`.

The import closure of `ZiskFv.Soundness` (where `root_soundness` lives) is 637
modules and reaches exactly two generated modules: `Extraction.LookupWiring` and
`Extraction.MemAlignRom`.

Two consequences, both visible in the rounds:

1. **`lake build` is the gate, not the theorem.** A mutation to a `Main`, `Binary`,
   `Arith`, `Mem` or `MemAlign` polynomial identity is caught by a `*MirrorWeld`
   module, so the repository build goes red — which is what CI checks. But those
   welds are outside `root_soundness`'s dependency graph, so the theorem itself is
   not stated *modulo* the extraction. Deleting a weld would not change what
   `root_soundness` proves; it would only stop anyone noticing that the model had
   drifted from ZisK.
2. **Coverage is per-constraint, and the repository says so.** `BinaryMirrorWeld`
   states plainly that the Binary family emits 31 constraints and welds 11 of them;
   the other 20 are the challenge-mixing (`gsum`/logUp) constraints that carry the
   bus tuples. A mutation inside one of those 20 lands in a file the build
   elaborates but no theorem constrains.

### Two things the rounds turned up that are not about any single constraint

**`Extraction.ArithTable` cannot elaborate, and nothing notices.**
`tools/pil-extract/src/arith_table.rs:109` writes `import ZiskFv.Fundamentals.Goldilocks`
into the generated module. No such module exists — the file has been
`ZiskFv/Field/Goldilocks.lean` since the directory restructure in `84828e96`, and
`Extraction/MemAlignRom.lean` (the other generated module that needs it) imports the
correct path. `Extraction.ArithTable` is absent from `lakefile.toml`'s `globs`, so
Lean never opens it and the stale import has never surfaced. Meanwhile the model's
own copy of the same data, `ZiskFv/AirsClean/ArithTable.lean:109`, is 74 rows of
literal `#v[…]` whose docstring says "Verbatim from
`build/extraction/Extraction/ArithTable.lean`" — a claim no compiled declaration
checks, because that module is not imported anywhere either.

**`pil-extract mem-align-rom` re-implements ZisK's ROM builder rather than
extracting it.** For the virtual `MemAlignRom` AIR the extractor reads only the
`OFFSET`/`WIDTH` fixed columns, three integer constants, and a regex check on the
`lookup_proves` tuple shape; the `pc`, `delta_pc`, `delta_addr` and `flags` of all
256 rows are then computed by `build_rows` in Rust
(`tools/pil-extract/src/mem_align_rom.rs`). A defect in ZisK's own row builder
therefore cannot reach Lean — round 50 changes the access-window test in that
builder and `MemAlignRom.lean` comes out byte-identical.

### The welds are definitional, not semantic

Rounds 6 and 21 were meant as controls: each rewrites one term of an Arith identity
into a commutative image of itself (`fab*a[1]*b[3]` → `fab*b[3]*a[1]`,
`eq[i] + carry[i-1]` → `carry[i-1] + eq[i]`). The project's own polynomial normal
form says nothing changed. **Both fail the build anyway**, at
`ArithMirrorWeld.lean:372` and `:330`.

That is the welds working as designed: they are `Iff.rfl` / structure-instance
equalities against the generated term, so they pin the *syntactic form* of each
constraint, which is strictly stronger than pinning the polynomial. The practical
consequence is that a benign refactor of ZisK's PIL — reordering a product, or
re-associating a sum — turns the repository red and needs the mirrors updated by
hand. That is a maintenance cost, not a soundness gap, and it is the price of
having the mirrors checked by the kernel rather than by a comment.
