# `ZiskFv/Trusted/`

The **transpile-contract trust surface**. The single file
`Transpiler.lean` declares the **51 `transpile_*` axioms** that
constitute class #1 of the trust ledger (the largest single block
in the 122-axiom TCB). Each axiom asserts that ZisK's Rust
transpilation lowers a Sail-decoded RV64IM instruction
(`ast` value) into a Main-AIR row column shape that matches the
pure spec.

Why a separate `Trusted/` subdirectory? The namespace
`ZiskFv.Trusted` reflects the trust-surface status: agents and
human readers can locate it instantly. The path-namespace match is
also load-bearing — the trust gate's
`check-locality.sh` enforces that all `axiom` / `opaque` /
`constant` / `unsafe def` / `partial def` / `@[extern]` /
`@[implemented_by]` declarations live in one of the files
allowlisted in `trust/allowed-axiom-files.txt`, and this file is on
that list.

Each axiom's docstring cites the exact upstream Rust function in the
`zisk/` submodule that the contract mirrors (e.g.
`transpile_ADD` cites `zisk/.../transpile.rs::transpile_R::ADD`).
The submodule is pinned at `0xPolygonHermez/zisk@48cf7ccef`.

To audit class #1: read `Transpiler.lean` top-to-bottom alongside
the `zisk/` source it cites. The same axioms also surface as the
`transpile_*` references in `trust/baseline-axioms.txt` (51 lines).

See `docs/fv/trusted-base.md` for the full per-class breakdown of
the 122 axioms.
