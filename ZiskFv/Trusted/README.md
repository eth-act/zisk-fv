# `ZiskFv/Trusted/`

The **transpile-contract trust surface**. The single file
`Transpiler.lean` now exposes legacy `transpile_*` names mostly as
theorems indexed by one aggregate contract. The source trust ledger
contains one transpiler declaration:
`ZiskFv.Trusted.transpiler_contract_sound`.

Why a separate `Trusted/` subdirectory? The namespace
`ZiskFv.Trusted` reflects the trust-surface status: agents and
human readers can locate it instantly. The path-namespace match is
also load-bearing — the trust gate's
`check-locality.sh` enforces that all `axiom` / `opaque` /
`constant` / `unsafe def` / `partial def` / `@[extern]` /
`@[implemented_by]` declarations live in one of the files
allowlisted in `trust/allowed-axiom-files.txt`, and this file is on
that list.

The surrounding theorem docstrings and differential notes cite the
upstream Rust paths and the in-tree Lean static transpiler model.

To audit this class: read `Transpiler.lean`, the generated source
ledger in `trust/generated/baseline-axioms.txt`, and
`trust/trusted-base.md`.

See `trust/trusted-base.md` for the full per-class breakdown of
the current source axioms.
