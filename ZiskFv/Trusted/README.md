# `ZiskFv/Trusted/`

The **transpiler-contract trust surface**. The single file
`Transpiler.lean` declares the executable proposition family
`TranspilerContract : TranspilerContractKind -> Prop` plus the single
explicit bridge axiom `transpiler_contract_sound`. The old
`transpile_*` entry points remain as theorem wrappers so existing proof
call sites still spell the contract they consume.

Why a separate `Trusted/` subdirectory? The namespace
`ZiskFv.Trusted` reflects the trust-surface status: agents and
human readers can locate it instantly. The path-namespace match is
also load-bearing — the trust gate's
`check-locality.sh` enforces that all `axiom` / `opaque` /
`constant` / `unsafe def` / `partial def` / `@[extern]` /
`@[implemented_by]` declarations live in one of the files
allowlisted in `trust/allowed-axiom-files.txt`, and this file is on
that list.

The contract docstrings cite the upstream Rust functions in the `zisk/`
submodule that the corresponding cases mirror. The non-trusted static
Lean model lives in `ZiskFv/Transpiler/Static.lean`; the Rust-vs-Lean
differential harness lives in `tools/transpiler-diff/`.

To audit class #1: read `Transpiler.lean` top-to-bottom alongside
`docs/fv/transpiler/differential-pinning.md`, the static Lean model,
and the pinned Rust source. The trust ledger should contain
`ZiskFv.Trusted.transpiler_contract_sound`, not the retired
source-level `transpile_*` axiom family.

See `docs/fv/trusted-base.md` for the full per-class breakdown of
the current axiom ledger.
