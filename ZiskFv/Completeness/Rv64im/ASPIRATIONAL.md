# Aspirational completeness route (quarantined)

This directory's `Defs.lean`, the `*Families.lean` / `*Edges.lean` files,
`GlobalTargets.lean`, and the `Stage`/`Pipeline`/`Interface` machinery in
`../Rv.lean` form an **abstract, `Rv.Interface`-parametrized** formulation of
RV64IM completeness. It is **quarantined**: no concrete `Interface` is ever
instantiated, and the live completeness endpoints do **not** depend on it.

## Live surface (what actually carries the claim)

`ZiskFv/Completeness.lean`:

- `root_completeness_sail` — **proven, unconditional.** Sail-executable RV64IM
  raw words land in `SupportedDecodeShape` (re-exports the `SailDecode`
  containment proof, which computes against the real generated Sail decoder).
- `eventual_zisk_coverage` — **conditional** on the ZisK coverage obligations
  over `SupportedDecodeShape`.
- `eventual_root_completeness` — the composition; conditional on the ZisK
  obligations only (the Sail half is discharged).

Their dependency cone is `SailDecode/*` + `Shapes.lean` + `RawInstruction`
(from `Rv.lean`). Nothing here.

## Why it's kept

It is the intended *eventual* composition machinery. When the Aeneas-extracted
ZisK coverage proofs can be imported into the main build (today they live in a
separate Lean workspace this build cannot import — see
`scripts/aeneas-production-extract.sh` under `AENEAS_CHECK_RV_COMPLETENESS`), the
plan is: instantiate a concrete `Interface` with those harness predicates,
discharge the per-stage obligations, and assemble the global theorem via the
per-family composition lemmas here — then `eventual_root_completeness` becomes
unconditional.

It is imported only by `ZiskFv.lean`, so it stays compiled and type-checked for
preservation — not because any live claim uses it.

## Status / next steps

- If the Aeneas import bridge never lands, this route is **deletable** with no
  loss to any proven claim (the hard content — the Sail proof — lives in
  `SailDecode/`, and these files are regenerable composition glue). Recover via
  `git show` if removed.
- The composition/monotonicity/disjunction lemmas (`Rv.lean`) are the only part
  with real reuse value; the per-family files are the most speculative.
