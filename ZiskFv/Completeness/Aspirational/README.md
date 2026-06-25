# Aspirational completeness route (quarantined)

Everything in this directory — `Interface.lean` (the `Stage`/`Pipeline`/`Interface`
abstraction + its composition lemmas), `Defs.lean`, the `*Families.lean` /
`*Edges.lean` files, and `GlobalTargets.lean` — forms an **abstract,
`Rv.Interface`-parametrized** formulation of RV64IM completeness. It is
**quarantined**: no concrete `Interface` is ever instantiated, and the live
completeness endpoints do **not** depend on any of it. The whole route is reached
only through `ZiskFv.lean` (so it stays built and verified) via the
`ZiskFv.Completeness.Aspirational` aggregator.

## Live surface (what actually carries the claim)

`ZiskFv/Completeness.lean`:

- `sail_executable_within_supported_decode_shape` — **proven, unconditional.** Sail-executable RV64IM
  raw words land in `SupportedDecodeShape` (re-exports the `SailDecode`
  containment proof, which computes against the real generated Sail decoder).
- `skeletal_root_completeness` — **conditional** on the ZisK coverage obligations; the
  end-to-end acceptance statement, with the Sail half discharged inline.

Their dependency cone is `Rv64im/SailDecode/*` + `Rv64im/Shapes.lean` +
`RawInstruction` (the live remnant of `Rv.lean`). Nothing in this directory.

## Why it's kept

It is the intended *eventual* composition machinery. When the Aeneas-extracted
ZisK coverage proofs can be imported into the main build (today they live in a
separate Lean workspace this build cannot import — see
`scripts/aeneas-production-extract.sh` under `AENEAS_CHECK_RV_COMPLETENESS`), the
plan is: instantiate a concrete `Interface` with those harness predicates,
discharge the per-stage obligations, and assemble the global theorem via the
per-family composition lemmas here — then `skeletal_root_completeness` becomes
unconditional.

It is imported only by `ZiskFv.lean`, so it stays compiled and type-checked for
preservation — not because any live claim uses it.

## Status / next steps

- If the Aeneas import bridge never lands, this whole directory is **deletable**
  with no loss to any proven claim (the hard content — the Sail proof — lives in
  `../Rv64im/SailDecode/`, and these files are regenerable composition glue).
  Recover via `git show` if removed.
- The composition/monotonicity/disjunction lemmas (`Interface.lean`) are the only
  part with real reuse value; the per-family files are the most speculative.
