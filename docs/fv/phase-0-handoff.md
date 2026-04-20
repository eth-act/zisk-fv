# Phase 0 handoff

## What shipped

- **`tools/zisk-pil-extract/`**: standalone Rust CLI; decodes a pilout
  protobuf, walks one named AIR, emits Lean 4 source matching the openvm-fv
  `Extraction/*.lean` shape. Supports `Constant`, `WitnessCol`, recursive
  `Expression`; skips unsupported operand kinds with a commented stub. CLI
  also has `--list` for discovering AIR names.
- **`ZiskFv/`**: Lake 4 package, toolchain `v4.26.0`, deps `mathlib` and
  `LeanZKCircuit` (both at `v4.26.0`). Contains:
  - `ZiskFv/Fundamentals/Goldilocks.lean` — `FGL = Fin (2^64 - 2^32 + 1)`
    with `Field` instance, `Fact (Nat.Prime GL_prime)` proved by
    `native_decide` (~6 min; acceptable but worth caching).
  - `ZiskFv/Extraction/BinaryAdd.lean` — generated from
    `pil/zisk.pilout`, AIR `BinaryAdd`. 4 of 9 constraints fully extracted
    (the ones using only constants / witness cols); 5 skipped pending
    operand-kind coverage.
  - `ZiskFv/Extraction/BinaryAdd.hand.lean` — byte-identical oracle used
    by the diff gate.
  - `ZiskFv/Spike.lean` — `cout_0_boolean`: from the extracted `constraint_0`
    (`cout[0] * (1 - cout[0]) = 0`), conclude `cout[0] ∈ {0, 1}` over
    Goldilocks. Proved with `unfold; grind`.
- **`justfile`** at repo root, target `verify-phase0`: regenerates the
  extraction, diffs vs. the oracle, runs `lake build`. Currently exits 0.
- **`docs/fv/extractor-notes.md`**: contract, pilout structure facts,
  operand-kind coverage.

## What was learned (relevant to the metaplan)

- **Pilout constants are big-endian variable-length bytes.** The `.proto`
  comment does not specify byte order; initial LE decode produced silent
  wrong-value output. Phase 1 should surface this in any additional
  protobuf-consuming code (e.g. `PeriodicCol`, `FixedCol` payload bytes use
  the same encoding).
- **`LeanZKCircuit.OpenVM.Circuit` is field-polymorphic and works unchanged
  over Goldilocks.** No shim was needed. The planned 2-hour time box for the
  shim decision is freed for Phase 1.
- **`BinaryAdd` uses 4 operand kinds beyond constants/witness cols:**
  `Challenge`, `AirValue`, `FixedCol`, (and transitively `Expression`).
  Phase 1 will need all four to extract the Main AIR.
- **`native_decide` on Goldilocks primality is ~386s.** Cheap enough for CI
  that caches `.olean`s; painful on cold rebuilds. Consider proving primality
  via a faster decision procedure (Lucas/Miller-Rabin encoded in Lean) or
  vendoring an `.olean`.
- **`lake exe cache get` works against Mathlib's Azure cache** — the 7700+
  mathlib `.olean`s fetch in seconds, not the hours they'd take to compile.
- **`cout[0]` is stage-1 col 8 in the compiled pilout.** This is visible in
  the `-- witness column names:` header that the extractor emits from the
  symbol table. Future proofs should reference columns by name via that
  table rather than by raw index.

## Metaplan recalibrations for Phase 1

- **Operand-kind coverage is the critical path**, not Plonky3 vs pilout
  translation. The top priorities for the extractor are, in order:
  `FixedCol`, `Challenge`, `AirValue`, `PeriodicCol`. With those four,
  every `BinaryAdd` constraint and almost every Main-AIR constraint
  extracts.
- **Constraint-kind fidelity** (`everyRow` vs `firstRow`/`lastRow`/
  `everyFrame`) is currently flattened into a single `constraint_N` shape.
  Phase 1 needs to emit separate predicates (e.g.
  `constraint_N_first_row`) so that the bridging proofs can quantify over
  the right domain.
- **Operation-bus bridging** — no surprises here. The bus schema is in
  `operations.pil` and `OPERATION_BUS_ID=5000`; `BinaryAdd` drives the ADD
  row via `proves_operation(op: OP_ADD, a:, b:, c:)`.

## Repro

```bash
just verify-phase0
```

Expected: exit 0 after ~3s cargo + ~1s diff + a few seconds of incremental
lake build. First-time build is ~10 min dominated by Goldilocks primality.
