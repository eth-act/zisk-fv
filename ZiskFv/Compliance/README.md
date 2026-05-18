# `ZiskFv/Compliance/`

The trust-ledger discharge layer for each of the 63 RV64IM opcodes,
plus the per-arm `OpEnvelope` dispatch glue that the global theorem
in `ZiskFv/Compliance.lean` (one level up) case-splits on.

- **`Wrappers/<Op>.lean`** — 63 wrappers (one per opcode). Each
  takes the canonical `equiv_<OP>` theorem (in `ZiskFv/Equivalence/`)
  and discharges its **promise hypotheses** by appealing to the
  trust ledger (`ZiskFv/Trusted/Transpiler.lean` for `transpile_*`
  contracts, the axiom-bearing files under `ZiskFv/Airs/` for
  range / bus / lookup-table soundness, and pure-Lean derivations
  for everything else). The wrapper's parameter surface is the
  *minimal* caller-burden remaining after discharge; that surface
  is drift-guarded by `trust/baseline-wrapper-caller-burden.txt`.

The uber theorem `zisk_riscv_compliant_program_bus` lives in
`ZiskFv/Compliance.lean` (the file at the level above this folder)
and uses an `OpEnvelope` sum type (35 arms, indexed by
`mainOpKind`) to dispatch each opcode to its `Wrappers/<Op>` wrapper.

To audit a single opcode's trust closure, read
`Compliance/Wrappers/<Op>.lean` together with the canonical
`Equivalence/<Op>.lean` it wraps; the diff between the two is
exactly the promise hypotheses discharged from the ledger.
