# `ZiskFv/Compliance/`

The trust-ledger discharge layer for each of the 63 RV64IM opcodes,
plus the per-arm `OpEnvelope` glue that the global theorem in
`ZiskFv/Compliance.lean` (one level up) proves.

- **`Wrappers/<Op>.lean`** — 63 wrappers (one per opcode). Each
  imports the **core** `equiv_<OP>` theorem from
  `ZiskFv/EquivCore/<Op>.lean` (the `execute = bus_effect` form) and
  discharges its **promise hypotheses** using explicit route facts,
  row/provider evidence, the remaining non-row-shape trust ledger entries,
  and pure-Lean derivations, producing `ZiskFv.Compliance.equiv_<OP>` in
  the channel-balance form. `ZiskFv/Equivalence/<Op>.lean` is a thin
  re-export *above* this wrapper, not an input to it — the dependency
  runs `EquivCore → Wrappers → Equivalence`. The wrapper's parameter
  surface is the *minimal* caller-burden remaining after discharge; that
  surface is drift-guarded by
  `trust/generated/baseline-wrapper-caller-burden.txt`.

The global theorem `zisk_riscv_compliant_program_bus` lives in
`ZiskFv/Compliance.lean` (the file at the level above this folder).
`OpEnvelope` is an inductive with one arm per opcode, but its `exec_eq`
conclusion is *not* a case-returning dispatch: it is a conjunction of the
ten per-family `exec_eq_<family>` statements, of which exactly one fires
with a real channel-balance statement for any given arm while the rest
are `True`. The ten `Compliance/Dispatch/<family>.lean` files each prove
their family's conjunct.

`zisk_riscv_compliant_program_bus` is an **internal** per-arm
channel-balance lemma, not the advertised endpoint; the public soundness
endpoint is `ZiskFv.Compliance.root_soundness` in `ZiskFv/Soundness.lean`,
which consumes it.

To audit a single opcode's trust closure, read
`Compliance/Wrappers/<Op>.lean` together with the canonical
`Equivalence/<Op>.lean` it wraps; the diff between the two is
exactly the promise hypotheses discharged from the ledger.
