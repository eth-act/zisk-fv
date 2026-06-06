# `ZiskFv/Compliance/`

The trust-ledger discharge layer for each of the 63 RV64IM opcodes,
plus the per-arm `OpEnvelope` dispatch glue that the global theorem
in `ZiskFv/Compliance.lean` (one level up) case-splits on.

- **`Wrappers/<Op>.lean`** — 63 wrappers (one per opcode). Each
  takes the canonical `equiv_<OP>` theorem (in `ZiskFv/Equivalence/`)
  and discharges its **promise hypotheses** using explicit route facts,
  row/provider evidence, the remaining non-row-shape trust ledger entries,
  and pure-Lean derivations. The wrapper's parameter surface is the
  *minimal* caller-burden remaining after discharge; that surface
  is drift-guarded by `trust/generated/baseline-wrapper-caller-burden.txt`.

The uber theorem `zisk_riscv_compliant_program_bus` lives in
`ZiskFv/Compliance.lean` (the file at the level above this folder)
and uses an `OpEnvelope` sum type (63 arms, one per RV64IM opcode)
to dispatch each opcode to its `Wrappers/<Op>` wrapper. Its
`OpEnvelope.completenessBurden` and
`OpEnvelope.AcceptedFullExecutionMemoryTraceSourceAtEnvelope` make
explicit that the current theorem starts from supplied witness evidence and,
for load envelopes only, a shared accepted memory trace plus selected envelope
Mem-row occurrence and split-indexed prefix-state equality in the
witness-selected table rather than deriving all of that evidence from a full
execution trace. Cursor-shaped replay evidence can be promoted to that source
shape only with an explicit selected-occurrence uniqueness proof.
Non-load envelopes carry no memory trace data. The load-scoped memory
construction object, lower trace/table bridge, packed
`OpEnvelope.AcceptedAirMainMemTraceEvidenceAtEnvelope`, ordinary selected-row
membership, selected prefix cursor, generated Mem burden, packed
`OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`, lower
`OpEnvelope.AcceptedFullMemoryBusRowsTraceAtEnvelope`, projected
`OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope`, and projected
`TraceReplaySound` replay objects are derived internally.

To audit a single opcode's trust closure, read
`Compliance/Wrappers/<Op>.lean` together with the canonical
`Equivalence/<Op>.lean` it wraps; the diff between the two is
exactly the promise hypotheses discharged from the ledger.
