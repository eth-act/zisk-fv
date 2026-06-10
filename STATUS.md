Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is
gone; load byte agreement now comes from `MemoryTimelineEvidence`, but
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge` and `MemTableGeneratedRangeFacts` expose
the row/list-position and range facts; `FullWitnessMemTableGeneratedRowsBridge`
is still the concrete full-ensemble bridge obligation.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  and load wrappers consume `MemoryTimelineEvidence`.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  obligation `ActiveMemReplayRowsOfTablePrimaryReadPrefixSound`.
- Latest slice adds `MemoryBusEntryByteDisjoint` and
  `readEventReplayAgreement_of_writeMemoryOfEntry_disjoint`, proving that a
  write to a disjoint eight-byte range preserves an existing read agreement.

Verification for latest slice: Lean LSP diagnostics are clean for
`ZiskFv.ZiskCircuit.MemTrace`; both target module builds, full `lake build`,
both trust gates, and `nix run .#test` pass.

Next step: commit the disjoint-write preservation slice, then use it to
discharge `ActiveMemReplayRowsOfTablePrimaryReadPrefixSound`.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
