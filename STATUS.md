Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is
gone; load byte agreement now comes from `MemoryTimelineEvidence`, but
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge` and `MemTableGeneratedRangeFacts` expose
the row/list-position and range facts; `FullWitnessMemTableGeneratedRowsBridge`
is still the concrete full-ensemble bridge obligation.
Current sub-gap: use the new address-range/no-wrap facts to prove the
zero-preloaded specialization of the primary-read prefix obligation.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  and load wrappers consume `MemoryTimelineEvidence`.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  obligation `ActiveMemReplayRowsOfTablePrimaryReadPrefixSound`.
- Latest completed slice lifts the table-shaped zero-preload read lemma through
  `replayMemoryAfterBusRows` under an explicit prior-prefix byte-disjointness
  premise, reduces that premise to prior-prefix address separation, and proves
  the adjacent non-boundary address-change order fact from the Mem AIR. It also
  discharges split/list bookkeeping down to indexed all-prior address
  inequality.

Verification: Lean LSP diagnostics are clean for `ZiskFv.Airs.Mem` and
`ZiskFv.AirsClean.FullEnsemble.Balance`; target builds, full `lake build`,
both trust gates, and `nix run .#test` pass.

Next step: lift the adjacent address-order fact to all prior rows in the
concrete table prefix, including the segment-boundary continuation case.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
