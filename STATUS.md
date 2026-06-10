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
- Latest committed slice lifts disjoint preservation to
  `replayMemoryAfterBusRow` and `replayMemoryAfterBusRows` prefixes when all
  prefix rows are byte-disjoint.
- Current uncommitted slice adds the `mem.pil:109` address-column range fact,
  the no-wrap theorem for `addr * 8`, and Balance projections that unequal Mem
  addresses give byte-disjoint replay entries.

Verification for current slice: Lean LSP diagnostics are clean for
`ZiskFv.Airs.Mem` and `ZiskFv.AirsClean.FullEnsemble.Balance`; target builds
for both modules pass, and both the LSP build hook and regular `lake build`
ran full successful Lake builds. Both trust gates and `nix run .#test` pass.

Next step: commit the address-range/disjointness slice, then use committed
replay-prefix preservation (`d27de7b5`) to prove the zero-preloaded
specialization of
`ActiveMemReplayRowsOfTablePrimaryReadPrefixSound`.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
