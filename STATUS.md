Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is
gone; load byte agreement now comes from `MemoryTimelineEvidence`, but
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: finish proving prefix-read soundness from concrete Mem table facts.
`MemTableGeneratedRowsBridge` names the table/list-position bridge, and
`FullWitnessMemTableGeneratedRowsBridge` is still the concrete full-ensemble
obligation to prove. `MemTableGeneratedRangeFacts` names the extracted range
facts needed for Nat timestamp order.

Latest proof surface:
- Local active-row chronology is proved from `MemTableGeneratedRowsBridge` and
  `MemTableGeneratedRangeFacts`.
- Adjacent same-address predecessor timestamp order is proved via
  `previous_primary_step_le_step_of_memTableGeneratedRowsBridge` and
  `previous_dual_step_le_step_of_memTableGeneratedRowsBridge`.
- Same-address read value carry is now projected to concrete bridged table rows,
  and the adjacent previous-primary-write -> current-read replay agreement step
  is factored through `readEventReplayAgreement_of_writeMemoryOfEntry_same`.
- Same-row primary-write -> dual-read replay agreement is now factored as
  `readEventReplayAgreement_after_primary_write_dual_read_of_row`.
- Read rows are now factored as replay-preserving via
  `replayMemoryAfterBusRow_eq_self_of_read`, with equal pointer/value read
  agreement transport in `readEventReplayAgreement_of_entry_same`.
- Adjacent previous-primary-read -> current-read and same-row primary-read ->
  dual-read replay agreement project those generic facts to bridged Mem rows.
- Replay list append is factored in `MemTrace` via
  `replayMemoryAfterBusRows_append`,
  `memoryBusRowsReadWriteSound_append`, and
  `memoryBusRowsPrefixReadSound_append`.
- One generated row's active replay chunk is packaged as recursive read/write
  sound by `memoryBusRowsReadWriteSound_activeMemReplayEntriesOfRow_of_spec`,
  assuming only the incoming soundness of any selected primary read.
- Address-change/first-read zero initialization is now factored through
  `zeroedMemoryEntryOfEntry`, `zeroMemoryOfEntry`, `zeroMemoryOfRows`, and
  `readEventReplayAgreement_of_zeroMemoryOfEntry`, with Balance projections
  for generated address-change primary reads.
- Row-local active replay soundness now composes over a table `flatMap` via
  `memoryBusRowsReadWriteSound_flatMap_activeMemReplayEntriesOfRow` and
  `memoryBusRowsReadWriteSound_activeMemReplayRowsOfTable_of_primary_reads`.

Verification for latest slice: Lean LSP diagnostics are clean for
`ZiskFv.AirsClean.FullEnsemble.Balance`, and `lake build
ZiskFv.AirsClean.FullEnsemble.Balance` plus full `lake build` pass.
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass.

Next step: commit the table-level fold slice, then use the bridge/range facts
to discharge the selected-primary-read prefix hypothesis.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
