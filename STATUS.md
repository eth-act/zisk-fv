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

Verification for latest slice: Lean LSP diagnostics are clean after an LSP
restart/build hook, and `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
passes. Full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` also pass.

Next step: lift adjacent/per-address cases toward the table-level
`MemoryBusRowsPrefixReadSound` proof.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
