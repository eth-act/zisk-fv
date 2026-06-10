Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is gone;
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: connect the local Mem-table theorem to concrete full-witness facts.
`MemTableGeneratedRowsBridge`, `MemTableGeneratedRangeFacts`,
`MemSegmentGeneratedRangeFacts`, `MemTableGeneratedFixedColumnFacts`, and
nonempty table evidence expose the local inputs; `FullWitnessMemReplayBridge`
now packages them for a concrete full-witness Mem table.
Current sub-gap: add or choose the extractor/global-boundary source for that
full-witness replay bridge, then route it through the memory-evidence boundary.
Audit result: existing Lean has selected-load MemClean row bridges, but no
source constructing whole-table `FullWitnessMemReplayBridge` fields from an
`EnsembleWitness`.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  and load wrappers consume `MemoryTimelineEvidence`.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  selected-primary-read obligation.
- Completed slices `15775597`, `3773a889`, and `98202ebc` construct first-
  segment and continuation accepted replay evidence from concrete Mem-table
  facts, with continuation replay seeded by `previous_segment_*`.
- Latest completed slice proves the previous-segment address range from
  `mem.pil:265/267/268` distance-base chunks plus row-0 Mem facts, adds
  `MemSegmentGeneratedRangeFacts`, and adds a first/continuation selector
  constructor for `AcceptedMemoryReplayEvidence`.
- Latest local bridge slice adds `FullWitnessMemReplayBridge`, keeps the older
  generated-row bridge projectable, and constructs `AcceptedMemoryReplayEvidence`
  from the bundled full-witness facts.
- Timeline integration now has `memoryTimelineEvidence_of_fullWitnessMemReplayBridge`,
  deriving the accepted replay subobject while leaving only the residual split,
  initial agreement, and state-at-prefix facts as timeline inputs.

Verification: `lake build ZiskFv.Airs.Mem` and
`lake build ZiskFv.AirsClean.FullEnsemble.Balance` pass for the recent
segment-range/full-witness-bridge slices. New accepted-replay declarations have
no `sorryAx` (only existing Clean component completeness axioms).
`trust/scripts/check-all.sh` passes for the timeline-constructor slice. Full
`nix run .#test` last passed for `98202ebc`.

Next step: decide whether to extend the extractor/global boundary to produce
`FullWitnessMemReplayBridge`, then wire that source through the memory-evidence
boundary.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
