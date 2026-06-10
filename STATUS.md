Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone, and
the global load boundary now asks for `FullWitnessMemoryTimelineEvidence`
instead of bare `MemoryTimelineEvidence`.

Blocking: connect the local Mem-table theorem to concrete full-witness facts:
generated rows plus row/segment range facts.
`FullWitnessMemReplayBridge` packages them for a concrete Mem table, while
`FullWitnessMemoryTimelineEvidence` is the global source object and coerces to
the existing load-proof timeline API.
Current sub-gap: supply generated/range facts for the witness-selected Mem table;
table projection, row count, fixed-column shape, and nonempty evidence now have
constructors.
Audit result: existing Lean has selected-load MemClean row bridges, but no
source constructing whole-table `FullWitnessMemReplayBridge` fields from an
`EnsembleWitness`.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  load wrappers consume `MemoryTimelineEvidence`, and `OpEnvelope` now requires
  the full-witness source that derives it.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  selected-primary-read obligation.
- Completed slices `15775597`, `3773a889`, and `98202ebc` construct first/
  continuation accepted replay evidence and the segment selector/range facts.
- Latest local bridge slice adds `FullWitnessMemReplayBridge`, keeps the older
  generated-row bridge projectable, and constructs `AcceptedMemoryReplayEvidence`
  from the bundled full-witness facts.
- Timeline integration now has `memoryTimelineEvidence_of_fullWitnessMemReplayBridge`
  and `FullWitnessMemoryTimelineEvidence`; accepted replay is derived from the
  full-witness bridge, while split, initial agreement, and state-at-prefix remain
  residual timeline inputs.
- Current constructor slices add `memOfTable`,
  `fullWitnessMemReplayBridge_of_memTable`, fixed-`SEGMENT_L1` construction,
  and active-row nonempty -> table nonempty, so those are no longer external
  bridge facts.

Verification: recent segment-range/full-witness-bridge slices pass target
builds and no-`sorryAx` scans (only existing Clean completeness axioms).
Full `nix run .#test` last passed for `98202ebc`. Current slices pass LSP/file
checks, `lake build ZiskFv.Compliance`, both trust gates, and the targeted
Balance build; new constructor scans show no `sorryAx`.

Next step: derive the remaining generated/range facts for the witness-selected
Mem table.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
