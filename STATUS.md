Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone, and
load arms consume one global memory-timeline boundary.

Blocking: make generated/full-ensemble output provide
`FullWitnessMemAirSourceRawFacts` for the witness-selected Mem table.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed-column facts, active-row equality, and
  nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` is the Compliance-facing load boundary.
  It now carries the concrete full witness and `FullWitnessMemAirSource`;
  `replayBridge` and `acceptedReplay` are derived accessors, not fields.
- Public load boundaries no longer mention `fullRv64imEnsemble` or the legacy
  `mem.addr r_mem = bus.e1.ptr` pin.
- `tools/pil-extract mem-air-facts` reports generated constraint groups,
  range-check hints, witness/fixed columns, `mem.pil` range/bit lines, and
  Lean range-fact coverage for every current Mem range fact field.
- `MemTableGeneratedAirSource` is the typed Lean target; replay/timeline
  constructors consume it, and `memTableGeneratedAirSource_of_witnessFacts`
  builds it from concrete Clean assertion and lookup witnesses.
- `MemTableGeneratedConstraintFacts` and
  `MemTableGeneratedConstraintAssertionFacts` split generated constraints into
  `segment_every_row` (`0..=23`) and `permutation_every_row` (`24..=33`), with
  Clean assertion witnesses projecting to those raw facts.
- `MemTableGeneratedRangeLookupFacts` and
  `MemSegmentGeneratedRangeLookupFacts` turn concrete Clean lookup witnesses
  into the raw row/segment range facts.
- `FullWitnessMemAirSourceFacts` names the remaining generated/full-ensemble
  callback: choose source columns and concrete assertion/range lookup witnesses
  for any witness Mem table; table membership and component identity come from
  the full witness.
- `FullWitnessMemAirSourceRawFacts` is the generated-module target when raw
  split constraints and range propositions are proved directly; Lean packages
  it into `FullWitnessMemAirSourceFacts` and can select a concrete
  `FullWitnessMemAirSource` from it.
- `fullWitnessMemoryTimelineEvidence_of_rawFacts` builds the full-witness
  memory timeline boundary from raw Mem source facts plus only the residual
  Sail timeline fields.

Latest verification:
- Lean LSP diagnostics on `Balance`: clean
- `lean_verify` on raw Mem source/timeline constructors: no `sorryAx`
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `trust/scripts/check-all.sh`

Last full `nix run .#test`: commit `98202ebc`.

Next step: make generated/full-ensemble output provide
`FullWitnessMemAirSourceRawFacts` for the witness Mem table.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
