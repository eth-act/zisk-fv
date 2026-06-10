Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone, and
load arms consume one global memory-timeline boundary.

Blocking: add generated/full-ensemble support for
`FullWitnessMemAirSourceRawFacts`. Existing `componentWithDualMemBus` emits
only the nine row constraints plus MemBus provider rows, not the stage-2
permutation/range/assertion source facts.

Latest audit: this is structural, not a missing lemma. The Mem table row input
contains only `MemRow`; stage-2 `gsum`/`im`, table-global segment/permutation
constants, challenges, ranges, and generated assertions are outside the
component, and per-row locals would not make table-global constants generic.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed-column facts, active-row equality, and
  nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` is the Compliance-facing load boundary.
  It now carries the concrete full witness and `FullWitnessMemAirSourceRawFacts`;
  `memSource`, `replayBridge`, and `acceptedReplay` are derived accessors, not
  fields.
- `tools/pil-extract mem-air-facts` reports generated constraint groups,
  range-check hints, witness/fixed columns, `mem.pil` range/bit lines, and Lean
  range-fact coverage.
- `MemTableGeneratedAirSource` and `memTableGeneratedAirSource_of_witnessFacts`
  remain the table-level typed source path from Clean assertion/lookup witnesses.
- `FullWitnessMemAirSourceFacts` names the remaining generated/full-ensemble
  callback: choose source columns and concrete assertion/range lookup witnesses
  for any witness Mem table; table membership and component identity come from
  the full witness.
- `FullWitnessMemAirSourceRawFacts` is the generated-module target when raw
  split constraints and range propositions are proved directly; Lean packages
  it into `FullWitnessMemAirSourceFacts` and can select a concrete
  `FullWitnessMemAirSource` from it.

Latest verification:
- Lean LSP diagnostics on `Balance`: clean
- `lean_verify` on raw-fact timeline accessors/constructor: no `sorryAx`
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `lake build ZiskFv.Compliance`
- `trust/scripts/check-all.sh`

Last full `nix run .#test`: commit `98202ebc`.

Next step: choose/implement the raw-facts route: either a checked concrete
generated-witness artifact, or a broader table/component model extension that
represents the missing Mem AIR source columns generically.
Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
