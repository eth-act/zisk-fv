Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone, and
load arms consume one global memory-timeline boundary.

Blocking: construct `MemTableGeneratedAirSource.facts` for the witness-selected
Mem table from generated extractor output or concrete Clean/pilout proofs.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed-column facts, active-row equality, and
  nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` is the Compliance-facing load boundary;
  it derives accepted replay from `FullWitnessMemReplayBridge` and carries only
  the residual timeline facts.
- Public load boundaries no longer mention `fullRv64imEnsemble` or the legacy
  `mem.addr r_mem = bus.e1.ptr` pin.
- `tools/pil-extract mem-air-facts` reports the Mem generated constraint
  groups, range-check hints, witness/fixed columns, and `mem.pil` range/bit
  source lines needed by `MemTableGeneratedAirFacts`.
- `MemTableGeneratedAirSource` is the typed Lean target for the stage-2 source
  columns/facts; replay and timeline constructors consume it.
- `memTableGeneratedAirSource_of_parts` builds that source from
  `generatedAt`, row ranges, and segment ranges.
- `MemTableGeneratedConstraintFacts` now splits the generated constraints into
  `segment_every_row` (`0..=23`) and `permutation_every_row` (`24..=33`);
  `memTableGeneratedAirSource_of_constraintFacts` recombines them with range
  facts for generated Lean modules.

Latest verification:
- Lean LSP diagnostics: `ZiskFv/AirsClean/FullEnsemble/Balance.lean`
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `trust/scripts/check-all.sh`
- `cargo test --manifest-path tools/pil-extract/Cargo.toml`
- `cargo run --manifest-path tools/pil-extract/Cargo.toml --quiet -- \
  mem-air-facts --pilout build/zisk.pilout --air Mem \
  --pil-source zisk/state-machines/mem/pil/mem.pil \
  --output /tmp/mem-air-facts-report.md`
- `lean_verify` on the new split-facts theorem/constructors: no `sorryAx`
- `git diff --check`
- `rg -n "h_mem_legacy_addr|_h_mem_legacy_addr|mem_legacy_addr" ZiskFv/Compliance`
  returns no hits.

Last full `nix run .#test`: commit `98202ebc`.

Next step: make the extractor/generated Lean module prove
`MemTableGeneratedConstraintFacts`, `MemTableGeneratedRangeFacts`, and
`MemSegmentGeneratedRangeFacts` for the witness-selected Mem table.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
