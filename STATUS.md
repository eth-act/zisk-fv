Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure; `LoadPromises.mem_read` is gone and
load arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Load arms
now require `FullWitnessGeneratedTimelineEvidence`, which wraps the full-witness
timeline evidence and carries the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`) for the witness-selected Mem table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; Mem range lookup witness
definitions exist, but the active component does not emit them, and segment
ranges are sidecar-global rather than row inputs.

Current slice: generated Mem source facts now have one raw target.
`MemGeneratedConstraintBridge.lean` maps extracted `constraint_0..33` to
`RawConstraintFacts`, wraps them with raw ranges as `ExtractedRawSourceFacts`,
and exposes raw/witness builders for that target.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessGeneratedTimelineEvidence` carries ProverData witness facts and
  proves the stored sidecars match the generated sidecar packager.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range hints,
  ProverData keys, generated timeline constructor, and witness contract.
- `tools/pil-extract mem-generated-artifact` emits checked witness/raw assembly
  helpers and the timeline constructor wrapper.
- `tools/pil-extract mem-generated-constraint-bridge` emits the checked
  ProverData circuit instance, extracted constraint surface, `ExtractedRawSourceFacts`,
  and raw/witness builders.

Latest verification:
- Full `cargo test --manifest-path tools/pil-extract/Cargo.toml` (73 tests).
- Regenerated local `Circuit.lean`, `Mem.lean`, `MemGeneratedArtifact.lean`,
  and `MemGeneratedConstraintBridge.lean` under `build/extraction/Extraction`.
- Exact generated-Mem gate sequence passes: compile `Circuit.lean` to
  `Circuit.olean`, compile `Mem.lean` and `MemGeneratedArtifact.lean` to
  oleans, then compile `MemGeneratedConstraintBridge.lean` with
  `LEAN_PATH=$(pwd)/build/extraction:$(lake env printenv LEAN_PATH)`.
- Last broad bridge gate: `lake build ZiskFv.Compliance`,
  `trust/scripts/check-all.sh`, `nix flake check --no-build`, and
  `git diff --check` at commit `465470dc`.
- Last full `nix run .#test`: commit `98202ebc`.

Next step: decide whether to broaden Clean Mem/component modeling for range
provenance or keep raw row/segment range facts as explicit generated sidecar input.
