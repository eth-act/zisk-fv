Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure; `LoadPromises.mem_read` is gone and
load arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Load arms
now require `FullWitnessGeneratedTimelineEvidence`, which wraps the full-witness
timeline evidence and carries the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`) for the witness-selected Mem
table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; stage-2 `gsum`/`im`,
table-global segment/permutation constants, challenges, ranges, and generated
assertions are outside the component.

Current slice: the generated extraction layer is being revived without the old
root `ZiskFv.Circuit` API. `pil-extract` now emits an `Extraction.Circuit`
shim, per-AIR extraction imports use `Extraction.Circuit.*`, and the generated
Mem gate compiles `Extraction.Circuit`, `Extraction.Mem`, and
`Extraction.MemGeneratedArtifact` under `build/extraction`.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessGeneratedTimelineEvidence` carries ProverData witness facts and
  proves the stored sidecars match the generated sidecar packager.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range
  hints, ProverData keys, generated timeline constructor, witness contract, and
  the raw-facts adapter path.
- `tools/pil-extract mem-generated-artifact` emits checked witness/raw assembly
  helpers and the timeline constructor wrapper; the gate now also checks the
  generated Mem constraint source.

Latest verification:
- Full `cargo test --manifest-path tools/pil-extract/Cargo.toml` (72 tests).
- Regenerated local `Circuit.lean`, `Mem.lean`, and
  `MemGeneratedArtifact.lean` under `build/extraction/Extraction`.
- Exact generated-Mem gate sequence passes: compile `Circuit.lean` to
  `Circuit.olean`, then compile `Mem.lean` and `MemGeneratedArtifact.lean`
  with `LEAN_PATH=$(pwd)/build/extraction:$(lake env printenv LEAN_PATH)`.
- `lake build ZiskFv.Compliance`, `trust/scripts/check-all.sh`,
  `nix flake check --no-build`, and `git diff --check`.
- Last full `nix run .#test`: commit `98202ebc`.

Next step: generate/prove the raw or witness ProverData Mem facts. Broadening
Clean table/component modeling is only the fallback.
