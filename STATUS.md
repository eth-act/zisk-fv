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

Current slice: raw ProverData facts now have checked assembly routes into the
generated witness target. Lean provides
`fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts`; the generated
wrapper emits `RawFacts`, raw per-table aliases, `buildRawFacts`,
`buildWitnessFactsFromRawFacts`, and `buildWitnessFactsFromRawParts`.

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
  helpers and the timeline constructor wrapper; trust docs name the gate.

Latest verification:
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`.
- `lake build ZiskFv.Compliance`.
- Focused wrapper/report tests and full
  `cargo test --manifest-path tools/pil-extract/Cargo.toml` (71 tests).
- Regenerated `/tmp` report/wrapper; `lake env lean /tmp/MemGeneratedArtifact.lean`.
- Regenerated populated wrapper; exact gate command
  `test -f build/extraction/Extraction/MemGeneratedArtifact.lean && lake env lean ...`.
- `trust/scripts/check-all.sh` and `git diff --check`.
- Last full `nix run .#test`: commit `98202ebc`.

Next step: generate/prove the raw or witness ProverData Mem facts. Broadening
Clean table/component modeling is only the fallback.
