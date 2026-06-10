Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone; load
arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Load arms
now require `FullWitnessGeneratedTimelineEvidence`, which wraps the full-witness
timeline evidence and carries the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`) for the witness-selected Mem
table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; stage-2 `gsum`/`im`,
table-global segment/permutation constants, challenges, ranges, and generated
assertions are outside the component.

Current slice: generated artifact is explicit at the load-facing boundary.
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts` packages
ProverData-backed Clean assertion/lookup witnesses into
`FullWitnessGeneratedTimelineEvidence`, whose inner timeline evidence still
carries only the Mem sidecar source plus residual Sail timeline facts.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessGeneratedTimelineEvidence` carries ProverData witness facts and
  proves the stored sidecars match the generated sidecar packager.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range
  hints, ProverData keys, and the generated timeline constructor.

Latest verification:
- Lean LSP diagnostics on `OpEnvelope.lean`: clean; `Balance.lean` LSP timed
  out, so verified by targeted Lake build.
- `lean_verify` on the generated constructor and coercion: no source warnings.
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`.
- `lake build ZiskFv.Compliance`.
- Focused mem-air-facts report test and full
  `cargo test --manifest-path tools/pil-extract/Cargo.toml` (69 tests).
- Regenerated `/tmp/mem-air-facts-report.md`; it names the generated wrapper.
- `trust/scripts/check-all.sh`.
- Rustfmt check has broad pre-existing churn outside this slice.
- Last full `nix run .#test`: commit `98202ebc`.

Next step: generate/prove `FullWitnessMemAirSourceProverDataWitnessFacts` in
the generated artifact. Broadening the Clean table/component model is only the
fallback if that artifact must be checked inside the generic full ensemble.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
