Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone; load
arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Lean now has
a concrete `witness.data` witness target
(`FullWitnessMemAirSourceProverDataWitnessFacts`), but generated code still
must supply it for the witness-selected mutable Mem table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; stage-2 `gsum`/`im`,
table-global segment/permutation constants, challenges, ranges, and generated
assertions are outside the component.

Current slice: sidecar source surface is reproducible and data-keyed.
`fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts` packages
ProverData-backed Clean assertion/lookup witnesses into the sidecar boundary
stored by `FullWitnessMemoryTimelineEvidence`.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range
  hints, sidecar ProverData keys, pilout sources, and Lean coverage.
- `MemTableGeneratedAirSource` remains the table-level path from Clean
  assertion/lookup witnesses.

Latest verification:
- Lean LSP diagnostics on `Balance.lean`: clean after witness-target edit.
- `lean_verify` on witness/raw adapters: no source warnings.
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`.
- Focused mem-air-facts report test and full
  `cargo test --manifest-path tools/pil-extract/Cargo.toml` (69 tests).
- Regenerated `/tmp/mem-air-facts-report.md`; it names the witness target and
  ProverData sidecar keys.
- `lake build ZiskFv.Compliance`.
- `trust/scripts/check-all.sh`.
- `git diff --check` clean.
- Rustfmt check still has broad pre-existing churn outside this slice.
- Last full `nix run .#test`: commit `98202ebc`.

Next step: make generated/full-ensemble output actually supply
`FullWitnessMemAirSourceProverDataWitnessFacts`; broader table/component model
support is still the fallback.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
