Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone; load
arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble support for the Mem raw facts. Existing
`componentWithDualMemBus` emits only row constraints plus MemBus provider rows,
not the stage-2 permutation/range/assertion source facts.

Latest audit: structural gap, not a missing lemma. The Mem table input has only
`MemRow`; `gsum`/`im`, table-global segment/permutation constants, challenges,
ranges, and generated assertions are outside the component, and per-row locals
would not make table-global constants generic.

Current slice: add a table-level generated-output contract. Lean now has
`MemTableGeneratedRawSourceSidecar` per mutable Mem table,
`FullWitnessMemAirSourceRawSidecars` for a full witness, and adapters to the
existing `FullWitnessMemAirSourceRawFacts` / source-selector path. Extractor
and docs text now point generated code at the sidecar target.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawFacts`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range hints,
  witness/fixed columns, `mem.pil` range/bit lines, and Lean coverage.
- `MemTableGeneratedAirSource` remains the table-level path from Clean
  assertion/lookup witnesses.

Latest verification:
- Lean LSP diagnostics on `Balance`: clean after sidecar edit
- `lean_verify` on sidecar adapters/selectors: no source warnings
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `cargo test --manifest-path tools/pil-extract/Cargo.toml`
- Regenerated `/tmp/mem-air-facts-report.md`; `git diff --check`
- Last wider build: `Compliance`; last trust gate: `check-all.sh`
- Last full `nix run .#test`: commit `98202ebc`

Next step: choose the next raw-facts route: checked generated-witness artifact
or broader table/component model support for Mem AIR source columns.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
