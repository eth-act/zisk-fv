Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone; load
arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble support for the Mem sidecars. Existing
`componentWithDualMemBus` emits only row constraints plus MemBus provider rows,
not the stage-2 permutation/range/assertion source facts.

Latest audit: structural gap, not a missing lemma. The Mem table input has only
`MemRow`; `gsum`/`im`, table-global segment/permutation constants, challenges,
ranges, and generated assertions are outside the component, and per-row locals
would not make table-global constants generic.

Current slice: make the sidecar source surface reproducible. The stored
boundary now carries `FullWitnessMemAirSourceRawSidecars` directly, and the Nix
`extracted-lean` derivation emits `MemAirFacts.md`; `populate` copies it to
`build/extraction/MemAirFacts.md` beside the generated extraction files.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range hints,
  witness/fixed columns, `mem.pil` range/bit lines, and Lean coverage.
- `MemTableGeneratedAirSource` remains the table-level path from Clean
  assertion/lookup witnesses.

Latest verification:
- Lean LSP diagnostics on `Balance`: clean after sidecar-boundary edit
- `lean_verify` on sidecar/raw compatibility adapter and timeline constructors:
  no source warnings
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `lake build ZiskFv.Compliance`
- `trust/scripts/check-all.sh`
- `cargo test --manifest-path tools/pil-extract/Cargo.toml` (68 tests)
- Regenerated `/tmp/mem-air-facts-report.md`; `git diff --check`
- Lean LSP + `lean_verify` clean for direct sidecar timeline constructor
- Nix eval for `.#packages.x86_64-linux.extracted-lean` and `.#apps.x86_64-linux.populate`
- local `pil-extract mem-air-facts`; `nix flake check --no-build`
- `populate` now requires generated `MemAirFacts.md` rather than copying it opportunistically
- Last full `nix run .#test`: commit `98202ebc`

Next step: generate or check `FullWitnessMemAirSourceRawSidecars` for the
witness-selected mutable Mem table; broader table/component model support is
still the fallback if generated sidecars cannot be made reproducible.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
