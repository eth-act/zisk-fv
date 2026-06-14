# Tracked Aeneas Extraction

`ProductionM2.lean` is the canonical checked-in copy of the Aeneas-generated
Lean extraction for the production-backed ZisK RV64IM lowering surface.

Regenerate it from the pinned flake inputs with:

```bash
AENEAS_UPDATE_TRACKED=1 nix run .#aeneas-production-extract
```

CI runs:

```bash
nix run .#aeneas-production-extract-check-tracked
```

That command regenerates `build/aeneas-production-extraction/Lean/ProductionM2.lean`
and fails unless it is byte-identical to this tracked copy. Temporary LLBC files
and generated harness modules such as `GeneratedChecks.lean` remain untracked
under `build/`.
