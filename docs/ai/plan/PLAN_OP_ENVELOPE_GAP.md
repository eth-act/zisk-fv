# Plan: Op Envelope Gap

## Summary

Implement the first depth-first proof slice for the `OpEnvelope` evidence gap. The target is LUI row-mode evidence: generated Aeneas output already checks the LUI row-shape projection, and main Lake already exposes `MainRowProvenance.LuiRowMode` as the proof-facing field consumed by `OpEnvelope.lui`.

## Checklist

- [x] Create project tracking files for this worktree.
- [x] Add a main-Lake helper deriving `LuiRowMode` from extracted-row constants.
- [x] Add a LUI `OpEnvelope` constructor/bridge theorem that uses the helper to fill the real `row_mode` field.
- [x] Add a staged Aeneas generated check for LUI row-mode evidence.
- [x] Update extraction/trust docs to describe the slice and remaining axiom boundary.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: AUIPC

Continue depth-first in the U/control-flow family by extending the same proof
shape to AUIPC row-mode evidence.

- [x] Add a main-Lake helper deriving `AuipcRowMode` from extracted-row constants.
- [x] Add an AUIPC `OpEnvelope` constructor/bridge theorem that uses the helper to fill the real `row_mode` field.
- [x] Add or confirm a staged Aeneas generated check for AUIPC row-mode evidence.
- [x] Update extraction/trust docs to describe the AUIPC slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Scope

No public theorem signature changes. No wrapper-signature shrinkage. No checked-in generated Aeneas Lean or LLBC. The global theorem is expected to keep depending on `ZiskFv.Compliance.aeneas_bridge_trust` after this slice.

## Verification

Required commands:

```bash
lake build ZiskFv.Compliance
trust/scripts/regenerate.sh
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
nix run .#aeneas-production-extract
```
