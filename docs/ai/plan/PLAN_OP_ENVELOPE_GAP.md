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

## Next Slice: JAL

Continue depth-first through U/J/control-flow row-mode evidence with the JAL
rd-write route.

- [x] Add a main-Lake helper deriving `JalRowMode` from extracted-row constants.
- [x] Add a JAL `OpEnvelope` constructor/bridge theorem that uses the helper to fill the real `row_mode` field.
- [x] Add a staged Aeneas generated check for JAL row-mode evidence.
- [x] Update extraction/trust docs to describe the JAL slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: JALR

Continue depth-first through U/J/control-flow evidence with the JALR final-row
control pins. JALR does not currently use a dedicated `JalrRowMode` provenance
structure; its `OpEnvelope` arm consumes `MainRowPins` plus explicit control
pins.

- [x] Add main-Lake helpers deriving JALR final-row `MainRowPins` and control pins from extracted-row constants.
- [x] Add a JALR `OpEnvelope` constructor/bridge theorem that uses those helpers to fill the real pins/control fields.
- [x] Add a staged Aeneas generated check for JALR control-pin evidence.
- [x] Update extraction/trust docs to describe the JALR slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: FENCE

Finish the U/J/control-flow group with FENCE activation/opcode pins. FENCE has
no dedicated bridge predicate payload, but its `OpEnvelope` arm still consumes
`MainRowPins main r_main 0 OP_FLAG`.

- [x] Add a main-Lake helper deriving FENCE `MainRowPins` from extracted-row constants.
- [x] Add a FENCE `OpEnvelope` constructor/bridge theorem that uses the helper to fill the real pins field.
- [x] Add a staged Aeneas generated check for FENCE pin evidence.
- [x] Update extraction/trust docs to describe the FENCE slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: ADD/ADDI/ADDW

Continue depth-first into the Binary provider-route group. These arms consume
external Main opcode pins plus provider-row source-lane equalities; this slice
derives the Main pins from production row-shape provenance and proves the
current `aeneasBridgeTrust` branches from the existing provider-lane fields.

- [x] Add main-Lake helpers deriving ADD/ADDI and ADDW `MainRowPins` from extracted-row constants.
- [x] Add ADD, ADDI, and ADDW `OpEnvelope` constructors/bridge theorems that use those helpers to fill the real pins fields.
- [x] Add staged Aeneas generated checks for ADD, ADDI, and ADDW external provider-route row shapes.
- [x] Update extraction/trust docs to describe the ADD/ADDI/ADDW slice.
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
