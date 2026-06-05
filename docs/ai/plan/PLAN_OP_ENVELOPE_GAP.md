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

## Next Slice: SUB/SUBW/ADDIW

Finish the initial BinaryAdd/BinaryAddW provider-route group by covering the
remaining source-lane bridge shapes that match the ADD slice.

- [x] Add main-Lake helpers deriving SUB and SUBW `MainRowPins` from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add SUB, SUBW, and ADDIW `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for SUB, SUBW, and ADDIW external provider-route row shapes.
- [x] Update extraction/trust docs to describe the SUB/SUBW/ADDIW slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: AND/OR/XOR/SLT/SLTU

Continue depth-first through the Binary provider-route group with the R-type
logic and comparison operations. These share the same external Binary provider
route as ADD/SUB: Main opcode pins plus provider source-lane equalities.

- [x] Add main-Lake helpers deriving AND, OR, XOR, LT, and LTU `MainRowPins` from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add AND, OR, XOR, SLT, and SLTU `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for AND, OR, XOR, SLT, and SLTU external provider-route row shapes.
- [x] Update extraction/trust docs to describe the logic/comparison slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: ANDI/ORI/XORI/SLTI/SLTIU

Finish the Binary logic/comparison provider-route group by covering the I-type
immediate forms. ANDI/ORI/XORI use sign-extended immediate source-lane
equalities; SLTI/SLTIU additionally consume the Main `m32 = 0` row-control pin.

- [x] Extend `aeneasBridgeTrust` and add ANDI, ORI, XORI, SLTI, and SLTIU `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for ANDI, ORI, XORI, SLTI, and SLTIU external provider-route row shapes.
- [x] Update extraction/trust docs to describe the immediate logic/comparison slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: SLL/SRL/SRA

Enter the BinaryExtension shift provider-route group with the R-type 64-bit
shift forms. These use the shift static lookup component and bridge
`rowA64` plus `rowShiftAmount`, so they are a separate provider family from
the Binary arithmetic/logical operations.

- [x] Add main-Lake helpers deriving SLL, SRL, and SRA `MainRowPins` from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add SLL, SRL, and SRA `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for SLL, SRL, and SRA external shift-provider row shapes.
- [x] Update extraction/trust docs to describe the R-type shift slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: SLLI/SRLI/SRAI

Continue through BinaryExtension with the 64-bit immediate shift forms. These
reuse the same Main opcode pins and shift provider component as SLL/SRL/SRA,
but bridge `ShiftImmPromises` and an immediate shift amount instead of an
R-type second-register shift amount.

- [x] Extend `aeneasBridgeTrust` and add SLLI, SRLI, and SRAI `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for SLLI, SRLI, and SRAI external shift-provider row shapes.
- [x] Update extraction/trust docs to describe the immediate shift slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: SLLW/SRLW/SRAW

Continue through BinaryExtension with the 32-bit R-type shift forms. These use
the same shift provider component but select the W opcodes and bridge
`rowA32` plus `rowShiftAmount32`.

- [x] Add main-Lake helpers deriving SLLW, SRLW, and SRAW `MainRowPins` from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add SLLW, SRLW, and SRAW `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for SLLW, SRLW, and SRAW external shift-provider row shapes.
- [x] Update extraction/trust docs to describe the R-type W shift slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: SLLIW/SRLIW/SRAIW

Finish the BinaryExtension W-shift group with the 32-bit immediate shift forms.
These reuse the W opcode pins and shift provider component from SLLW/SRLW/SRAW,
but bridge `ShiftWImmPromises` and immediate shift amounts.

- [x] Extend `aeneasBridgeTrust` and add SLLIW, SRLIW, and SRAIW `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for SLLIW, SRLIW, and SRAIW external shift-provider row shapes.
- [x] Update extraction/trust docs to describe the immediate W shift slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: SB/SH/SW/SD

Move into the store-family Main-only shape. Stores are larger than the shift
provider slices: they use internal `OP_COPYB`, carry store width/`store_pc`
facts, and include Clean Main-row, memory-bus, address, store-value, and
byte-lane witnesses.

- [x] Add main-Lake helpers deriving store `OP_COPYB` pins and width/control facts from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add SB, SH, SW, and SD `OpEnvelope` constructors/bridge theorems.
- [x] Add staged Aeneas generated checks for SB, SH, SW, and SD store row shapes.
- [x] Update extraction/trust docs to describe the store-family slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Scope

No public theorem signature changes. No wrapper-signature shrinkage. No checked-in generated Aeneas Lean or LLBC. The global theorem is expected to keep depending on `ZiskFv.Compliance.aeneas_bridge_trust` after this slice.

## Next Slice: LD/LBU/LHU/LWU

Continue through the Main/Mem load route with LD plus zero-extension loads.
These share the internal `OP_COPYB` Main row with stores, but use the load
memory-bus witness path and widths `8`, `1`, `2`, and `4`. Signed LB/LH/LW use
external BinaryExtension sign-extension opcodes and remain a separate provider
slice.

- [x] Extend `aeneasBridgeTrust` and add LD, LBU, LHU, and LWU `OpEnvelope` constructors/bridge theorems using store-slice `OP_COPYB`, width, and Clean `store_pc` helpers.
- [x] Add staged Aeneas generated checks for LD, LBU, LHU, and LWU load row shapes.
- [x] Update extraction/trust docs to describe the zero-extension load slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: LB/LH/LW

Continue through the signed-load BinaryExtension route. LB, LH, and LW share
the Clean Main/Mem load path with the zero-extension loads, but use external
`OP_SIGNEXTEND_B`, `OP_SIGNEXTEND_H`, and `OP_SIGNEXTEND_W` Main pins plus the
existing BinaryExtension static lookup/match witnesses.

- [x] Add main-Lake helpers deriving signed-load Main pins and width/control facts from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add LB, LH, and LW `OpEnvelope` constructors/bridge theorems using derived sign-extension pins, width, and Clean `store_pc` helpers.
- [x] Add staged Aeneas generated checks for LB, LH, and LW signed-load row shapes.
- [x] Update extraction/trust docs to describe the signed-load provider slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: BEQ/BNE/BLT/BGE/BLTU/BGEU

Continue through the branch route. Branch `OpEnvelope` arms do not currently
carry explicit Main-row pin fields, so this slice makes the Aeneas bridge
predicate expose the branch opcode/control pins and the fall-through jump
offset side that distinguishes normal branches from negated branches.

- [x] Add main-Lake helpers deriving branch Main pins, branch controls, and fall-through jump-offset facts from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add BEQ, BNE, BLT, BGE, BLTU, and BGEU `OpEnvelope` constructors/bridge theorems using those derived branch facts.
- [x] Add staged Aeneas generated checks for branch row shapes.
- [x] Update extraction/trust docs to describe the branch slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Next Slice: MUL/MULH/MULHU/MULHSU/MULW

Enter the Mul/Div/Rem tail group with the ArithMul provider route. These arms
share external ArithMul Main-row routing, but select different opcode literals
and use `m32 = 1` only for MULW.

- [x] Add main-Lake helpers deriving MUL-family Main pins and row-control facts from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add MUL, MULH, MULHU, MULHSU, and MULW `OpEnvelope` constructors/bridge theorems using those derived Main facts.
- [x] Add staged Aeneas generated checks for MUL-family row shapes.
- [x] Update extraction/trust docs to describe the MUL-family slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Verification

Required commands:

```bash
lake build ZiskFv.Compliance
trust/scripts/regenerate.sh
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
nix run .#aeneas-production-extract
```
