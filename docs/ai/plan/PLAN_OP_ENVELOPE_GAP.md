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

No wrapper-signature shrinkage. No checked-in generated Aeneas Lean or LLBC.
At this point in the slice sequence the global theorem still depended on
`ZiskFv.Compliance.aeneas_bridge_trust`; the later boundary-reduction slice
removes that axiom.

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

## Next Slice: DIV/DIVU/DIVW/DIVUW/REM/REMU/REMW/REMUW

Finish the Mul/Div/Rem tail group with the ArithDiv provider route. These arms
share external ArithDiv Main-row routing and fall-through controls; the
unsigned/signed and quotient/remainder split selects opcode literals, while the
W forms use `m32 = 1`.

- [x] Add main-Lake helpers deriving DIV/REM-family Main pins and row-control facts from extracted-row constants.
- [x] Extend `aeneasBridgeTrust` and add DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, and REMUW `OpEnvelope` constructors/bridge theorems using those derived Main facts.
- [x] Add staged Aeneas generated checks for DIV/REM-family row shapes.
- [x] Update extraction/trust docs to describe the DIV/REM-family slice.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Final Hardening: Exhaustive Bridge Predicate

Audit `OpEnvelope.aeneasBridgeTrust` after the opcode-family slices and remove
the wildcard branch so constructor coverage is checked by Lean. This narrows
the local bridge predicate. At this point the global
`ZiskFv.Compliance.aeneas_bridge_trust` axiom still existed; the following
boundary-reduction slice removes it.

- [x] Add an explicit FENCE bridge-predicate case using derived activation/opcode pins.
- [x] Add explicit `auipc_x0` and `jal_x0` cases documenting that those no-memory arms still carry no bridge payload.
- [x] Remove the wildcard `| _ => True` branch from `OpEnvelope.aeneasBridgeTrust`.
- [x] Run focused `lake build ZiskFv.Compliance.AeneasBridgeTrust`.
- [x] Update extraction/trust docs to describe the narrowed predicate.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Boundary Reduction: Retire `aeneas_bridge_trust`

Remove the broad bridge-trust conjunct from the global theorem conclusion and
delete the corresponding axiom. The local `OpEnvelope.aeneasBridgeTrust`
predicate and extracted-shape theorems remain as audit helpers for the
production-backed proof slices, but `zisk_riscv_compliant_program_bus` no
longer proves that predicate by axiom.

- [x] Remove `env.aeneasBridgeTrust` from `OpEnvelope.exec_eq`.
- [x] Remove the `aeneas_bridge_trust` proof obligation from `zisk_riscv_compliant_program_bus`.
- [x] Delete the `ZiskFv.Compliance.aeneas_bridge_trust` axiom declaration.
- [x] Run `lake build ZiskFv.Compliance`.
- [x] Update extraction/trust docs to describe the retired axiom and remaining caller-burden obligations.
- [x] Run `trust/scripts/regenerate.sh`.
- [x] Run `trust/scripts/check-all.sh`.
- [x] Run `trust/scripts/check-all-semantic.sh`.
- [x] Run `nix run .#aeneas-production-extract`.

## Caller-Burden Audit: Residual Structural Obligations

After the broad axiom was retired, the global axiom closure is smaller but the
canonical and wrapper caller-burden ledgers still expose explicit
soundness-relevant obligations. The remaining nonzero categories are:
`bridge = 119`, canonical `row_shape = 27`, wrapper `row_shape = 37`, and
`bus_shape = 27`.

Initial classification:

- U/control-flow and memory `promises` bundles are semantic state/bus inputs;
  they should not be hidden by repackaging without imported generated proof
  evidence.
- Binary/shift/mul/div/rem bridge equalities tie decoded Sail inputs to
  provider-row values; those need production extraction/provider proofs, not
  signature-only reshaping.
- The W-shift trio (`SLLW`, `SRLW`, `SRAW`) still carries explicit execution
  and memory-bus shape binders plus destination-register shape facts. These
  look like the narrowest structural reduction candidate because they mirror a
  bundleable bus-channel shape already consumed as ordinary proof data.

- [x] Re-read `STATUS.md`, this plan, and the generated caller-burden ledgers.
- [x] Classify residual `bridge`, `row_shape`, and `bus_shape` categories.
- [x] Inspect the W-shift wrapper/canonical proofs for an honest internalized
      shape witness.
- [x] If feasible, refactor the W-shift trio to consume a single documented
      structural witness instead of individual bus/row-shape binders.
- [x] Regenerate ledgers and verify that the diff is a real reduction or a
      documented structural boundary, not semantic laundering.
- [x] Run required build/trust/extraction checks.
- [x] Commit the reduction slice.

Ledger result: the W-shift refactor is a structural consolidation, not a
semantic discharge. It removes all 27 explicit `bus_shape` caller-burden rows
and reduces `row_shape` by 9 rows in both canonical/wrapper ledgers, while
adding 3 `bridge` rows because `SLLW`, `SRLW`, and `SRAW` now expose one
`RTypePromises` bundle each. Total canonical rows dropped from 1104 to 1062;
wrapper rows dropped from 1165 to 1123.

## Phase 2: Caller-Burden Reduction

Continue beyond opcode coverage by shrinking or reclassifying the remaining
caller-supplied proof obligations only when the new boundary is a real proof
source or a documented structural witness. The goal is not to game the ledger:
renaming or hiding semantic assumptions under opaque bundles is not progress.

Current acceptance target for this phase:

- Structural shape obligations should either be derived from existing row/bus
  evidence or grouped under documented witness types whose source is explicit.
- Semantic bridge obligations should remain visible until they are discharged
  by production extraction/provider proofs.
- Promise obligations should remain visible unless they are derived from Sail
  state, decoded instruction data, and bus/effect facts already available at
  the theorem boundary.
- Every reduction must land with regenerated ledgers and a note explaining what
  moved and why the trust boundary did not get less honest.

Work queue:

- [x] Finish the W-shift (`SLLW`/`SRLW`/`SRAW`) structural cleanup using the
      existing `RTypePromises` shape where appropriate.
- [x] Regenerate caller-burden ledgers and compare `bridge`, `row_shape`, and
      `bus_shape` counts before/after the W-shift cleanup.
- [x] Audit U/control-flow (`LUI`, `AUIPC`, `JAL`, `JALR`, `FENCE`) residual
      row-shape and promise obligations and separate structural facts from
      semantic promise facts.
- [x] Audit load/store residual `LoadPromises`/`StorePromises` and
      `LoadCleanWitness` obligations against the Clean Main/Mem bridge
      witnesses already present in `OpEnvelope`.
- [x] Audit Binary/BinaryExtension/Arith provider bridge equalities by family
      and record which require generated production proofs rather than local
      refactors.
- [x] For each honest reduction slice, update docs, run build/trust/extraction
      checks, and commit.

U/control-flow audit result: `LUI`, `AUIPC`, and `JAL` canonical proofs already
used row-provenance wrappers, but the wrapper caller-burden ledger still
tracked older pin-based compatibility wrappers because those owned the
`equiv_<OP>` names. The active row-provenance wrappers now own `equiv_LUI`,
`equiv_AUIPC`, and `equiv_JAL`, while compatibility wrappers are named
`*_of_main_pins`. This is a ledger-surface correction: wrapper row_shape drops
from 28 to 22, but remaining U/control promise and PC/link bridge obligations
remain visible and require generated-proof or state/bus integration.

Load/store audit result: the active `equiv_<OP>` load/store wrappers already
consume shared `BusRows` plus structural `LoadPromises`/`StorePromises` bundles
and Clean memory witnesses. Those promise bundles still contain real theorem
inputs: RISC-V platform assumptions, opcode/state assumptions, execution-bus
length/multiplicity, nextPC alignment, and memory-bus multiplicity/address-space
facts. The full-ensemble constructors such as
`*_eq_of_full_ensemble_mem_provider` and `*_eq_of_full_ensemble_main_c` can
derive selected Clean witness fields from same-message evidence, but switching
the public `equiv_<OP>` ledger surface to those constructors would add the
larger generated/full-ensemble artifact rather than discharge the residual
promises. No load/store caller-burden reduction is therefore honest until the
generated/full-ensemble facts are integrated as a maintained proof source.

Provider-family audit result: the remaining `bridge` rows are not accidental
wrapper clutter. Binary/BinaryAdd/BinaryExtension rows are Sail-input to
provider-row equalities (`binaryRowA64`, `binaryRowB64`, `rowA64`,
`rowA32`, `rowShiftAmount`, `rowShiftAmount32`) plus structural
`RTypePromises`, `ITypePromises`, `ShiftImmPromises`, and
`ShiftWImmPromises`. ArithMul/ArithDiv/Rem rows are provider-limb operand
bridges (`h_rs1_value`, `h_rs2_value`) plus division/remainder edge
preconditions (`h_op2_ne`, `h_no_overflow`, and W-form variants). Existing
Clean balance modules already derive provider-row `matches_entry` witnesses
from active Main op-bus interactions, but the operand equalities and arithmetic
side conditions must come from production row/provider facts and Sail input
facts. A local signature reshuffle would only hide those obligations, so this
phase records them as Phase 3 generated-proof integration work.

## Phase 3: Generated Proof Integration

The opcode-family slices currently validate generated Aeneas facts in a staged
extraction harness while main Lake consumes hand-written extracted-shape
helpers. To close the original `witness rows -> OpEnvelope` gap, the generated
proof facts need a maintained path into the proof boundary.

Acceptance target:

- Generated/production-backed facts used to construct `OpEnvelope` evidence are
  checked as part of the normal verification flow, not only as an external
  staged artifact.
- The proof boundary makes clear which facts come from decoded instruction
  data, lowerer/transpiler output, Main rows, bus rows, provider rows, memory
  rows, and Sail state assumptions.
- Residual caller-burden entries that remain after this phase are documented as
  deliberate public theorem inputs, not accidental opcode-specific proof holes.

Work queue:

- [ ] Decide the integration path for generated Aeneas Lean: import into main
      Lake, checked generated module, or a documented verified bridge artifact.
- [ ] Wire the first production-backed generated fact into main verification for
      one already-covered family, starting with the smallest row-shape case.
- [ ] Extend the integration pattern across the U/control-flow row-shape facts.
- [ ] Extend the integration pattern across Binary/BinaryExtension provider
      source-lane facts where the production extraction already computes the
      required row constants.
- [ ] Extend or explicitly defer memory/load/store generated facts depending on
      available production proof coverage.
- [ ] Update trust scripts so generated-proof integration regressions are
      visible in CI-style checks.

## Phase 4: Final Boundary Verification

Once caller-burden reductions and generated-proof integration have landed, the
final pass verifies that the public theorem boundary matches the documented
target and that the remaining trust surface is intentional.

Acceptance target:

- `zisk_riscv_compliant_program_bus` no longer depends on broad temporary
  envelope-evidence axioms.
- Caller-burden ledgers contain only documented theorem inputs or explicitly
  deferred assumptions.
- Global axiom closure matches the expected trust baseline.
- Extraction, semantic trust checks, and main Lake builds all pass from a clean
  worktree.

Work queue:

- [ ] Re-run and review all caller-burden ledgers after the final reduction
      slice.
- [ ] Update `docs/extraction/op-envelope-gap-plan.md`,
      `docs/ai/PROJECTS.md`, and `trust/trusted-base.md` with the final
      theorem boundary.
- [ ] Run `lake build ZiskFv.Compliance`.
- [ ] Run `trust/scripts/regenerate.sh`.
- [ ] Run `trust/scripts/check-all.sh`.
- [ ] Run `trust/scripts/check-all-semantic.sh`.
- [ ] Run `nix run .#aeneas-production-extract`.
- [ ] Commit the final boundary-verification slice.

## Verification

Required commands:

```bash
lake build ZiskFv.Compliance
trust/scripts/regenerate.sh
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
nix run .#aeneas-production-extract
```
