# Plan: Close the OpEnvelope Evidence Gap

## Summary

The current global soundness theorem:

```lean
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

takes an already-constructed `OpEnvelope state m r_main`. That envelope bundles
the opcode case plus many proof fields about decoded instruction data, lowered
witness rows, bus rows, provider rows, row shape, and Sail-side promise facts.

In the intended pipeline:

```text
RISC-V instruction
  -> ZisK decoder
  -> ZisK transpiler / lowerer
  -> witness rows
  -> Lean OpEnvelope
  -> wrapper proofs
  -> global soundness theorem
```

the current proof gap is:

```text
witness rows -> Lean OpEnvelope
```

The long-term target is proof-first: derive the `OpEnvelope` evidence from the
extracted ZisK/Aeneas path and extracted AIR facts, instead of accepting those
facts from the caller of the global theorem.

## Current Gap

`OpEnvelope` is a proof-facing bundle. For each opcode arm it contains the data
and proof fields needed by that opcode's wrapper theorem. These include facts
such as source-lane values, destination write lanes, row-mode/provenance facts,
operation-bus matches, provider-row matches, bus shape, immediate/PC/link
equalities, and Sail promise predicates.

The current branch makes part of this explicit through:

```text
ZiskFv.Compliance.aeneas_bridge_trust
```

That is useful, but incomplete. The caller-burden ledgers still show externally
supplied `bridge`, `row_shape`, `bus_shape`, and `promises` fields. Those fields
are soundness assumptions unless they are derived before the global theorem
uses them.

## Target Theorem Boundary

The desired final boundary is closer to:

```text
valid extracted ZisK rows
  + decoded/lowered instruction evidence from the production path
  + explicit bus/provider/memory assumptions
  -> Sail-equivalent state transition
```

The final public theorem should not require a caller to hand-assemble
opcode-specific `OpEnvelope` evidence. Instead, the proof should construct or
derive the needed envelope facts from the extracted decoder/lowerer/witness-row
pipeline.

## Milestones

1. **Make the current trust boundary fully explicit.**

   Replace the partial Aeneas bridge boundary with a named temporary
   `OpEnvelope` evidence trust boundary that covers all externally supplied
   soundness-relevant envelope evidence. The generated caller-burden ledgers are
   the inventory for this axiom. This is not the final state; it is the honest
   interim ledger state.

2. **Classify every envelope field by source.**

   Add or regenerate an inventory that groups `OpEnvelope` fields by where they
   should ultimately come from:

   - decoder instruction fields
   - production lowerer/transpiler output
   - Main row constraints
   - operation bus
   - memory bus
   - Binary/Arith/Mem provider tables
   - Sail state/profile assumptions
   - known defect exclusions

3. **Connect generated Aeneas Lean to a small proof slice.**

   Start with the already-tested production-backed cases:

   - LUI
   - AUIPC
   - JAL
   - JALR
   - ADD
   - ADDI
   - ADDW

   The first objective is not full theorem cleanup. It is to prove that generated
   Aeneas facts can discharge real `OpEnvelope` fields.

   The first concrete slice is LUI row-mode evidence. Because generated Aeneas
   Lean is currently staged under `build/aeneas-production-extraction` rather
   than imported by the main Lake project, this slice has two halves:

   - the staged Aeneas harness proves that `extract_lui_from_inst` computes the
     row-shape constants needed for `MainRowProvenance.LuiRowMode`;
   - main Lake proves `MainRowProvenance.luiRowMode_of_extracted_shape`, the
     proof-facing theorem showing those constants are exactly enough to fill the
     `OpEnvelope.lui` `row_mode` field.
   - main Lake also exposes `OpEnvelope.luiOfExtractedShape` and
     `OpEnvelope.aeneasBridgeTrust_luiOfExtractedShape`, which construct the
     LUI envelope with that derived row-mode field and prove the LUI branch of
     `OpEnvelope.aeneasBridgeTrust` from extracted row-shape equalities plus
     the remaining dynamic LUI facts.

   This is a proof-slice validation, not retirement of
   `aeneas_bridge_trust`. The broad axiom remains in the global closure until
   the generated facts are imported or otherwise connected for every
   soundness-relevant envelope field.

   The same shape now extends to AUIPC row-mode evidence:

   - the staged Aeneas harness proves that `extract_auipc_from_inst` computes
     the row-shape constants needed for `MainRowProvenance.AuipcRowMode`;
   - main Lake proves `MainRowProvenance.auipcRowMode_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.auipcOfExtractedShape` and
     `OpEnvelope.aeneasBridgeTrust_auipcOfExtractedShape`, which construct the
     AUIPC envelope with that derived row-mode field and prove the AUIPC branch
     of `OpEnvelope.aeneasBridgeTrust` from extracted row-shape equalities plus
     the remaining dynamic AUIPC facts.

   The same shape now covers the JAL rd-write route:

   - the staged Aeneas harness proves that `extract_jal_from_inst` computes the
     row-shape constants needed for `MainRowProvenance.JalRowMode`;
   - main Lake proves `MainRowProvenance.jalRowMode_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.jalOfExtractedShape` and
     `OpEnvelope.aeneasBridgeTrust_jalOfExtractedShape`, which construct the
     JAL envelope with that derived row-mode field and prove the JAL branch of
     `OpEnvelope.aeneasBridgeTrust` from extracted row-shape equalities plus
     the remaining dynamic JAL facts.

   JALR is a related but different proof slice because the current
   `OpEnvelope.jalr` arm consumes `MainRowPins` and direct control pins instead
   of a dedicated `JalrRowMode` provenance structure:

   - the staged Aeneas harness proves that `extract_jalr_from_inst` computes
     the final-row external `OP_AND` and control-pin constants;
   - main Lake proves `MainRowProvenance.jalrPins_of_extracted_shape` and
     `MainRowProvenance.jalrControl_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.jalrOfExtractedShape` and
     `OpEnvelope.aeneasBridgeTrust_jalrOfExtractedShape`, which construct the
     JALR envelope with derived pins/control fields and prove the JALR branch of
     `OpEnvelope.aeneasBridgeTrust` from extracted row-shape equalities plus
     the remaining dynamic JALR facts.

   FENCE completes the first U/J/control-flow proof-slice group:

   - the staged Aeneas harness proves that `extract_fence_from_inst` computes
     the internal `OP_FLAG` activation/opcode constants;
   - main Lake proves `MainRowProvenance.fencePins_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.fenceOfExtractedShape` and
     `OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape`, which construct the
     FENCE envelope with derived activation/opcode pins and prove the FENCE
     branch of `OpEnvelope.aeneasBridgeTrust` from extracted row-shape
     equalities plus the remaining dynamic FENCE facts.

   The next slice enters the Binary provider-route group for ADD, ADDI, and
   ADDW:

   - the staged Aeneas harness proves that regular ADD and ADDI lower to
     external `OP_ADD` rows, while ADDW lowers to an external `OP_ADD_W` row;
   - main Lake proves `MainRowProvenance.addPins_of_extracted_shape` and
     `MainRowProvenance.addwPins_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.addViaBinaryOfExtractedShape`,
     `OpEnvelope.addiViaBinaryOfExtractedShape`, and
     `OpEnvelope.addwOfExtractedShape`, plus matching
     `OpEnvelope.aeneasBridgeTrust_*OfExtractedShape` theorems. These
     constructors derive the Main activation/opcode pins from row-shape
     equalities and prove the current bridge branches from the existing
     provider-row source-lane equalities.

   The same Binary provider-route shape now covers SUB, SUBW, and ADDIW:

   - the staged Aeneas harness proves that SUB lowers to an external `OP_SUB`
     row, SUBW lowers to an external `OP_SUB_W` row, and ADDIW lowers to an
     external `OP_ADD_W` row;
   - main Lake proves `MainRowProvenance.subPins_of_extracted_shape` and
     `MainRowProvenance.subwPins_of_extracted_shape`;
   - main Lake extends `OpEnvelope.aeneasBridgeTrust` with the corresponding
     source-lane predicates and exposes `OpEnvelope.subOfExtractedShape`,
     `OpEnvelope.subwOfExtractedShape`, and `OpEnvelope.addiwOfExtractedShape`
     plus matching bridge theorems.

   The R-type Binary logic/comparison provider-route shape now covers AND, OR,
   XOR, SLT, and SLTU:

   - the staged Aeneas harness proves that AND lowers to external `OP_AND`, OR
     lowers to external `OP_OR`, XOR lowers to external `OP_XOR`, SLT lowers
     to external `OP_LT`, and SLTU lowers to external `OP_LTU`;
   - main Lake proves `MainRowProvenance.andPins_of_extracted_shape`,
     `MainRowProvenance.orPins_of_extracted_shape`,
     `MainRowProvenance.xorPins_of_extracted_shape`,
     `MainRowProvenance.ltPins_of_extracted_shape`, and
     `MainRowProvenance.ltuPins_of_extracted_shape`;
   - main Lake extends `OpEnvelope.aeneasBridgeTrust` with the corresponding
     source-lane predicates and exposes `OpEnvelope.andOfExtractedShape`,
     `OpEnvelope.orOfExtractedShape`, `OpEnvelope.xorOfExtractedShape`,
     `OpEnvelope.sltOfExtractedShape`, and
     `OpEnvelope.sltuOfExtractedShape` plus matching bridge theorems.

   The I-type logic/comparison immediates complete that Binary group:

   - the staged Aeneas harness proves that ANDI, ORI, XORI, SLTI, and SLTIU use
     the same external Binary opcodes as the R-type forms, with the second
     source lane supplied by the sign-extended immediate row shape;
   - main Lake reuses the same extracted opcode pin helpers and exposes
     `OpEnvelope.andiOfExtractedShape`, `OpEnvelope.oriOfExtractedShape`,
     `OpEnvelope.xoriOfExtractedShape`, `OpEnvelope.sltiOfExtractedShape`, and
     `OpEnvelope.sltiuOfExtractedShape` plus matching bridge theorems;
   - SLTI and SLTIU additionally derive the `m.m32 r_main = 0` envelope field
     from extracted `m32 = false` row-shape provenance.

   The BinaryExtension shift provider-route group begins with SLL, SRL, and
   SRA:

   - the staged Aeneas harness proves that SLL, SRL, and SRA lower to external
     `OP_SLL`, `OP_SRL`, and `OP_SRA` rows;
   - main Lake proves `MainRowProvenance.sllPins_of_extracted_shape`,
     `MainRowProvenance.srlPins_of_extracted_shape`, and
     `MainRowProvenance.sraPins_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.sllOfExtractedShape`,
     `OpEnvelope.srlOfExtractedShape`, and `OpEnvelope.sraOfExtractedShape`
     plus matching bridge theorems for `rowA64` and `rowShiftAmount`.

   The immediate 64-bit shift forms SLLI, SRLI, and SRAI reuse that
   BinaryExtension route:

   - the staged Aeneas harness proves that SLLI, SRLI, and SRAI lower to the
     same external `OP_SLL`, `OP_SRL`, and `OP_SRA` provider rows, but with an
     immediate shift source row shape;
   - main Lake reuses the same extracted opcode pin helpers and exposes
     `OpEnvelope.slliOfExtractedShape`, `OpEnvelope.srliOfExtractedShape`, and
     `OpEnvelope.sraiOfExtractedShape`;
   - the matching bridge theorems prove the immediate shift predicates by
     connecting `r1_val` to `rowA64` and `shamt.toNat` to `rowShiftAmount`.

   The R-type W shift forms SLLW, SRLW, and SRAW are the 32-bit counterpart:

   - the staged Aeneas harness proves that SLLW, SRLW, and SRAW lower to
     external `OP_SLL_W`, `OP_SRL_W`, and `OP_SRA_W` rows with `m32 = true`;
   - main Lake proves `MainRowProvenance.sllwPins_of_extracted_shape`,
     `MainRowProvenance.srlwPins_of_extracted_shape`, and
     `MainRowProvenance.srawPins_of_extracted_shape`;
   - main Lake exposes `OpEnvelope.sllwOfExtractedShape`,
     `OpEnvelope.srlwOfExtractedShape`, and `OpEnvelope.srawOfExtractedShape`,
     whose bridge theorems connect low-32-bit `r1_val` to `rowA32` and
     `r2_val % 32` to `rowShiftAmount32`.

   SLLIW, SRLIW, and SRAIW finish the BinaryExtension W-shift group:

   - the staged Aeneas harness proves that the immediate W shift forms use the
     same external W opcodes with immediate-source row shape;
   - main Lake reuses the W opcode pin helpers and exposes
     `OpEnvelope.slliwOfExtractedShape`, `OpEnvelope.srliwOfExtractedShape`,
     and `OpEnvelope.sraiwOfExtractedShape`;
   - the bridge theorems connect low-32-bit `r1_val` to `rowA32` and
     `shamt.toNat` to `rowShiftAmount32`.

   SB, SH, SW, and SD start the Main-only store family:

   - the staged Aeneas harness proves that each store lowers to internal
     `OP_COPYB` with register/register address/value sources, indirect store
     mode, `store_pc = false`, and width `1`, `2`, `4`, or `8`; the concrete
     full-row checks also record that `store_offset` carries the sample
     immediate;
   - main Lake exposes store provenance helpers for `OP_COPYB` pins,
     `ind_width`, and `store_pc = 0`;
   - main Lake exposes `OpEnvelope.sbOfExtractedShape`,
     `OpEnvelope.shOfExtractedShape`, `OpEnvelope.swOfExtractedShape`, and
     `OpEnvelope.sdOfExtractedShape`, whose bridge theorems prove the current
     store payload from derived width plus the existing store-value lane
     witnesses.

   LD, LBU, LHU, and LWU cover the zero-extension Main/Mem load route:

   - the staged Aeneas harness proves that each load lowers to internal
     `OP_COPYB` with register/immediate address sources, load destination
     routing (`bSrc = 5`), `store_pc = false`, and width `8`, `1`, `2`, or
     `4`; the concrete full-row checks also record that the sample immediate is
     carried in `bOffsetImm0`;
   - main Lake reuses the store-slice `OP_COPYB`, `ind_width`, and Clean
     `store_pc = 0` provenance helpers;
   - main Lake exposes `OpEnvelope.ldOfExtractedShape`,
     `OpEnvelope.lbuOfExtractedShape`, `OpEnvelope.lhuOfExtractedShape`, and
     `OpEnvelope.lwuOfExtractedShape`, whose bridge theorems prove the current
     zero-extension load predicates from derived width. Signed LB, LH, and LW
     lower to external sign-extension opcodes and remain a separate provider
     slice.

   LB, LH, and LW now cover that signed-load provider route:

   - the staged Aeneas harness proves that the signed loads lower to external
     `OP_SIGNEXTEND_B`, `OP_SIGNEXTEND_H`, and `OP_SIGNEXTEND_W` rows with the
     same load address/destination routing as the zero-extension load group and
     widths `1`, `2`, and `4`;
   - main Lake exposes sign-extension Main pin helpers for the extracted
     opcodes and reuses the existing width and Clean `store_pc = 0` helpers;
   - main Lake exposes `OpEnvelope.lbOfExtractedShape`,
     `OpEnvelope.lhOfExtractedShape`, and `OpEnvelope.lwOfExtractedShape`.
     Their bridge theorems prove the current signed-load predicates from
     derived width while the BinaryExtension static lookup/match witnesses
     remain explicit dynamic provider facts.

   BEQ, BNE, BLT, BGE, BLTU, and BGEU now cover the branch route:

   - the staged Aeneas harness proves that branches lower to external
     `OP_EQ`, `OP_LT`, or `OP_LTU` rows with register/register source routing,
     no store, `m32 = 0`, `set_pc = 0`, and `store_pc = 0`;
   - the same checks record the production lowerer's polarity split:
     BEQ/BLT/BLTU use `jmp_offset2 = 4`, while BNE/BGE/BGEU are negated and
     use `jmp_offset1 = 4`;
   - main Lake exposes branch Main pin/control/fall-through helpers plus
     `OpEnvelope.beqOfExtractedShape`, `OpEnvelope.bneOfExtractedShape`,
     `OpEnvelope.bltOfExtractedShape`, `OpEnvelope.bgeOfExtractedShape`,
     `OpEnvelope.bltuOfExtractedShape`, and
     `OpEnvelope.bgeuOfExtractedShape`. Their bridge theorems prove the
     current branch predicates from derived opcode/control/fall-through facts.
     Dynamic branch immediates remain outside this slice because branch
     `OpEnvelope` arms do not yet carry a Main-row provenance field.

   MUL, MULH, MULHU, MULHSU, and MULW start the ArithMul provider route:

   - the staged Aeneas harness proves that the MUL family lowers to external
     ArithMul rows with register/register source routing, register destination
     store, no PC controls, and fall-through jump offsets;
   - the checks record the concrete opcode split: `OP_MUL`, `OP_MULH`,
     `OP_MULUH`, `OP_MULSUH`, and `OP_MUL_W`, with `m32 = true` only for
     MULW;
   - main Lake exposes MUL-family Main pin/control helpers plus
     `OpEnvelope.mulOfExtractedShape`, `OpEnvelope.mulhOfExtractedShape`,
     `OpEnvelope.mulhuOfExtractedShape`,
     `OpEnvelope.mulhsuOfExtractedShape`, and
     `OpEnvelope.mulwOfExtractedShape`. Their bridge theorems prove the
     current ArithMul predicates from derived Main facts while provider-table,
     operation-bus, memory, range, and operand-lane facts remain explicit
     dynamic ArithMul obligations.

4. **Prove constructor-specific envelope evidence lemmas.**

   For each selected opcode, prove a theorem of the form:

   ```text
   extracted decoder/lowerer facts
     + extracted AIR row facts
     + bus/provider facts
     -> required OpEnvelope evidence for this constructor
   ```

   These lemmas should replace caller-supplied bridge facts one group at a time.

5. **Expand by opcode family.**

   After the initial slice works, expand in this order:

   - U/J/control-flow cases: LUI, AUIPC, JAL, JALR, FENCE
   - BinaryAdd/BinaryAddW: ADD, ADDI, ADDW, SUBW, ADDIW
   - Binary and BinaryExtension ALU/shift families
   - load/store families
   - Mul/Div/Rem families

   The expansion should be tracked by shrinking caller-burden categories, not by
   local proof churn alone.

6. **Retire the temporary trust axiom.**

   When the generated/proved evidence covers every soundness-relevant envelope
   field, remove the temporary `OpEnvelope` evidence trust axiom from the global
   closure. Narrow or remove `aeneas_bridge_trust` at the same time.

## Expected Trust-Ledger Evolution

Short term, the trust ledger gets larger but more honest:

```text
global closure includes a broad named OpEnvelope evidence trust boundary
```

Long term, the trust ledger should shrink:

```text
temporary OpEnvelope evidence axiom removed
aeneas_bridge_trust removed or narrowed
caller-burden bridge/row_shape/bus_shape/promises categories reduced
```

The desired end state is that the global theorem closure contains only stable
external assumptions, such as extraction trust, memory/bus soundness boundaries,
and explicitly scoped platform assumptions.

## OpenVM-FV Parity Target

OpenVM FV's theorem boundary is closer to:

```text
valid extracted AIR row
  + extracted constraints
  + explicit bus axioms / well-formedness assumptions
  -> Sail-equivalent bus effect
```

Closing the `OpEnvelope` gap should move zisk-fv toward that shape. Full parity
requires more than removing `OpEnvelope` caller burden: zisk-fv should also make
its remaining bus, memory, lookup/permutation, and extraction assumptions as
uniform and explicit as OpenVM FV's `axiomsPerRow` /
`wf_propertiesToAssumePerRow` boundary.

## Acceptance Criteria

- The global theorem no longer depends on caller-supplied opcode-specific
  `OpEnvelope` bridge facts.
- `bridge`, `row_shape`, `bus_shape`, and `promises` caller-burden categories
  shrink to zero, or to explicitly scoped inputs that are documented as
  non-soundness or external-boundary assumptions.
- The global axiom closure no longer contains a broad temporary `OpEnvelope`
  evidence trust axiom.
- Remaining trust classes are stable, named, and comparable to OpenVM FV's
  extracted-row plus explicit bus/memory assumption boundary.

## Verification Commands

For docs-only edits:

```bash
rg "OpEnvelope|aeneas_bridge_trust|caller-burden|OpenVM" \
  docs/extraction/op-envelope-gap-plan.md
```

For implementation milestones that change Lean or trust ledgers:

```bash
lake build ZiskFv.Compliance
trust/scripts/regenerate.sh
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
```
