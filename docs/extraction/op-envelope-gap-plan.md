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
