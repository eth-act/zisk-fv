import ZiskFv.Compliance.OpEnvelope

/-!
# Known-defect predicates for the global compliance theorem

This module records the Lean side of `trust/defects.md`. A defect
predicate is not a trusted fact: it is a visible exclusion on a theorem
whose claim is "compliance outside known defect regions".

The predicates below are deliberately conservative while the exact bad
witness shapes are still being triaged. Retiring a defect should shrink
`Blocks`; it should not add an axiom.
-/

namespace ZiskFv.Compliance.Defects

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- Stable identifiers for entries in `trust/defects.md`. -/
inductive DefectId where
  | arithMulSignedWitnessSoundness
  | arithDivDynamicWitnessSoundness
  | fenceIncomplete
  deriving DecidableEq, Repr

/-- Register-zero shape used by ZisK's currently accepted FENCE subset. -/
def IsX0Reg : regidx → Prop
  | regidx.Regidx r => r = 0#5

/-- Current modeled FENCE subset accepted by ZisK's production decoder.

The extracted decoder rejects generic FENCE encodings with a nonzero `fm`,
`rs1`, or `rd` field. The known-bug gate therefore keeps only the known-good
FENCE shape in the global theorem surface while completeness is being
triaged. Non-FENCE envelopes are unaffected by this predicate. -/
def FenceKnownGoodShape
    : OpEnvelope state m r_main → Prop
  | .fence _ fm _ _ rs rd _ _ _ =>
      fm = 0#4 ∧ IsX0Reg rs ∧ IsX0Reg rd
  | _ => True

/-- Marker for the malicious signed-MUL witness shape.

For `MUL` (low-64 product) the exclusion is now **narrowed to the exact
genuine forge**: the exceptional product-sign rows that the shared 74-row
ArithTable admits for op `180`.  `ZiskFv.AirsClean.ArithTableProjections.Mul.`
`mul_np_xor_or_zero_product_shape` proves that every lookup-aware MUL row has
`np = na XOR nb` (the honest signed product-sign witness) **or** one of the two
exceptional shapes `(na = 1, nb = 0, np = 0)` / `(na = 0, nb = 1, np = 0)`.
Those exceptional shapes pin `np = 0` while `na XOR nb = 1`, which breaks the
low-half carry-chain identity `(A - na·2^64)(B - nb·2^64) ≡ A·B (mod 2^64)`
that the honest proof relies on; this is the witness a malicious prover uses to
forge e.g. `MUL(-1, 1) = 1`.  An honest MUL row (where `np = na XOR nb`) is
**not** in this shape, so the narrowed predicate is satisfiable-free precisely
on honest rows — the canonical `equiv_MUL` is non-vacuous under
`¬ MaliciousSignedMulWitnessShape`.

`MULH` / `MULHSU` (the high-half signed products) remain opcode-wide `True`:
their high-half correctness needs a dynamic carry/range proof that has not yet
been done, so they stay conservatively blocked. Narrowing them is the next
step of the signed-M retirement. -/
def MaliciousSignedMulWitnessShape
    : OpEnvelope state m r_main → Prop
  | .mul _ _ _ _ _ _ _ v r_a .. =>
      (v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)
  | .mulh .. => True
  | .mulhsu .. => True
  | _ => False

/-- Conservative marker for remaining dynamic DIV/REM witness facts.

The retired `arith_table_op_*` and `arith_div_*` assumptions were not pure
finite-table projections: they connected row selectors to concrete operand
chunks, sign witnesses, and remainder bounds. The unsigned `DIVU`/`REMU` and
`DIVUW`/`REMUW` paths now derive these facts from row/range/operation-bus
evidence; the remaining signed arms stay excluded until their extra sign and
overflow/div-by-zero facts are proved. -/
def ArithDivDynamicWitnessShape
    : OpEnvelope state m r_main → Prop
  | .div .. => True
  | .divw .. => True
  | .rem .. => True
  | .remw .. => True
  | _ => False

/-- `Blocks id env` means defect `id` excludes this envelope from the
    defect-qualified compliance theorem. -/
def Blocks (id : DefectId) (env : OpEnvelope state m r_main) : Prop :=
  match id with
  | .arithMulSignedWitnessSoundness =>
      MaliciousSignedMulWitnessShape env
  | .arithDivDynamicWitnessSoundness =>
      ArithDivDynamicWitnessShape env
  | .fenceIncomplete =>
      ¬ FenceKnownGoodShape env

/-- Public theorem-side hypothesis: this envelope is outside every known
    defect region. -/
def NoKnownDefect (env : OpEnvelope state m r_main) : Prop :=
  ∀ id, ¬ Blocks id env

theorem fence_known_good_shape_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    FenceKnownGoodShape env := by
  by_contra h_not
  exact h_known_bugs .fenceIncomplete h_not

theorem no_malicious_signed_mul_witness_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    ¬ MaliciousSignedMulWitnessShape env :=
  h_known_bugs .arithMulSignedWitnessSoundness

theorem no_arith_div_dynamic_witness_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    ¬ ArithDivDynamicWitnessShape env :=
  h_known_bugs .arithDivDynamicWitnessSoundness

/-- **Non-vacuity / constructibility witness for the narrowed MUL exclusion.**

An HONEST MUL envelope — one whose ArithMul row has `np = na XOR nb` in the
simplest non-negative form `na = nb = np = 0` (both operands non-negative, e.g.
`MUL(2, 3)`) — is NOT in `MaliciousSignedMulWitnessShape`.  Hence
`¬ MaliciousSignedMulWitnessShape` (the `h_not_forge` hypothesis of the canonical
`ZiskFv.Equivalence.Mul.equiv_MUL`) IS satisfiable, so the canonical theorem is
non-vacuous: it discharges a reachable honest case, not an empty one.  This is
the Lean-checked anti-vacuity guard for the `MUL` arm of
`ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`. -/
theorem honest_mul_witness_not_malicious
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_MUL)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    (h_honest : v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0) :
    ¬ MaliciousSignedMulWitnessShape
        (OpEnvelope.mul mul_input r1 r2 rd srs1 srs2 bus v r_a pins
          h_match_primary promises arith_mem bounds h_row_constraints arith_table
          arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value) := by
  obtain ⟨ha, hb, _hp⟩ := h_honest
  rintro (⟨ha1, _, _⟩ | ⟨_, hb1, _⟩)
  · rw [ha] at ha1; exact absurd ha1 (by decide)
  · rw [hb] at hb1; exact absurd hb1 (by decide)

end ZiskFv.Compliance.Defects
