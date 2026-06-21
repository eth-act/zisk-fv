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
open ZiskFv.PackedBitVec.SignedChunkLift (toIntZ)

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

`MULH` / `MULHSU` (the high-half signed products) are now narrowed to the SAME
exact forge shape as `MUL`: the two exceptional product-sign rows the shared
ArithTable admits for op 181 / 179 (`Counterexamples.mulh_np_xor_not_static`,
`Counterexamples.mulhsu_np_xor_not_static`).  An honest high-half MUL row
(`np = na XOR nb`) is NOT in this shape, so the canonical `equiv_MULH` /
`equiv_MULHSU` are non-vacuous under `¬ MaliciousSignedMulWitnessShape`.  The
high-half proof additionally consumes the documented SIGN-RANGE RESIDUAL
(`na = MSB`, `nb = MSB`); see `trust/defects.md` (sign-range residual entry). -/
def MaliciousSignedMulWitnessShape
    : OpEnvelope state m r_main → Prop
  | .mul _ _ _ _ _ _ _ v r_a .. =>
      (v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)
  | .mulh _ _ _ _ _ v r_a .. =>
      (v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)
  | .mulhsu _ _ _ _ _ v r_a .. =>
      (v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)
  | _ => False

/-- The signed `DIV`/`REM` remainder integer value reconstructed from the
    circuit's `d[]` remainder chunks and the `nr` sign witness:
    `r = packed4(d) - nr·2^64`. -/
def signedRemainderInt (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ) : ℤ :=
  (ZiskFv.PackedBitVec.MulNoWrap.packed4
      (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
    - (v.nr r_a).val * (2:ℤ)^64

/-- W-mode (`DIVW`/`REMW`) signed remainder integer value, reconstructed from
    the low 32-bit remainder chunks and the `nr` sign witness:
    `r₃₂ = (d_0 + d_1·2^16) - nr·2^32`. -/
def signedRemainderIntW (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ) : ℤ :=
  ((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ) - (v.nr r_a).val * (2:ℤ)^32

/-- **Narrowed marker for the signed DIV/REM remainder-bound false positive.**

The retired `arith_table_op_*` and `arith_div_*` assumptions connected row
selectors to concrete operand chunks, sign witnesses, and remainder bounds.
The unsigned `DIVU`/`REMU` and `DIVUW`/`REMUW` paths derive these facts from
row/range/operation-bus evidence.

For the SIGNED arms the only residual unsoundness is the documented
`LT_ABS_NP` byte-chain false positive (`trust/defects.md`,
`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`, witnessed by
`ZiskFv.Airs.Binary.ltAbsNpByteChain_falsePositive_eqAbs256`): the per-byte
absolute-compare chain accepts a remainder whose magnitude *equals* the
divisor magnitude (`|r| = |op2|`) as though `|r| < |op2|`.  An HONEST signed
division ALWAYS has `|r| < |op2|` strictly (e.g. `x/x` has remainder `0`), so
this forge shape is never produced by a real trace.

The narrowed predicate is therefore EXACTLY the false-positive equality
`|remainder| = |divisor|` on the nonzero-divisor path.  Excluding it (via
`NoKnownDefect`) upgrades the in-model WEAK bound `|r| ≤ |op2|` (the most the
`LT_ABS_NP`/`LT_ABS_PN` chain can soundly witness) to the STRICT bound
`|r| < |op2|` that Sail DIV/REM requires on that path.  The architecturally
valid divisor-zero branch is handled separately by the ArithDiv boundary
constraints and is not a strict-remainder-bound obligation.  Honest rows are
NOT in this shape (anti-vacuity guards
`honest_{div,rem,divw,remw}_witness_not_forge`). -/
def ArithDivDynamicWitnessShape
    : OpEnvelope state m r_main → Prop
  | .div div_input _ _ _ _ v r_a .. =>
      div_input.r2_val.toInt ≠ 0
        ∧ (signedRemainderInt v r_a).natAbs = div_input.r2_val.toInt.natAbs
  | .rem rem_input _ _ _ _ v r_a .. =>
      rem_input.r2_val.toInt ≠ 0
        ∧ (signedRemainderInt v r_a).natAbs = rem_input.r2_val.toInt.natAbs
  -- W-mode (`DIVW`/`REMW`): narrowed to the EXACT `|r₃₂| = |op2₃₂|`
  -- false-positive shape, the W analogue of the `.div`/`.rem` narrowing.
  -- The `LT_ABS_NP`/`LT_ABS_PN` byte chain at 32-bit width accepts a
  -- remainder whose 32-bit magnitude EQUALS the divisor's 32-bit magnitude;
  -- excluding it on the nonzero-divisor path upgrades the WEAK in-model bound
  -- `|r₃₂| ≤ |op2₃₂|` to the STRICT bound that Sail DIVW/REMW require there.
  -- Honest W rows have `|r₃₂| < |op2₃₂|` strictly, so are never in this shape
  -- (anti-vacuity guards `honest_{divw,remw}_witness_not_forge`).
  | .divw divw_input _ _ _ _ v r_a .. =>
      Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32
        ∧ (signedRemainderIntW v r_a).natAbs
          = (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs
  | .remw remw_input _ _ _ _ v r_a .. =>
      Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32
        ∧ (signedRemainderIntW v r_a).natAbs
          = (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs
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

/-- **Non-vacuity / constructibility witness for the narrowed MULH exclusion.**

An HONEST MULH envelope — one whose ArithMul row has `np = na XOR nb` in the
simplest non-negative form `na = nb = np = 0` (both operands non-negative, e.g.
`MULH(2, 3)`) — is NOT in `MaliciousSignedMulWitnessShape`.  Hence
`¬ MaliciousSignedMulWitnessShape` (the `h_not_forge` hypothesis of the canonical
`equiv_MULH`) IS satisfiable, so the canonical theorem is non-vacuous.  This is
the Lean-checked anti-vacuity guard for the `MULH` arm of
`ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`. -/
theorem honest_mulh_witness_not_malicious
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_MULH)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0)
    (h_honest : v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0) :
    ¬ MaliciousSignedMulWitnessShape
        (OpEnvelope.mulh mulh_input r1 r2 rd bus v r_a pins
          h_match_secondary promises arith_mem bounds h_row_constraints arith_table
          arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value h_sign_a h_sign_b) := by
  obtain ⟨ha, hb, _hp⟩ := h_honest
  rintro (⟨ha1, _, _⟩ | ⟨_, hb1, _⟩)
  · rw [ha] at ha1; exact absurd ha1 (by decide)
  · rw [hb] at hb1; exact absurd hb1 (by decide)

/-- **Non-vacuity / constructibility witness for the narrowed MULHSU exclusion.**
    Companion of `honest_mulh_witness_not_malicious` for the signed × unsigned
    high half (the table pins `nb = 0`; an honest row has `na = np = 0`). -/
theorem honest_mulhsu_witness_not_malicious
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_MULSUH)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhsu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhsu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_honest : v.na r_a = 0 ∧ v.nb r_a = 0 ∧ v.np r_a = 0) :
    ¬ MaliciousSignedMulWitnessShape
        (OpEnvelope.mulhsu mulhsu_input r1 r2 rd bus v r_a pins
          h_match_secondary promises arith_mem bounds h_row_constraints arith_table
          arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value h_sign_a) := by
  obtain ⟨ha, hb, _hp⟩ := h_honest
  rintro (⟨ha1, _, _⟩ | ⟨_, hb1, _⟩)
  · rw [ha] at ha1; exact absurd ha1 (by decide)
  · rw [hb] at hb1; exact absurd hb1 (by decide)

/-- **Non-vacuity / constructibility witness for the narrowed DIV exclusion.**

An HONEST signed division always has a remainder STRICTLY smaller in magnitude
than the divisor (`|r| < |op2|`), e.g. `7 / 2 = 3 rem 1` with `|1| < |2|`, or any
`x / x` whose remainder is `0`.  Such a row has
`(signedRemainderInt v r_a).natAbs < div_input.r2_val.toInt.natAbs`, hence
`(signedRemainderInt v r_a).natAbs ≠ div_input.r2_val.toInt.natAbs`, so it is NOT
in `ArithDivDynamicWitnessShape`.  Therefore `NoKnownDefect` is satisfiable for an
honest DIV envelope — the narrowed defect excludes ONLY the malicious `|r| = |op2|`
false-positive forge, never an honest division.  This is the Lean-checked
anti-vacuity guard for the `DIV` arm of
`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`. -/
theorem honest_div_witness_not_forge
    {div_input : PureSpec.DivInput} {r1 r2 rd : regidx}
    {bus : ZiskFv.Compliance.BusRows}
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r_a : ℕ}
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_DIV)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary : ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a) - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      (signedRemainderInt v r_a).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ (signedRemainderInt v r_a) * div_input.r1_val.toInt)
    (h_honest_strict :
      (signedRemainderInt v r_a).natAbs < div_input.r2_val.toInt.natAbs) :
    ¬ ArithDivDynamicWitnessShape
        (OpEnvelope.div div_input r1 r2 rd bus v r_a pins h_match_primary promises
          arith_mem bounds h_no_overflow h_row_constraints h_boundary arith_table
          arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor
          h_nr_pin h_rs1_value h_rs2_value h_r_le h_r_sign) := by
  dsimp [ArithDivDynamicWitnessShape, signedRemainderInt]
  rintro ⟨_, h_eq⟩
  exact (Nat.ne_of_lt h_honest_strict) h_eq

/-- **Non-vacuity / constructibility witness for the narrowed REM exclusion.**
    Companion of `honest_div_witness_not_forge` for the remainder lane. -/
theorem honest_rem_witness_not_forge
    {rem_input : PureSpec.RemInput} {r1 r2 rd : regidx}
    {bus : ZiskFv.Compliance.BusRows}
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r_a : ℕ}
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_REM)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (rem_input.r1_val.toInt = -(2:ℤ)^63 ∧ rem_input.r2_val.toInt = -1))
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a) - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      rem_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      rem_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      (signedRemainderInt v r_a).natAbs ≤ rem_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ (signedRemainderInt v r_a) * rem_input.r1_val.toInt)
    (h_honest_strict :
      (signedRemainderInt v r_a).natAbs < rem_input.r2_val.toInt.natAbs) :
    ¬ ArithDivDynamicWitnessShape
        (OpEnvelope.rem rem_input r1 r2 rd bus v r_a pins h_match_secondary promises
          arith_mem bounds h_op2_ne h_no_overflow h_row_constraints arith_table
          arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor
          h_nr_pin h_rs1_value h_rs2_value h_r_le h_r_sign) := by
  dsimp [ArithDivDynamicWitnessShape, signedRemainderInt]
  rintro ⟨_, h_eq⟩
  exact (Nat.ne_of_lt h_honest_strict) h_eq

/-- **Non-vacuity / constructibility witness for the narrowed DIVW exclusion.**

An HONEST 32-bit signed division always has a remainder STRICTLY smaller in
magnitude than the divisor (`|r₃₂| < |op2₃₂|`), e.g. `7 / 2 = 3 rem 1` in 32-bit
with `|1| < |2|`.  Such a row has
`(signedRemainderIntW v r_a).natAbs < (extractLsb op2 31 0).toInt.natAbs`, hence
`≠`, so it is NOT in `ArithDivDynamicWitnessShape`.  The narrowed defect excludes
ONLY the malicious `|r₃₂| = |op2₃₂|` false-positive forge, never an honest DIVW.
Lean-checked anti-vacuity guard for the `DIVW` arm of
`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`. -/
theorem honest_divw_witness_not_forge
    {divw_input : PureSpec.DivwInput} {r1 r2 rd : regidx}
    {bus : ZiskFv.Compliance.BusRows}
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r_a : ℕ}
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_DIV_W)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary : ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a) - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ) - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ) - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt)
    (h_honest_strict :
      (signedRemainderIntW v r_a).natAbs
        < (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs) :
    ¬ ArithDivDynamicWitnessShape
        (OpEnvelope.divw divw_input r1 r2 rd bus v r_a pins h_match_primary promises
          arith_mem bounds h_row_constraints h_boundary arith_table arith_chunk_ranges arith_carry_ranges
          h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_m32 h_div
          h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice h_rs1_value h_rs2_value
          h_no_overflow h_r_le h_r_sign) := by
  dsimp [ArithDivDynamicWitnessShape]
  rintro ⟨_, h_eq⟩
  exact (Nat.ne_of_lt h_honest_strict) h_eq

/-- **Non-vacuity / constructibility witness for the narrowed REMW exclusion.**
    Companion of `honest_divw_witness_not_forge` for the W remainder lane. -/
theorem honest_remw_witness_not_forge
    {remw_input : PureSpec.RemwInput} {r1 r2 rd : regidx}
    {bus : ZiskFv.Compliance.BusRows}
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r_a : ℕ}
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_REM_W)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a) - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ) - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ) - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt)
    (h_honest_strict :
      (signedRemainderIntW v r_a).natAbs
        < (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs) :
    ¬ ArithDivDynamicWitnessShape
        (OpEnvelope.remw remw_input r1 r2 rd bus v r_a pins h_match_secondary promises
          arith_mem bounds h_row_constraints arith_table arith_chunk_ranges arith_carry_ranges
          h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_m32 h_div
          h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice h_rs1_value h_rs2_value
          h_op2_ne h_no_overflow_w h_r_le h_r_sign) := by
  dsimp [ArithDivDynamicWitnessShape]
  rintro ⟨_, h_eq⟩
  exact (Nat.ne_of_lt h_honest_strict) h_eq

end ZiskFv.Compliance.Defects
