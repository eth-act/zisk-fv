import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

open LeanRV64D.Functions

/-!
## RV64M DIVW — pure spec + Sail equivalence (Track J4)

DIVW is the signed 32-bit divide. Per `riscv2zisk_context.rs:250`,
RV64 `divw` transpiles via `create_register_op(..., "div_w", 4)`,
op = OP_DIV_W = 0xbe = 190, m32 = 1, sa = sb = 1 (signed).

Sail (`InstsEnd.lean:69371`): `execute_DIVW (...) (is_unsigned :=
false)` — signed truncated division of low 32 bits, sign-extended
to 64 bits. Special cases per RV64 spec:
  - rs2 = 0           → -1 (all bits set)
  - rs1 = INT32_MIN, rs2 = -1 → INT32_MIN (signed overflow)

Phase 6 Track R: equivalence is now *proved* using the
`execute_DIVW'` refactor in `Fundamentals/Execution.lean`. No
remaining axioms.
-/

namespace PureSpec

  structure DivwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure DivwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- DIVW pure spec. Lower 32 bits of `r1`, `r2` interpreted as
      signed 2-complement; truncated division (rounds toward 0);
      sign-extend 32-bit quotient to 64 bits.

      Special cases per RV64 spec:
        - rs2 = 0: result is -1 (all-ones).
        - rs1 = INT32_MIN ∧ rs2 = -1: result is INT32_MIN
          (signed overflow; native `tdiv` would yield 2^31, which
          doesn't fit in signed 32-bit). -/
  def execute_DIVREM_divw_pure (input : DivwInput) : DivwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let q32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then BitVec.allOnes 32
        else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
          then BitVec.ofNat 32 (2^31)
          else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
    let q64 : BitVec 64 := BitVec.signExtend 64 q32
    {
      nextPC := input.PC + 4#64
      rd := if h: input.rd = 0
        then .none
        else .some (
          ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
          q64
        )
    }

  /-- Helper: `to_bits_truncate (l := 32) z = BitVec.ofInt 32 z` for any `z : ℤ`. -/
  lemma to_bits_truncate_32_eq_ofInt_divw (z : ℤ) :
      to_bits_truncate (l := 32) z = BitVec.ofInt 32 z := by
    apply BitVec.eq_of_toNat_eq
    simp only [to_bits_truncate, Sail.get_slice_int, BitVec.extractLsb'_toNat,
               BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.zero_add]
    have h33 : ((2 : ℕ) ^ (0 + 32 + 1) : ℤ) = 8589934592 := by norm_num
    have h32_int : ((2 : ℕ) ^ 32 : ℤ) = 4294967296 := by norm_num
    have h32n : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
    omega

  /-- For 32-bit signed values `a, b`, `a.tdiv b ≤ 2^31`. -/
  lemma tdiv_le_two_pow_31_of_bounds
      {a b : ℤ}
      (ha_lo : -(2^31 : ℤ) ≤ a) (ha_hi : a < (2^31 : ℤ)) :
      Int.tdiv a b ≤ (2 : ℤ) ^ 31 := by
    -- |a| ≤ 2^31 and |a.tdiv b| ≤ |a|.
    have h_abs_a : |a| ≤ (2 : ℤ) ^ 31 := by
      rcases le_or_gt 0 a with hp | hn
      · rw [abs_of_nonneg hp]; linarith
      · rw [abs_of_neg hn]; linarith
    have h_abs_a_natAbs : (a.natAbs : ℤ) ≤ 2^31 := by
      rw [← Int.abs_eq_natAbs a]; exact h_abs_a
    have h_natAbs_le : (a.tdiv b).natAbs ≤ a.natAbs := Int.natAbs_tdiv_le_natAbs _ _
    have h_le_natAbs : (a.tdiv b) ≤ (a.tdiv b).natAbs := Int.le_natAbs
    have h2 : ((a.tdiv b).natAbs : ℤ) ≤ a.natAbs := by exact_mod_cast h_natAbs_le
    linarith

  /-- For any q ≤ 2^31, `BitVec.ofInt 32 (if 2^31 ≤ q then -2^31 else q) = BitVec.ofInt 32 q`.
      The point: the only `q ≥ 2^31` we can hit (given the bound) is `q = 2^31`,
      and `2^31 ≡ -2^31 (mod 2^32)`. -/
  lemma BitVec_ofInt_overflow_collapse {q : ℤ} (hle : q ≤ (2 : ℤ) ^ 31) :
      BitVec.ofInt 32 (if (2 : ℤ) ^ 31 ≤ q then -(2 : ℤ) ^ 31 else q) =
      BitVec.ofInt 32 q := by
    split_ifs with hge
    · -- 2^31 ≤ q ≤ 2^31, so q = 2^31; -2^31 ≡ 2^31 mod 2^32
      have hq_eq : q = (2 : ℤ) ^ 31 := le_antisymm hle hge
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, hq_eq]
      decide
    · rfl

  /-- Variant of `BitVec_ofInt_overflow_collapse` using LeanRV64D's `^i`
      (HPow Int Int Int) operator, which is what the Sail-generated body uses. -/
  lemma BitVec_ofInt_overflow_collapse_i {q : ℤ} (hle : q ≤ (2 : ℤ) ^i (31 : ℤ)) :
      BitVec.ofInt 32 (if (2 : ℤ) ^i (31 : ℤ) ≤ q then -((2 : ℤ) ^i (31 : ℤ)) else q) =
      BitVec.ofInt 32 q := by
    have h_pow_eq : (2 : ℤ) ^i (31 : ℤ) = (2 : ℤ) ^ 31 := by
      show (2 : ℤ) ^ ((31 : ℤ).toNat) = (2 : ℤ) ^ 31
      rfl
    rw [h_pow_eq] at hle ⊢
    exact BitVec_ofInt_overflow_collapse hle

  set_option maxHeartbeats 800000 in
  lemma execute_DIVREM_divw_pure_equiv
      (divw_input : DivwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok divw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok divw_input.r2_val state)
      (h_input_rd : divw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some divw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))
      ) state =
      let divw_output := execute_DIVREM_divw_pure divw_input
      (do
        Sail.writeReg Register.nextPC divw_output.nextPC
        match divw_output.rd with
          | .some (rd, rd_val) => write_xreg rd rd_val
          | .none => pure ()
        pure (ExecutionResult.Retire_Success ())
      ) state := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_DIVW'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    -- Bridge `(↑x.toNat).bmod 4294967296 = (extractLsb_or_self).toInt`.
    have h_bmod_to_toInt : ∀ v : BitVec 64,
        ((v.toNat : ℤ).bmod 4294967296) = (Sail.BitVec.extractLsb v 31 0).toInt := by
      intro v
      rw [BitVec.toInt_eq_toNat_bmod]
      have h_ext : (Sail.BitVec.extractLsb v 31 0).toNat = v.toNat % 4294967296 := by simp
      rw [h_ext]
      have h_pow_simp : (2 : ℕ) ^ (31 - 0 + 1) = 4294967296 := by norm_num
      rw [h_pow_simp]
      have h_cast : ((v.toNat % 4294967296 : ℕ) : ℤ) = (v.toNat : ℤ) % ((4294967296 : ℕ) : ℤ) := by
        push_cast; rfl
      rw [h_cast, Int.emod_bmod]
    -- Reduce EStateM match on Result.ok.
    simp only []
    -- Convert .bmod 4294967296 to .toInt of the lo32 extract.
    simp only [h_bmod_to_toInt]
    -- The LHS quotient expression becomes `if 2^31 ≤ q then -2^31 else q`
    -- where `q = if r2_lo32.toInt = 0 then -1 else r1_lo32.toInt.tdiv r2_lo32.toInt`.
    -- We bound q ≤ 2^31 and then collapse the overflow patch.
    -- IMPORTANT: do NOT use `set ... : BitVec 32` — that introduces a let-binding
    -- with unreduced width `(31-0)+1` and breaks `rw` pattern matching later.
    -- Use `generalize` to abstract the lo32 extracts. The generalized variables
    -- have type `BitVec ((31-0)+1)` exactly as in the goal.
    generalize hr1_eq : Sail.BitVec.extractLsb divw_input.r1_val 31 0 = r1_lo32
    generalize hr2_eq : Sail.BitVec.extractLsb divw_input.r2_val 31 0 = r2_lo32
    -- Now r1_lo32, r2_lo32 : BitVec ((31-0)+1), matching the goal exactly.
    have h_r1_lo : -(2^31 : ℤ) ≤ r1_lo32.toInt := by
      have := BitVec.le_toInt (w := (31 - 0 + 1)) r1_lo32; simpa using this
    have h_r1_hi : r1_lo32.toInt < (2^31 : ℤ) := by
      have := @BitVec.toInt_lt (31 - 0 + 1) r1_lo32; simpa using this
    -- Now bridge to pure spec form.
    -- IMPORTANT: the goal's `2 ^ 31` is the LeanRV64D `^i` (HPow Int Int Int),
    -- NOT the Mathlib `^` (HPow Int Nat Int). They compute the same value but
    -- are *different operators* — `rw` will not unify them. Match the goal's
    -- form by writing `(2 : ℤ) ^i (31 : ℤ)` in `h_inner_eq`.
    have h_inner_eq :
      BitVec.signExtend 64 (to_bits_truncate (l := 32)
        (if (2 : ℤ) ^i (31 : ℤ) ≤
            (if r2_lo32.toInt = 0 then (-1 : ℤ)
             else Int.tdiv r1_lo32.toInt r2_lo32.toInt)
          then -((2 : ℤ) ^i (31 : ℤ))
          else (if r2_lo32.toInt = 0 then (-1 : ℤ)
                else Int.tdiv r1_lo32.toInt r2_lo32.toInt))) =
      BitVec.signExtend 64 (
        if r2_lo32 = 0#32
          then BitVec.allOnes 32
          else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
            then BitVec.ofNat 32 (2^31)
            else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)) := by
      rw [to_bits_truncate_32_eq_ofInt_divw]
      congr 1
      -- Bridge for "r2_lo32 = 0" iff "r2_lo32.toInt = 0".
      have h_toInt_zero_iff : r2_lo32.toInt = 0 ↔ r2_lo32 = 0#32 := by
        constructor
        · intro h
          have hbv := (BitVec.ofInt_toInt (x := r2_lo32)).symm
          rw [h] at hbv; rw [hbv]; decide
        · intro h; rw [h]; decide
      -- The integer expression Q = if r2_lo32.toInt = 0 then -1 else tdiv.
      set Q : ℤ := if r2_lo32.toInt = 0 then -1 else Int.tdiv r1_lo32.toInt r2_lo32.toInt
        with hQ_def
      -- Bound Q ≤ 2^i 31. (The goal uses LeanRV64D's `^i` operator.)
      have h_pow_eq : (2 : ℤ) ^i (31 : ℤ) = (2 : ℤ) ^ 31 := by
        show (2 : ℤ) ^ ((31 : ℤ).toNat) = (2 : ℤ) ^ 31
        rfl
      have hQ_le : Q ≤ (2 : ℤ) ^i (31 : ℤ) := by
        rw [h_pow_eq, hQ_def]
        split_ifs with hz
        · norm_num
        · exact tdiv_le_two_pow_31_of_bounds h_r1_lo h_r1_hi
      -- Apply overflow collapse: BitVec.ofInt 32 of the LHS = BitVec.ofInt 32 Q.
      rw [BitVec_ofInt_overflow_collapse_i hQ_le]
      -- Now goal: BitVec.ofInt 32 Q = pure spec 3-branch form.
      rw [hQ_def]
      by_cases hb : r2_lo32 = 0#32
      · have hb_int : r2_lo32.toInt = 0 := h_toInt_zero_iff.mpr hb
        rw [if_pos hb_int, if_pos hb]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.allOnes]
      · have hb_int : r2_lo32.toInt ≠ 0 := fun h => hb (h_toInt_zero_iff.mp h)
        rw [if_neg hb_int, if_neg hb]
        by_cases hov :
          r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
        · -- Overflow case: r1.toInt = -2^31, r2.toInt = -1, tdiv = 2^31.
          rw [if_pos hov]
          obtain ⟨hr1, hr2⟩ := hov
          have hr1_int : r1_lo32.toInt = -(2^31 : ℤ) := by rw [hr1]; decide
          have hr2_int : r2_lo32.toInt = -1 := by rw [hr2]; decide
          rw [hr1_int, hr2_int]
          have h_tdiv : Int.tdiv (-(2^31 : ℤ)) (-1) = (2^31 : ℤ) := by decide
          rw [h_tdiv]
          apply BitVec.eq_of_toNat_eq
          decide
        · rw [if_neg hov]
    rw [h_inner_eq]
    -- Substitute r1_lo32, r2_lo32 back to their original Sail.BitVec.extractLsb form
    -- so they match the pure-spec RHS expressions.
    subst hr1_eq
    subst hr2_eq
    -- Now resume with the rd-write cases.
    simp only [execute_DIVREM_divw_pure]
    obtain ⟨rd⟩ := rd
    by_cases h_zero : rd = 0
    · rewrite [h_zero, wX_write_xreg_zero_equiv]
      simp
      rewrite [dite_cond_eq_true]
      · simp
      · simp [h_input_rd, h_zero, regidx_to_fin]
    · have h_inc := regidx_non_zero h_zero
      apply Finset.mem_Icc.mp at h_inc
      obtain ⟨h_low, h_high⟩ := h_inc
      rewrite [
        wX_write_xreg_non_zero_equiv _ _
          (regidx.Regidx rd)
          ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
          (by simp [regidx_to_fin])
      ]
      simp [regidx_to_fin]
      rewrite [dite_cond_eq_false]
      · simp [h_input_rd, regidx_to_fin]
      · simp [regidx_to_fin] at *
        omega

end PureSpec
