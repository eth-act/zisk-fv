import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution
import ZiskFv.RV64D.divw  -- for to_bits_truncate_32_eq_ofInt_divw

open LeanRV64D.Functions

/-!
## RV64M REMW — pure spec + Sail equivalence (Track J4)

REMW is the signed 32-bit remainder. Per `riscv2zisk_context.rs:250`,
RV64 `remw` transpiles via `create_register_op(..., "div_w", 4)`,
op = OP_DIV_W = 0xbe = 190, m32 = 1, sa = sb = 1 (signed).

Sail (`InstsEnd.lean:65921`): `execute_REMW (...) (is_unsigned :=
false)` — signed truncated remainder of low 32 bits, sign-extended
to 64 bits. Special cases per RV64 spec:
  - rs2 = 0           → rs1 (low 32 bits)
  - rs1 = INT32_MIN, rs2 = -1 → 0 (signed overflow, remainder is 0)

Note: REMW does NOT have an explicit overflow patch in the Sail
body. `Int.tmod (-2^31) (-1) = 0` natively, and 0 fits in 32 bits.

Phase 6 Track R: equivalence is now *proved* using the
`execute_REMW'` refactor in `Fundamentals/Execution.lean`. No
remaining axioms.

The proof reuses helpers from `divw.lean`:
- `to_bits_truncate_32_eq_ofInt_divw` (renamed for clarity below)
- `tdiv_le_two_pow_31_of_bounds` (not strictly needed — REMW has
  no overflow patch — but kept for symmetry).
-/

namespace PureSpec

  structure RemwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure RemwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- REMW pure spec. Lower 32 bits of `r1`, `r2` interpreted as
      signed 2-complement; truncated remainder; sign-extend
      32-bit remainder to 64 bits.

      Per RV64 spec:
        - rs2 = 0: result is `rs1` (low 32 bits).
        - rs1 = INT32_MIN ∧ rs2 = -1: result is 0
          (signed overflow case has zero remainder).
        - Otherwise: `Int.tmod r1.toInt r2.toInt`. -/
  def execute_DIVREM_remw_pure (input : RemwInput) : RemwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let q32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then r1_lo32
        else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
          then 0#32
          else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
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

  set_option maxHeartbeats 800000 in
  lemma execute_DIVREM_remw_pure_equiv
      (remw_input : RemwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok remw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok remw_input.r2_val state)
      (h_input_rd : remw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))
      ) state =
      let remw_output := execute_DIVREM_remw_pure remw_input
      (do
        Sail.writeReg Register.nextPC remw_output.nextPC
        match remw_output.rd with
          | .some (rd, rd_val) => write_xreg rd rd_val
          | .none => pure ()
        pure (ExecutionResult.Retire_Success ())
      ) state := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_REMW'
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
    -- Generalize the lo32 extracts to match the goal's BitVec ((31-0)+1) width.
    generalize hr1_eq : Sail.BitVec.extractLsb remw_input.r1_val 31 0 = r1_lo32
    generalize hr2_eq : Sail.BitVec.extractLsb remw_input.r2_val 31 0 = r2_lo32
    -- Bridge the inner-integer expression to the pure-spec 3-branch form.
    -- For REMW, the Sail body has NO overflow patch — `Int.tmod (-2^31) (-1) = 0`
    -- already fits in 32 bits.
    -- The early `simp` unfolds `Int.tmod` via `Int.tmod_eq_emod` into the
    -- expression `a % b - if (0 ≤ a ∨ b ∣ a) then 0 else |b|`. We re-fold it.
    have h_inner_eq :
      BitVec.signExtend 64 (to_bits_truncate (l := 32)
        (if r2_lo32.toInt = 0
          then r1_lo32.toInt
          else r1_lo32.toInt % r2_lo32.toInt -
            (if 0 ≤ r1_lo32.toInt ∨ r2_lo32.toInt ∣ r1_lo32.toInt then 0
             else |r2_lo32.toInt|))) =
      BitVec.signExtend 64 (
        if r2_lo32 = 0#32
          then r1_lo32
          else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
            then 0#32
            else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)) := by
      -- Refold `Int.tmod` so we can reuse `to_bits_truncate_32_eq_ofInt_divw`.
      have h_tmod_unfold :
          r1_lo32.toInt % r2_lo32.toInt -
            (if 0 ≤ r1_lo32.toInt ∨ r2_lo32.toInt ∣ r1_lo32.toInt then 0
             else |r2_lo32.toInt|) =
          Int.tmod r1_lo32.toInt r2_lo32.toInt := by
        rw [Int.tmod_eq_emod]
        congr 1
        split_ifs
        · rfl
        · exact Int.abs_eq_natAbs _
      rw [h_tmod_unfold]
      rw [to_bits_truncate_32_eq_ofInt_divw]
      congr 1
      have h_toInt_zero_iff : r2_lo32.toInt = 0 ↔ r2_lo32 = 0#32 := by
        constructor
        · intro h
          have hbv := (BitVec.ofInt_toInt (x := r2_lo32)).symm
          rw [h] at hbv; rw [hbv]; decide
        · intro h; rw [h]; decide
      by_cases hb : r2_lo32 = 0#32
      · have hb_int : r2_lo32.toInt = 0 := h_toInt_zero_iff.mpr hb
        rw [if_pos hb_int, if_pos hb]
        exact BitVec.ofInt_toInt
      · have hb_int : r2_lo32.toInt ≠ 0 := fun h => hb (h_toInt_zero_iff.mp h)
        rw [if_neg hb_int, if_neg hb]
        by_cases hov :
          r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
        · -- Overflow case: tmod(-2^31, -1) = 0
          rw [if_pos hov]
          obtain ⟨hr1, hr2⟩ := hov
          have hr1_int : r1_lo32.toInt = -(2^31 : ℤ) := by rw [hr1]; decide
          have hr2_int : r2_lo32.toInt = -1 := by rw [hr2]; decide
          rw [hr1_int, hr2_int]
          have h_tmod : Int.tmod (-(2^31 : ℤ)) (-1) = 0 := by decide
          rw [h_tmod]
          decide
        · rw [if_neg hov]
    rw [h_inner_eq]
    -- Substitute back to the original Sail.BitVec.extractLsb form.
    subst hr1_eq
    subst hr2_eq
    -- Now resume with the rd-write cases.
    simp only [execute_DIVREM_remw_pure]
    -- Clear leftover hypotheses to prevent simp loops.
    clear h_inner_eq h_bmod_to_toInt h_input_pc
    obtain ⟨rd⟩ := rd
    by_cases h_zero : rd = 0
    · rewrite [h_zero, wX_write_xreg_zero_equiv]
      -- (Bare `simp` loops here on the unfolded `Int.tmod` form. We can skip
      -- this simp call since the `dite_cond_eq_true` rewrite below works
      -- without it.)
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
      simp only [regidx_to_fin]
      rewrite [dite_cond_eq_false]
      · simp only [h_input_rd, regidx_to_fin]
      · simp only [regidx_to_fin] at *
        have h_rd_ne : rd.toNat ≠ 0 := by
          intro h; apply h_zero; apply BitVec.eq_of_toNat_eq; simp [h]
        -- Goal: (remw_input.rd = 0) = False
        rw [h_input_rd]
        simp only [eq_iff_iff, iff_false]
        intro h_eq
        -- h_eq: ⟨rd.toNat, _⟩ = (0 : Fin 32). Extract rd.toNat = 0.
        apply h_rd_ne
        have := Fin.mk_eq_zero.mp h_eq
        exact this

end PureSpec
