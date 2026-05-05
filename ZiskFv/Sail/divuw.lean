import ZiskFv.Sail.Auxiliaries
import ZiskFv.Fundamentals.Execution

open LeanRV64D.Functions

/-!
## RV64M DIVUW — pure spec + Sail equivalence

DIVUW is the unsigned 32-bit divide. Per
`riscv2zisk_context.rs:251`, RV64 `divuw` transpiles via
`create_register_op(..., "divu_w", 4)`, emitting a single Arith-bus
row with `op = OP_DIVU_W = 0xbc = 188`, `m32 = 1`.

Per Sail (`InstsEnd.lean:69371`), `execute_DIVW (...) (is_unsigned :=
true)` extracts low 32 bits of `rs1`/`rs2`, treats them as unsigned,
divides (with `-1` on zero-divisor), then sign-extends the 32-bit
quotient to 64 bits (per RV64 spec for the *W variants).

The Sail equivalence is now *proved* (Phase 6 Track R) using the
`execute_DIVW'` refactor in `Fundamentals/Execution.lean`. No
remaining axioms.
-/

namespace PureSpec

  structure DivuwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure DivuwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- DIVUW pure spec. Lower 32 bits of `r1`, `r2` interpreted as
      unsigned; divide; sign-extend 32-bit quotient to 64 bits. -/
  def execute_DIVREM_divuw_pure (input : DivuwInput) : DivuwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let q32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then BitVec.allOnes 32
        else BitVec.ofNat 32 (r1_lo32.toNat / r2_lo32.toNat)
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
  lemma to_bits_truncate_32_eq_ofInt (z : ℤ) :
      to_bits_truncate (l := 32) z = BitVec.ofInt 32 z := by
    apply BitVec.eq_of_toNat_eq
    simp only [to_bits_truncate, Sail.get_slice_int, BitVec.extractLsb'_toNat,
               BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.zero_add]
    -- Goal: (z % (2^33 : ℕ)).toNat % 2^32 = (z % (2^32 : ℕ)).toNat
    have h33 : ((2 : ℕ) ^ (0 + 32 + 1) : ℤ) = 8589934592 := by norm_num
    have h32_int : ((2 : ℕ) ^ 32 : ℤ) = 4294967296 := by norm_num
    have h32n : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
    omega

  /-- Helper: the unsigned 32-bit divide (Sail form) equals the pure-spec form. -/
  lemma divuw_quotient_bridge (a b : BitVec 32) :
      to_bits_truncate (l := 32)
          (if (((Sail.BitVec.toNatInt b : ℤ) == 0) : Bool)
           then (Neg.neg 1 : ℤ)
           else (Int.tdiv (Sail.BitVec.toNatInt a) (Sail.BitVec.toNatInt b)))
        = (if b = 0#32 then BitVec.allOnes 32
           else BitVec.ofNat 32 (a.toNat / b.toNat)) := by
    rw [to_bits_truncate_32_eq_ofInt]
    by_cases hb : b = 0#32
    · -- b = 0 branch
      subst hb
      simp only [Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod,
                 Int.ofNat_zero, beq_self_eq_true, if_true, if_pos, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.allOnes]
    · -- b ≠ 0 branch
      have hb' : b.toNat ≠ 0 := by
        intro h; apply hb; apply BitVec.eq_of_toNat_eq; simp [h]
      have hbz : ((b.toNat : ℤ) ≠ 0) := by exact_mod_cast hb'
      simp only [Sail.BitVec.toNatInt, beq_iff_eq, Int.ofNat_eq_zero, hb',
                 if_false, ↓reduceIte]
      rw [if_neg hb]
      apply BitVec.eq_of_toNat_eq
      -- LHS: ((BitVec.ofInt 32 (Int.tdiv (a.toNat : ℤ) (b.toNat : ℤ))).toNat
      -- RHS: (BitVec.ofNat 32 (a.toNat / b.toNat)).toNat
      -- Both reduce to (a.toNat / b.toNat) % 2^32
      conv_lhs => simp [BitVec.toNat_ofInt, Int.natCast_tdiv_eq_ediv]
      conv_rhs => simp [BitVec.toNat_ofNat]
      push_cast
      omega

  set_option maxHeartbeats 800000 in
  lemma execute_DIVREM_divuw_pure_equiv
      (divuw_input : DivuwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok divuw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok divuw_input.r2_val state)
      (h_input_rd : divuw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some divuw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))
      ) state =
      let divuw_output := execute_DIVREM_divuw_pure divuw_input
      (do
        Sail.writeReg Register.nextPC divuw_output.nextPC
        match divuw_output.rd with
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
    -- After simp, the LHS quotient is `if r2.toNat % 2^32 = 0 then -1 else
    -- r1.toNat % 2^32 / (r2.toNat % 2^32)`, all as integers.  The RHS
    -- `execute_DIVREM_divuw_pure.q32` is `if extractLsb r2 = 0 then allOnes
    -- else BitVec.ofNat (extractLsb r1).toNat / (extractLsb r2).toNat`.
    -- They are equal after applying `to_bits_truncate` and `BitVec.signExtend`.
    simp only [execute_DIVREM_divuw_pure]
    -- Bridge the BitVec equality.  `Sail.BitVec.extractLsb v 31 0 = 0#32` iff
    -- `v.toNat % 2^32 = 0`.
    have h_extract_eq_zero : ∀ v : BitVec 64,
        (Sail.BitVec.extractLsb v 31 0 = 0#32) ↔ (v.toNat % 4294967296 = 0) := by
      intro v
      constructor
      · intro h; rw [← BitVec.toNat_inj] at h; simpa using h
      · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
    -- Bridge the bitvec inner expression
    have h_inner_eq :
      (BitVec.signExtend 64 (to_bits_truncate (l := 32)
        (if divuw_input.r2_val.toNat % 4294967296 = 0 then (-1 : ℤ)
         else (divuw_input.r1_val.toNat : ℤ) % 4294967296 /
              ((divuw_input.r2_val.toNat : ℤ) % 4294967296)))) =
      (BitVec.signExtend 64
        (if Sail.BitVec.extractLsb divuw_input.r2_val 31 0 = 0#32
         then BitVec.allOnes 32
         else BitVec.ofNat 32
           ((Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat /
            (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat))) := by
      rw [to_bits_truncate_32_eq_ofInt]
      congr 1
      by_cases hb : Sail.BitVec.extractLsb divuw_input.r2_val 31 0 = 0#32
      · have hb' : divuw_input.r2_val.toNat % 4294967296 = 0 := (h_extract_eq_zero _).mp hb
        rw [if_pos hb, if_pos hb']
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.allOnes]
      · have hb' : divuw_input.r2_val.toNat % 4294967296 ≠ 0 :=
          fun h => hb ((h_extract_eq_zero _).mpr h)
        rw [if_neg hb, if_neg hb']
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
        -- Goal: (↑r1.toNat % m / (↑r2.toNat % m) % m).toNat % 2^32 = r1.toNat % m / (r2.toNat % m) % 2^32
        have h_eq : ((divuw_input.r1_val.toNat : ℤ) % 4294967296 /
                     ((divuw_input.r2_val.toNat : ℤ) % 4294967296)) =
                    ((divuw_input.r1_val.toNat % 4294967296 /
                      (divuw_input.r2_val.toNat % 4294967296) : ℕ) : ℤ) := by
          push_cast
          rfl
        rw [h_eq]
        have h_ext_r1 : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
            = divuw_input.r1_val.toNat % 4294967296 := by simp
        have h_ext_r2 : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
            = divuw_input.r2_val.toNat % 4294967296 := by simp
        rw [h_ext_r1, h_ext_r2]
        push_cast
        omega
    rw [h_inner_eq]
    -- Now the LHS and the per-rd-cases
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
