import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.Bits.Execution

open LeanRV64D.Functions

/-!
## RV64M REMUW — pure spec + Sail equivalence

REMUW is the unsigned 32-bit remainder. Per
`riscv2zisk_context.rs:255`, transpiles via
`create_register_op(..., "remu_w", 4)`, op = OP_REMU_W = 0xbd = 189,
m32 = 1, secondary lane.

Sail (`InstsEnd.lean:65921`): `execute_REMW (...) (is_unsigned :=
true)` — analogous to DIVW with remainder semantics. Sign-extends
32-bit remainder to 64 bits.

Equivalence is proved using `execute_REMW'` in
`Fundamentals/Execution.lean`.
-/

namespace PureSpec

  structure RemuwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure RemuwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- REMUW pure spec. Lower 32 bits unsigned divide remainder,
      sign-extended to 64 bits. -/
  def execute_DIVREM_remuw_pure (input : RemuwInput) : RemuwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let r32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then r1_lo32   -- remainder of x / 0 is x per RISC-V spec
        else BitVec.ofNat 32 (r1_lo32.toNat % r2_lo32.toNat)
    let r64 : BitVec 64 := BitVec.signExtend 64 r32
    {
      nextPC := input.PC + 4#64
      rd := if h: input.rd = 0
        then .none
        else .some (
          ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
          r64
        )
    }

  /-- Helper: `to_bits_truncate (l := 32) z = BitVec.ofInt 32 z` for any `z : ℤ`. -/
  lemma to_bits_truncate_32_eq_ofInt_remuw (z : ℤ) :
      to_bits_truncate (l := 32) z = BitVec.ofInt 32 z := by
    apply BitVec.eq_of_toNat_eq
    simp only [to_bits_truncate, Sail.get_slice_int, BitVec.extractLsb'_toNat,
               BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.zero_add]
    have h33 : ((2 : ℕ) ^ (0 + 32 + 1) : ℤ) = 8589934592 := by norm_num
    have h32_int : ((2 : ℕ) ^ 32 : ℤ) = 4294967296 := by norm_num
    have h32n : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
    omega

  set_option maxHeartbeats 800000 in
  lemma execute_DIVREM_remuw_pure_equiv
      (remuw_input : RemuwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok remuw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok remuw_input.r2_val state)
      (h_input_rd : remuw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some remuw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))
      ) state =
      let remuw_output := execute_DIVREM_remuw_pure remuw_input
      (do
        Sail.writeReg Register.nextPC remuw_output.nextPC
        match remuw_output.rd with
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
    -- Sail's REMW unsigned: if r2 (lo32) == 0 then result is r1 (lo32 as Int);
    -- else Int.tmod (r1 % 2^32) (r2 % 2^32). After sign_extend (m:=64).
    have h_extract_eq_zero : ∀ v : BitVec 64,
        (Sail.BitVec.extractLsb v 31 0 = 0#32) ↔ (v.toNat % 4294967296 = 0) := by
      intro v
      constructor
      · intro h; rw [← BitVec.toNat_inj] at h; simpa using h
      · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
    have h_inner_eq :
      (BitVec.signExtend 64 (to_bits_truncate (l := 32)
        (if remuw_input.r2_val.toNat % 4294967296 = 0
         then ((remuw_input.r1_val.toNat : ℤ) % 4294967296)
         else ((remuw_input.r1_val.toNat : ℤ) % 4294967296) %
              ((remuw_input.r2_val.toNat : ℤ) % 4294967296)))) =
      (BitVec.signExtend 64
        (if Sail.BitVec.extractLsb remuw_input.r2_val 31 0 = 0#32
         then Sail.BitVec.extractLsb remuw_input.r1_val 31 0
         else BitVec.ofNat 32
           ((Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat %
            (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat))) := by
      rw [to_bits_truncate_32_eq_ofInt_remuw]
      congr 1
      by_cases hb : Sail.BitVec.extractLsb remuw_input.r2_val 31 0 = 0#32
      · have hb' : remuw_input.r2_val.toNat % 4294967296 = 0 := (h_extract_eq_zero _).mp hb
        rw [if_pos hb, if_pos hb']
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ofInt]
        omega
      · have hb' : remuw_input.r2_val.toNat % 4294967296 ≠ 0 :=
          fun h => hb ((h_extract_eq_zero _).mpr h)
        rw [if_neg hb, if_neg hb']
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
        -- bridge (a%m) % (b%m) for nonneg
        have h_eq : ((remuw_input.r1_val.toNat : ℤ) % 4294967296 %
                     ((remuw_input.r2_val.toNat : ℤ) % 4294967296)) =
                    ((remuw_input.r1_val.toNat % 4294967296 %
                      (remuw_input.r2_val.toNat % 4294967296) : ℕ) : ℤ) := by
          push_cast
          rfl
        rw [h_eq]
        have h_ext_r1 : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
            = remuw_input.r1_val.toNat % 4294967296 := by simp
        have h_ext_r2 : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
            = remuw_input.r2_val.toNat % 4294967296 := by simp
        rw [h_ext_r1, h_ext_r2]
        push_cast
        omega
    -- Now bridge using h_inner_eq
    simp only []
    rw [h_inner_eq]
    simp [execute_DIVREM_remuw_pure]
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
