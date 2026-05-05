import ZiskFv.Sail.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SRAI (shift-right-arithmetic-immediate). Phase 3A H6 sibling of SRA.

Full 64-bit arithmetic right shift by a 6-bit immediate shamt. Proof
shape identical to SLLI with `sop.SLLI` swapped for `sop.SRAI`.
-/

namespace PureSpec

  structure SraiInput where
    -- operands
    r1_val : BitVec 64
    shamt : BitVec 6
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SraiOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SRAI: shift r1 right (arithmetic, sign-extend) by the 6-bit
      shamt immediate, 64-bit result. PC advances by 4. -/
  def execute_SHIFTIOP_srai_pure (input : SraiInput) : SraiOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_SHIFTIOP_pure input.r1_val input.shamt sop.SRAI
      )
    : SraiOutput
  }

  /-- **SRAI Sail-equivalence.** Same proof shape as
      `slli.lean::execute_SHIFTIOP_slli_pure_equiv` with `sop.SLLI`
      swapped for `sop.SRAI`. -/
  lemma execute_SHIFTIOP_srai_pure_equiv
    (srai_input : SraiInput)
    (r1 rd: regidx) (shamt : BitVec 6)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (srai_input.r1_val) state)
    (h_input_shamt: srai_input.shamt = shamt)
    (h_input_rd: srai_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some srai_input.PC)
  :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state =
    let srai_output := execute_SHIFTIOP_srai_pure srai_input
    (do
      Sail.writeReg Register.nextPC srai_output.nextPC
      match srai_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_SHIFTIOP'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_SHIFTIOP_srai_pure, ← h_input_shamt]
    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_zero_equiv]
      simp
      rewrite [dite_cond_eq_true]
      . simp
      . simp [h_input_rd, h_zero, regidx_to_fin]
    . have h_inc := regidx_non_zero h_zero
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
      . simp [h_input_rd, regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
