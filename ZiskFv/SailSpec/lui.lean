import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  structure LuiInput where
    -- operands
    imm : BitVec 20
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure LuiOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_LUI_pure (input : LuiInput) : LuiOutput :=
    {
      nextPC := input.PC + 4#64
      rd := if h: input.rd = 0
        then .none
        else .some (⟨input.rd, by {
          apply Finset.mem_Icc.mpr
          omega
        }⟩, BitVec.signExtend 64 (input.imm ++ 0#12))
    }

  set_option maxHeartbeats 0 in
  lemma execute_LUI_pure_equiv
    (lui_input : LuiInput)
    (imm: BitVec 20)
    (rd: regidx)
    (h_input_imm: lui_input.imm = imm)
    (h_input_rd: lui_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some lui_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.UTYPE (imm, rd, uop.LUI))
    ) state =
    let lui_output := execute_LUI_pure lui_input
    (do
      Sail.writeReg Register.nextPC lui_output.nextPC
      match lui_output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_UTYPE,
      ← h_input_imm
    ]
    simp [execute_LUI_pure]
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
