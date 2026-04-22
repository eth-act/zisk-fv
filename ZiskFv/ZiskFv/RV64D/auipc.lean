import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure AuipcInput where
    -- operands
    imm : BitVec 20
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure AuipcOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_AUIPC_pure (input : AuipcInput) : AuipcOutput :=
    {
      nextPC := (input.PC + 4)
      rd := if h: input.rd = 0
        then .none
        else (.some (⟨input.rd, by {
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + BitVec.signExtend 64 (input.imm ++ 0#12)))
      : AuipcOutput
    }

  set_option maxHeartbeats 0 in
  lemma execute_AUIPC_pure_equiv
    (auipc_input : AuipcInput)
    (imm: BitVec 20)
    (rd: regidx)
    (h_input_imm: auipc_input.imm = imm)
    (h_input_rd: auipc_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some auipc_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.UTYPE (imm, rd, .AUIPC))
    ) state =
    let auipc_output := execute_AUIPC_pure auipc_input
    (do
      Sail.writeReg Register.nextPC auipc_output.nextPC
      match auipc_output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_UTYPE,
      LeanRV64D.Functions.get_arch_pc,
      readReg_succ (writeReg_read_diff h_input_pc (show Register.PC ≠ Register.nextPC by grind)),
      ← h_input_imm
    ]
    simp [execute_AUIPC_pure]
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
