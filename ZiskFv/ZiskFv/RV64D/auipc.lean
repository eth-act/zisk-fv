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
        }⟩, input.PC + (input.imm ++ 0#12)))
      : AuipcOutput
    }

  set_option maxHeartbeats 0 in
  lemma execute_AUIPC_pure_equiv
    (auipc_input : AuipcInput)
    (imm: BitVec 21)
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
  := sorry

end PureSpec
