import ZiskFv.RV64D.Auxiliaries

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
        }⟩, input.imm ++ 0#12)
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
  := sorry

end PureSpec
