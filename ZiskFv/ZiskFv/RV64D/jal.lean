import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure JalInput where
    -- operands
    imm : BitVec 21
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure JalOutput where
    -- registers
    nextPC : Option (BitVec 64)
    rd : Option (Finset.Icc 1 31 × BitVec 64)
    -- result
    success : Bool
    throws : Bool

  def execute_JAL_pure (input : JalInput) : JalOutput :=
    let bit0_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0]! == 0#1)
    let bit1_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1]! == 0#1)
    {
      nextPC :=
        if !bit0_valid || !bit1_valid
        then (.some (input.PC + 4))
        else (.some (input.PC + BitVec.signExtend 64 input.imm))
      rd := if h: !bit0_valid || !bit1_valid || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := bit0_valid && bit1_valid
      throws := !bit0_valid
    }

  lemma rv32d_execute_jal :
    LeanRV64D.Functions.execute (instruction.JAL (imm, rd)) state =
    LeanRV64D.Functions.execute_JAL imm rd state
  := sorry

  set_option maxHeartbeats 0 in
  lemma execute_JAL_pure_equiv
    (jal_input : JalInput)
    (imm: BitVec 21)
    (rd: regidx)
    (h_input_imm: jal_input.imm = imm)
    (h_input_rd: jal_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JAL (imm, rd))
    ) state =
    let jal_output := execute_JAL_pure jal_input
    (do
      match jal_output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match jal_output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if jal_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !jal_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := sorry

end PureSpec
