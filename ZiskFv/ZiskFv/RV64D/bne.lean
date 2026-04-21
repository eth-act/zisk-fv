import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure BneInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BneOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BNE_pure (input : BneInput) : BneOutput :=
    let skip := !(input.r1_val != input.r2_val)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BneOutput
    }

  @[simp]
  lemma sign_extend_equiv :
    @LeanRV64D.Functions.sign_extend width1 width2 =
    @BitVec.signExtend width1 width2
  := rfl

  set_option maxHeartbeats 0 in
  lemma execute_BNE_pure_equiv
    (bne_input : BneInput)
    (imm: BitVec 13)
    (h_input_imm: bne_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bne_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bne_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BNE ))
    ) state =
    let bne_output := execute_BNE_pure bne_input
    (do
      Sail.writeReg Register.nextPC bne_output.nextPC
      if bne_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bne_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 64 bne_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := sorry

end PureSpec
