import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure BltInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BltOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BLT_pure (input : BltInput) : BltOutput :=
    let skip := !(input.r1_val.toInt <b input.r2_val.toInt)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BltOutput
    }

  lemma execute_BLT_pure_equiv
    (blt_input : BltInput)
    (imm: BitVec 13)
    (h_input_imm: blt_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (blt_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (blt_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BLT ))
    ) state =
    let blt_output := execute_BLT_pure blt_input
    (do
      Sail.writeReg Register.nextPC blt_output.nextPC
      if blt_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !blt_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (blt_input.PC + BitVec.signExtend 64 blt_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := sorry

end PureSpec
