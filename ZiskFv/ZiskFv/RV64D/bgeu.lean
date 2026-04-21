import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure BgeuInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BgeuOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BGEU_pure (input : BgeuInput) : BgeuOutput :=
    let skip := !(input.r1_val.toNat ≥b input.r2_val.toNat)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BgeuOutput
    }

  lemma execute_BGEU_pure_succ_throws
    (input : BgeuInput)
  :
    let output := execute_BGEU_pure input
    output.success = true → output.throws = false
  := sorry

  @[simp]
  lemma sign_extend_equiv :
    @LeanRV64D.Functions.sign_extend width1 width2 =
    @BitVec.signExtend width1 width2
  := rfl

  set_option maxHeartbeats 0 in
  lemma execute_BGEU_pure_equiv
    (bgeu_input : BgeuInput)
    (imm: BitVec 13)
    (h_input_imm: bgeu_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bgeu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bgeu_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BGEU ))
    ) state =
    let bgeu_output := execute_BGEU_pure bgeu_input
    (do
      Sail.writeReg Register.nextPC bgeu_output.nextPC
      if bgeu_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bgeu_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := sorry

end PureSpec
