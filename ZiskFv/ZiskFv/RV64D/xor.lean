import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure XorInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure XorOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_RTYPE_xor_pure (input : XorInput) : XorOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val ^^^ input.r2_val
      )
    : XorOutput
  }

  lemma execute_RTYPE_xor_pure_equiv
    (xor_input : XorInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (xor_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (xor_input.r2_val) state)
    (h_input_rd: xor_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some xor_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.RTYPE (r2, r1, rd, rop.XOR))
    ) state =
    let xor_output := execute_RTYPE_xor_pure xor_input
    (do
      Sail.writeReg Register.nextPC xor_output.nextPC
      match xor_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
