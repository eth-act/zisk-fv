import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure SlliInput where
    -- operslls
    r1_val : BitVec 64
    imm : BitVec 6
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SlliOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_SHIFTIOP_slli_pure (input : SlliInput) : SlliOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val <<< (input.imm % 32)
      )
    : SlliOutput
  }

  lemma execute_SHIFTIOP_slli_pure_equiv
    (slli_input : SlliInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slli_input.r1_val) state)
    (h_input_imm: slli_input.imm = imm)
    (h_input_rd: slli_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some slli_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.SHIFTIOP (imm, r1, rd, sop.SLLI))
    ) state =
    let slli_output := execute_SHIFTIOP_slli_pure slli_input
    (do
      Sail.writeReg Register.nextPC slli_output.nextPC
      match slli_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
