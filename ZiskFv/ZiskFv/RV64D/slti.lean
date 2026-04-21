import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure SltiInput where
    -- operands
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SltiOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_slti_pure (input : SltiInput) : SltiOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        if input.r1_val.slt (BitVec.signExtend 64 input.imm)
        then 1#64
        else 0#64
      )
    : SltiOutput
  }

  lemma execute_ITYPE_slti_pure_equiv
    (slti_input : SltiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slti_input.r1_val) state)
    (h_input_imm: slti_input.imm = imm)
    (h_input_rd: slti_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some slti_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.SLTI))
    ) state =
    let slti_output := execute_ITYPE_slti_pure slti_input
    (do
      Sail.writeReg Register.nextPC slti_output.nextPC
      match slti_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
