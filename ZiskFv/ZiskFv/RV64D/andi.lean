import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure AndiInput where
    -- operands
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure AndiOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_andi_pure (input : AndiInput) : AndiOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val &&& BitVec.signExtend 64 input.imm
      )
    : AndiOutput
  }

  lemma execute_ITYPE_andi_pure_equiv
    (andi_input : AndiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (andi_input.r1_val) state)
    (h_input_imm: andi_input.imm = imm)
    (h_input_rd: andi_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some andi_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ANDI))
    ) state =
    let andi_output := execute_ITYPE_andi_pure andi_input
    (do
      Sail.writeReg Register.nextPC andi_output.nextPC
      match andi_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
