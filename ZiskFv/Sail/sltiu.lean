import ZiskFv.Sail.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure SltiuInput where
    -- operands
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SltiuOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_sltiu_pure (input : SltiuInput) : SltiuOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        if input.r1_val < (BitVec.signExtend 64 input.imm)
        then 1#64
        else 0#64
      )
    : SltiuOutput
  }

  set_option maxHeartbeats 400000 in
  lemma execute_ITYPE_sltiu_pure_equiv
    (sltiu_input : SltiuInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sltiu_input.r1_val) state)
    (h_input_imm: sltiu_input.imm = imm)
    (h_input_rd: sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some sltiu_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.SLTIU))
    ) state =
    let sltiu_output := execute_ITYPE_sltiu_pure sltiu_input
    (do
      Sail.writeReg Register.nextPC sltiu_output.nextPC
      match sltiu_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_ITYPE'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_ITYPE_pure, execute_RTYPE_pure, execute_ITYPE_sltiu_pure, ← h_input_imm]
    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_zero_equiv]
      simp
      rewrite [dite_cond_eq_true]
      . simp
      . simp [h_input_rd, h_zero, regidx_to_fin]
    . have h_inc := regidx_non_zero h_zero
      apply Finset.mem_Icc.mp at h_inc
      obtain ⟨h_low, h_high⟩ := h_inc
      rewrite [
        wX_write_xreg_non_zero_equiv _ _
          (regidx.Regidx rd)
          ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
          (by simp [regidx_to_fin])
      ]
      simp [regidx_to_fin]
      rewrite [dite_cond_eq_false]
      . -- Bridge: BitVec.setWidth 64 (if r1.toNat < sext(imm).toNat then 1#1 else 0#1)
        --       = if r1 < sext(imm) then 1#64 else 0#64
        have h_bridge :
          BitVec.setWidth 64
            (if sltiu_input.r1_val.toNat
                < (BitVec.signExtend 64 sltiu_input.imm).toNat
             then 1#1 else 0#1) =
          if sltiu_input.r1_val < (BitVec.signExtend 64 sltiu_input.imm)
          then 1#64 else 0#64 := by
          by_cases h : sltiu_input.r1_val < (BitVec.signExtend 64 sltiu_input.imm)
          · have : sltiu_input.r1_val.toNat
                   < (BitVec.signExtend 64 sltiu_input.imm).toNat := h
            simp [this, h]
          · have : ¬ sltiu_input.r1_val.toNat
                   < (BitVec.signExtend 64 sltiu_input.imm).toNat := h
            simp [this, h]
        rw [h_bridge]
        simp [h_input_rd, regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
