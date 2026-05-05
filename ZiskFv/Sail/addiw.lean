import ZiskFv.Sail.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure AddiwInput where
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 64

  structure AddiwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_addiw_pure (input : AddiwInput) : AddiwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_ADDIW_pure input.imm input.r1_val
      )
    : AddiwOutput
  }

  lemma execute_ITYPE_addiw_pure_equiv
    (addiw_input : AddiwInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (addiw_input.r1_val) state)
    (h_input_imm: addiw_input.imm = imm)
    (h_input_rd: addiw_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some addiw_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ADDIW (imm, r1, rd))
    ) state =
    let addiw_output := execute_ITYPE_addiw_pure addiw_input
    (do
      Sail.writeReg Register.nextPC addiw_output.nextPC
      match addiw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_ADDIW'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_ITYPE_addiw_pure, execute_ADDIW_pure, ← h_input_imm]
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
      . simp [h_input_rd, regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
