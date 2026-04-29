import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SRL (shift-right-logical, register variant). Phase 3A H2 sibling.

Full 64-bit logical right shift: takes `rs1`, shifts right by the low
6 bits of `rs2`, zero-fills on the left. No PC jump; write to `rd`;
advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_RTYPE` for `rop.SRL`, which
uses `Sail.shift_bits_right`. Proof shape identical to SLL with
`rop.SLL` swapped for `rop.SRL`.
-/

namespace PureSpec

  structure SrlInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SrlOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SRL: shift r1 right (logical) by the low 6 bits of r2,
      64-bit result. PC advances by 4. -/
  def execute_RTYPE_srl_pure (input : SrlInput) : SrlOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_RTYPE_pure input.r1_val input.r2_val rop.SRL
      )
    : SrlOutput
  }

  /-- **SRL Sail-equivalence.** Same proof shape as
      `sll.lean::execute_RTYPE_sll_pure_equiv` with `rop.SLL` swapped
      for `rop.SRL`. -/
  lemma execute_RTYPE_srl_pure_equiv
    (srl_input : SrlInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (srl_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (srl_input.r2_val) state)
    (h_input_rd: srl_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some srl_input.PC)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state =
    let srl_output := execute_RTYPE_srl_pure srl_input
    (do
      Sail.writeReg Register.nextPC srl_output.nextPC
      match srl_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_RTYPE'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_RTYPE_srl_pure]
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
