import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.Bits.Execution

/-!
RV64 SRAW (shift-right-arithmetic-word). Sibling of SLLW/SRLW.

Takes the low 32 bits of `rs1`, shifts right (arithmetic, preserving the
sign bit) by the low 5 bits of `rs2`, then sign-extends the 32-bit result
back to 64 bits. No PC jump; write to `rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_RTYPEW` for `ropw.SRAW`: the
32-bit result is `shift_bits_right_arith a32 (Sail.BitVec.extractLsb b32 4 0)`
and gets sign-extended to 64 via `sign_extend (m := 64)`. Proof shape is
identical to `sllw.lean::execute_RTYPE_sllw_pure_equiv`, swapping
`ropw.SLLW` for `ropw.SRAW`.
-/

namespace PureSpec

  structure SrawInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SrawOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SRAW: extract low 32 bits of r1, shift right (arithmetic) by low 5
      bits of r2, sign-extend 32-bit result to 64. PC advances by 4. -/
  def execute_RTYPE_sraw_pure (input : SrawInput) : SrawOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_RTYPEW_pure input.r1_val input.r2_val ropw.SRAW
      )
    : SrawOutput
  }

  /-- **SRAW Sail-equivalence.** An RV64 SRAW
      `.RTYPEW (r2, r1, rd, ropw.SRAW)` reduces to the pure-spec block
      that (a) writes `nextPC = PC + 4`, (b) writes the shift result to
      `rd` (or no-ops when `rd = 0`), (c) retires.

      Same proof shape as `sllw.lean::execute_RTYPE_sllw_pure_equiv`,
      switching `ropw.SLLW` for `ropw.SRAW`. -/
  lemma execute_RTYPE_sraw_pure_equiv
    (sraw_input : SrawInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sraw_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (sraw_input.r2_val) state)
    (h_input_rd: sraw_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some sraw_input.PC)
  :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state =
    let sraw_output := execute_RTYPE_sraw_pure sraw_input
    (do
      Sail.writeReg Register.nextPC sraw_output.nextPC
      match sraw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_RTYPEW'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_RTYPE_sraw_pure]
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
