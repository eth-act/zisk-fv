import ZiskFv.Sail.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SLLW (shift-left-word). Phase 2 A6 archetype.

Takes the low 32 bits of `rs1`, shifts left by the low 5 bits of `rs2`,
sign-extends the 32-bit result back to 64 bits. No PC jump; write to
`rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_RTYPEW` for `ropw.SLLW`
(`InstsEnd.lean:65650-65661`): the 32-bit result is
`Sail.shift_bits_left a32 (Sail.BitVec.extractLsb b32 4 0)` and gets
sign-extended to 64 via `sign_extend (m := 64)`. All of this plumbing
is centralized in `Fundamentals/Execution.lean::execute_RTYPEW_pure`.
-/

namespace PureSpec

  structure SllwInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SllwOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SLLW: extract low 32 bits of r1, shift left by low 5 bits of r2,
      sign-extend 32-bit result to 64. PC advances by 4. Returns the
      shifted/extended value as the destination-register write (or
      `.none` when `rd = 0`). -/
  def execute_RTYPE_sllw_pure (input : SllwInput) : SllwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_RTYPEW_pure input.r1_val input.r2_val ropw.SLLW
      )
    : SllwOutput
  }

  /-- **SLLW Sail-equivalence.** An RV64 SLLW
      `.RTYPEW (r2, r1, rd, ropw.SLLW)` reduces to the pure-spec block
      that (a) writes `nextPC = PC + 4`, (b) writes the shift result to
      `rd` (or no-ops when `rd = 0`), (c) retires.

      Same proof shape as `RV64D/add.lean::execute_RTYPE_add_pure_equiv`,
      switching `execute_RTYPE'`/`rop.ADD` for `execute_RTYPEW'`/
      `ropw.SLLW`. The simp-set unfolds the Sail monadic block via
      `execute_RTYPEW_eq_execute_RTYPEW'` (from
      `Fundamentals/Execution.lean`); then standard
      `rX_read_xreg_equiv` / `read_xreg_write_other_reg_state` /
      `wX_write_xreg_*_equiv` massage writes through. The `rd = 0`
      vs. `rd ≠ 0` split mirrors ADD's. -/
  lemma execute_RTYPE_sllw_pure_equiv
    (sllw_input : SllwInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sllw_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (sllw_input.r2_val) state)
    (h_input_rd: sllw_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some sllw_input.PC)
  :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state =
    let sllw_output := execute_RTYPE_sllw_pure sllw_input
    (do
      Sail.writeReg Register.nextPC sllw_output.nextPC
      match sllw_output.rd with
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
    simp [execute_RTYPE_sllw_pure]
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
