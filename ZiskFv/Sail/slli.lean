import ZiskFv.Sail.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SLLI (shift-left-immediate). Phase 3A H4 sibling of SLL.

Full 64-bit shift-left by a 6-bit immediate shamt. No PC jump; write to
`rd`; advance PC by 4. The pure spec mirrors LeanRV64D's
`execute_SHIFTIOP` for `sop.SLLI`, which uses `Sail.shift_bits_left`
with the shamt directly. All plumbing is centralized in
`Fundamentals/Execution.lean::execute_SHIFTIOP_pure`.

Proof shape is the SLL port with `execute_RTYPE'`/`rop.SLL` swapped for
`execute_SHIFTIOP'`/`sop.SLLI`, and the `r2` register-read branch
removed (the shift amount is inlined as an immediate, not read from a
register).
-/

namespace PureSpec

  structure SlliInput where
    -- operands
    r1_val : BitVec 64
    shamt : BitVec 6
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SlliOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SLLI: shift r1 left by the 6-bit shamt immediate, 64-bit result.
      PC advances by 4. -/
  def execute_SHIFTIOP_slli_pure (input : SlliInput) : SlliOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_SHIFTIOP_pure input.r1_val input.shamt sop.SLLI
      )
    : SlliOutput
  }

  /-- **SLLI Sail-equivalence.** An RV64 SLLI
      `.SHIFTIOP (shamt, r1, rd, sop.SLLI)` reduces to the pure-spec
      block. Same proof shape as `RV64D/sll.lean` with `r2` dropped and
      `execute_RTYPE'`/`rop.SLL` swapped for `execute_SHIFTIOP'`/
      `sop.SLLI`. -/
  lemma execute_SHIFTIOP_slli_pure_equiv
    (slli_input : SlliInput)
    (r1 rd: regidx) (shamt : BitVec 6)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slli_input.r1_val) state)
    (h_input_shamt: slli_input.shamt = shamt)
    (h_input_rd: slli_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some slli_input.PC)
  :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state =
    let slli_output := execute_SHIFTIOP_slli_pure slli_input
    (do
      Sail.writeReg Register.nextPC slli_output.nextPC
      match slli_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_SHIFTIOP'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_SHIFTIOP_slli_pure, ← h_input_shamt]
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
