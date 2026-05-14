import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.Bits.Execution

/-!
RV64 SLL (shift-left, register variant). Sibling of SLLW.

Full 64-bit shift: takes `rs1`, shifts left by the low 6 bits of `rs2`,
stores the 64-bit result. No PC jump; write to `rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_RTYPE` for `rop.SLL`: the
result is `Sail.shift_bits_left rs1 (Sail.BitVec.extractLsb rs2 5 0)`.
All of this plumbing is centralized in `Fundamentals/Execution.lean::
execute_RTYPE_pure`. Proof shape is the SLLW port with `execute_RTYPEW'`
swapped for `execute_RTYPE'` (no 32-bit sign-extension).
-/

namespace PureSpec

  structure SllInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SllOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SLL: shift r1 left by the low 6 bits of r2, 64-bit result.
      PC advances by 4. Returns the shifted value as the destination-
      register write (or `.none` when `rd = 0`). -/
  def execute_RTYPE_sll_pure (input : SllInput) : SllOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_RTYPE_pure input.r1_val input.r2_val rop.SLL
      )
    : SllOutput
  }

  /-- **SLL Sail-equivalence.** An RV64 SLL
      `.RTYPE (r2, r1, rd, rop.SLL)` reduces to the pure-spec block
      that (a) writes `nextPC = PC + 4`, (b) writes the shift result to
      `rd` (or no-ops when `rd = 0`), (c) retires.

      Same proof shape as `RV64D/add.lean::execute_RTYPE_add_pure_equiv`,
      switching `rop.ADD` for `rop.SLL`. The simp-set unfolds the Sail
      monadic block via `execute_RTYPE_eq_execute_RTYPE'` (from
      `Fundamentals/Execution.lean`); then standard
      `rX_read_xreg_equiv` / `read_xreg_write_other_reg_state` /
      `wX_write_xreg_*_equiv` massage writes through. The `rd = 0`
      vs. `rd ≠ 0` split mirrors ADD's. -/
  lemma execute_RTYPE_sll_pure_equiv
    (sll_input : SllInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sll_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (sll_input.r2_val) state)
    (h_input_rd: sll_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some sll_input.PC)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state =
    let sll_output := execute_RTYPE_sll_pure sll_input
    (do
      Sail.writeReg Register.nextPC sll_output.nextPC
      match sll_output.rd with
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
    simp [execute_RTYPE_sll_pure]
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
