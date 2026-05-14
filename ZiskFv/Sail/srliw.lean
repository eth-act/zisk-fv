import ZiskFv.Sail.Auxiliaries
import ZiskFv.Bits.Execution

/-!
RV64 SRLIW (shift-right-logical-immediate-word). Sibling of SLLIW.

Takes the low 32 bits of `rs1`, shifts right (logical) by a 5-bit
immediate `shamt`, sign-extends the 32-bit result back to 64 bits. No
PC jump; write to `rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_SHIFTIWOP` for `sopw.SRLIW`:
the 32-bit result is `Sail.shift_bits_right rs1_val shamt` and gets
sign-extended to 64 via `sign_extend (m := 64)`. Proof shape is
identical to `slliw.lean::execute_SHIFTIWOP_slliw_pure_equiv`, swapping
`sopw.SLLIW` for `sopw.SRLIW`.
-/

namespace PureSpec

  structure SrliwInput where
    r1_val : BitVec 64
    shamt : BitVec 5
    rd : Fin 32
    PC : BitVec 64

  structure SrliwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SRLIW: extract low 32 bits of r1, shift right (logical) by
      5-bit immediate `shamt`, sign-extend 32-bit result to 64. PC
      advances by 4. -/
  def execute_SHIFTIWOP_srliw_pure (input : SrliwInput) : SrliwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_right
            (Sail.BitVec.extractLsb input.r1_val 31 0) input.shamt)
      )
    : SrliwOutput
  }

  /-- **SRLIW Sail-equivalence.** Direct analogue of
      `execute_SHIFTIWOP_slliw_pure_equiv` with
      `sopw.SLLIW → sopw.SRLIW`. -/
  lemma execute_SHIFTIWOP_srliw_pure_equiv
    (srliw_input : SrliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srliw_input.r1_val state)
    (h_input_rd : srliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srliw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state =
    let srliw_output := execute_SHIFTIWOP_srliw_pure srliw_input
    (do
      Sail.writeReg Register.nextPC srliw_output.nextPC
      match srliw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_SHIFTIWOP'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_SHIFTIWOP_srliw_pure, execute_SHIFTIWOP_pure]
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
