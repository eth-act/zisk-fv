import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SRAIW (shift-right-arithmetic-immediate-word). Phase 3A H2d sibling
of SLLIW/SRLIW.

Takes the low 32 bits of `rs1`, shifts right (arithmetic, preserving the
sign bit) by a 5-bit immediate `shamt`, sign-extends the 32-bit result
back to 64 bits. No PC jump; write to `rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_SHIFTIWOP` for `sopw.SRAIW`:
the 32-bit result is `shift_bits_right_arith rs1_val shamt` and gets
sign-extended to 64 via `sign_extend (m := 64)`. Proof shape is
identical to `slliw.lean::execute_SHIFTIWOP_slliw_pure_equiv`, swapping
`sopw.SLLIW` for `sopw.SRAIW`.

Trusted-axiom policy: axiomatized per the D4b-patch pattern (see
`slliw.lean` docstring). Catalogues as **C3c** in
`docs/fv/trusted-base.md`.
-/

namespace PureSpec

  structure SraiwInput where
    r1_val : BitVec 64
    shamt : BitVec 5
    rd : Fin 32
    PC : BitVec 64

  structure SraiwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SRAIW: extract low 32 bits of r1, shift right (arithmetic)
      by 5-bit immediate `shamt`, sign-extend 32-bit result to 64.
      PC advances by 4. -/
  def execute_SHIFTIWOP_sraiw_pure (input : SraiwInput) : SraiwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        LeanRV64D.Functions.sign_extend (m := 64)
          (LeanRV64D.Functions.shift_bits_right_arith
            (Sail.BitVec.extractLsb input.r1_val 31 0) input.shamt)
      )
    : SraiwOutput
  }

  /-- **SRAIW Sail-equivalence (trusted — C3c).** Direct analogue of
      `execute_SHIFTIWOP_slliw_pure_equiv_axiom`. -/
  axiom execute_SHIFTIWOP_sraiw_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (sraiw_input : SraiwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraiw_input.r1_val state)
    (h_input_rd : sraiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraiw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state =
    let sraiw_output := execute_SHIFTIWOP_sraiw_pure sraiw_input
    (do
      Sail.writeReg Register.nextPC sraiw_output.nextPC
      match sraiw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state

  /-- **SRAIW Sail-equivalence.** Closed via
      `execute_SHIFTIWOP_sraiw_pure_equiv_axiom`. -/
  lemma execute_SHIFTIWOP_sraiw_pure_equiv
    (sraiw_input : SraiwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraiw_input.r1_val state)
    (h_input_rd : sraiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraiw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state =
    let sraiw_output := execute_SHIFTIWOP_sraiw_pure sraiw_input
    (do
      Sail.writeReg Register.nextPC sraiw_output.nextPC
      match sraiw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state :=
    execute_SHIFTIWOP_sraiw_pure_equiv_axiom sraiw_input r1 rd
      h_input_r1 h_input_rd h_input_pc

end PureSpec
