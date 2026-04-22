import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SRLIW (shift-right-logical-immediate-word). Phase 3A H2c sibling
of SLLIW.

Takes the low 32 bits of `rs1`, shifts right (logical) by a 5-bit
immediate `shamt`, sign-extends the 32-bit result back to 64 bits. No
PC jump; write to `rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_SHIFTIWOP` for `sopw.SRLIW`:
the 32-bit result is `Sail.shift_bits_right rs1_val shamt` and gets
sign-extended to 64 via `sign_extend (m := 64)`. Proof shape is
identical to `slliw.lean::execute_SHIFTIWOP_slliw_pure_equiv`, swapping
`sopw.SLLIW` for `sopw.SRLIW`.

Trusted-axiom policy: axiomatized per the D4b-patch pattern (see
`slliw.lean` docstring). Catalogues as **C3b** in
`docs/fv/trusted-base.md`.
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

  /-- **SRLIW Sail-equivalence (trusted — C3b).** Direct analogue of
      `execute_SHIFTIWOP_slliw_pure_equiv_axiom`. -/
  axiom execute_SHIFTIWOP_srliw_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
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
    ) state

  /-- **SRLIW Sail-equivalence.** Closed via
      `execute_SHIFTIWOP_srliw_pure_equiv_axiom`. -/
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
    ) state :=
    execute_SHIFTIWOP_srliw_pure_equiv_axiom srliw_input r1 rd
      h_input_r1 h_input_rd h_input_pc

end PureSpec
