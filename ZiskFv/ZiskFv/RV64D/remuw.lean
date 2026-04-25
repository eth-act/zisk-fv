import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
## RV64M REMUW — pure spec + Sail equivalence

REMUW is the unsigned 32-bit remainder. Per
`riscv2zisk_context.rs:255`, transpiles via
`create_register_op(..., "remu_w", 4)`, op = OP_REMU_W = 0xbd = 189,
m32 = 1, secondary lane.

Sail (`InstsEnd.lean:65921`): `execute_REMW (...) (is_unsigned :=
true)` — analogous to DIVW with remainder semantics. Sign-extends
32-bit remainder to 64 bits.
-/

namespace PureSpec

  structure RemuwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure RemuwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- REMUW pure spec. Lower 32 bits unsigned divide remainder,
      sign-extended to 64 bits. -/
  def execute_DIVREM_remuw_pure (input : RemuwInput) : RemuwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let r32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then r1_lo32   -- remainder of x / 0 is x per RISC-V spec
        else BitVec.ofNat 32 (r1_lo32.toNat % r2_lo32.toNat)
    let r64 : BitVec 64 := BitVec.signExtend 64 r32
    {
      nextPC := input.PC + 4#64
      rd := if h: input.rd = 0
        then .none
        else .some (
          ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
          r64
        )
    }

  axiom execute_DIVREM_remuw_pure_equiv_axiom :
      ∀ (remuw_input : RemuwInput) (r1 r2 rd : regidx)
        (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource),
        read_xreg (regidx_to_fin r1) state = EStateM.Result.ok remuw_input.r1_val state →
        read_xreg (regidx_to_fin r2) state = EStateM.Result.ok remuw_input.r2_val state →
        remuw_input.rd = regidx_to_fin rd →
        state.regs.get? Register.PC = .some remuw_input.PC →
        (do
          Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
          LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))
        ) state =
        let remuw_output := execute_DIVREM_remuw_pure remuw_input
        (do
          Sail.writeReg Register.nextPC remuw_output.nextPC
          match remuw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())
        ) state

  lemma execute_DIVREM_remuw_pure_equiv
      (remuw_input : RemuwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok remuw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok remuw_input.r2_val state)
      (h_input_rd : remuw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some remuw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))
      ) state =
      let remuw_output := execute_DIVREM_remuw_pure remuw_input
      (do
        Sail.writeReg Register.nextPC remuw_output.nextPC
        match remuw_output.rd with
          | .some (rd, rd_val) => write_xreg rd rd_val
          | .none => pure ()
        pure (ExecutionResult.Retire_Success ())
      ) state :=
    execute_DIVREM_remuw_pure_equiv_axiom
      remuw_input r1 r2 rd state h_input_r1 h_input_r2 h_input_rd h_input_pc

end PureSpec
