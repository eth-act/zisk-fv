import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
## RV64M REMW — pure spec + Sail equivalence (Track J4)

REMW is the signed 32-bit divide. Per `riscv2zisk_context.rs:250`,
RV64 `remw` transpiles via `create_register_op(..., "div_w", 4)`,
op = OP_DIV_W = 0xbe = 190, m32 = 1, sa = sb = 1 (signed).

Sail (`InstsEnd.lean:69371`): `execute_REMW (...) (is_unsigned :=
false)` — signed truncated division of low 32 bits, sign-extended
to 64 bits. Special cases per RV64 spec:
  - rs2 = 0           → -1 (all bits set)
  - rs1 = INT32_MIN, rs2 = -1 → INT32_MIN (signed overflow)
-/

namespace PureSpec

  structure RemwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure RemwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_DIVREM_remw_pure (input : RemwInput) : RemwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let q32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then r1_lo32
        else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
          then 0#32
          else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
    let q64 : BitVec 64 := BitVec.signExtend 64 q32
    {
      nextPC := input.PC + 4#64
      rd := if h: input.rd = 0
        then .none
        else .some (
          ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
          q64
        )
    }

  axiom execute_DIVREM_remw_pure_equiv_axiom :
      ∀ (remw_input : RemwInput) (r1 r2 rd : regidx)
        (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource),
        read_xreg (regidx_to_fin r1) state = EStateM.Result.ok remw_input.r1_val state →
        read_xreg (regidx_to_fin r2) state = EStateM.Result.ok remw_input.r2_val state →
        remw_input.rd = regidx_to_fin rd →
        state.regs.get? Register.PC = .some remw_input.PC →
        (do
          Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
          LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))
        ) state =
        let remw_output := execute_DIVREM_remw_pure remw_input
        (do
          Sail.writeReg Register.nextPC remw_output.nextPC
          match remw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())
        ) state

  lemma execute_DIVREM_remw_pure_equiv
      (remw_input : RemwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok remw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok remw_input.r2_val state)
      (h_input_rd : remw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))
      ) state =
      let remw_output := execute_DIVREM_remw_pure remw_input
      (do
        Sail.writeReg Register.nextPC remw_output.nextPC
        match remw_output.rd with
          | .some (rd, rd_val) => write_xreg rd rd_val
          | .none => pure ()
        pure (ExecutionResult.Retire_Success ())
      ) state :=
    execute_DIVREM_remw_pure_equiv_axiom
      remw_input r1 r2 rd state h_input_r1 h_input_r2 h_input_rd h_input_pc

end PureSpec
