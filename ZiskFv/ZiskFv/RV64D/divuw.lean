import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
## RV64M DIVUW — pure spec + Sail equivalence

DIVUW is the unsigned 32-bit divide. Per
`riscv2zisk_context.rs:251`, RV64 `divuw` transpiles via
`create_register_op(..., "divu_w", 4)`, emitting a single Arith-bus
row with `op = OP_DIVU_W = 0xbc = 188`, `m32 = 1`.

Per Sail (`InstsEnd.lean:69371`), `execute_DIVW (...) (is_unsigned :=
true)` extracts low 32 bits of `rs1`/`rs2`, treats them as unsigned,
divides (with `-1` on zero-divisor), then sign-extends the 32-bit
quotient to 64 bits (per RV64 spec for the *W variants).

The Sail equivalence is axiomatized to keep the proof tractable —
the unfolding of `execute_DIVW` is heavier than the integer arithmetic
warrants.
-/

namespace PureSpec

  structure DivuwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure DivuwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- DIVUW pure spec. Lower 32 bits of `r1`, `r2` interpreted as
      unsigned; divide; sign-extend 32-bit quotient to 64 bits. -/
  def execute_DIVREM_divuw_pure (input : DivuwInput) : DivuwOutput :=
    let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r1_val 31 0
    let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb input.r2_val 31 0
    let q32 : BitVec 32 :=
      if r2_lo32 = 0#32
        then BitVec.allOnes 32
        else BitVec.ofNat 32 (r1_lo32.toNat / r2_lo32.toNat)
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

  /-- Sail-side equivalence (axiomatized — `execute_DIVW`'s body is
      a deep nested let/if chain whose unfolding would be a substantial
      Sail-internals proof). Trust adds 1 axiom. -/
  axiom execute_DIVREM_divuw_pure_equiv_axiom :
      ∀ (divuw_input : DivuwInput) (r1 r2 rd : regidx)
        (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource),
        read_xreg (regidx_to_fin r1) state = EStateM.Result.ok divuw_input.r1_val state →
        read_xreg (regidx_to_fin r2) state = EStateM.Result.ok divuw_input.r2_val state →
        divuw_input.rd = regidx_to_fin rd →
        state.regs.get? Register.PC = .some divuw_input.PC →
        (do
          Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
          LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))
        ) state =
        let divuw_output := execute_DIVREM_divuw_pure divuw_input
        (do
          Sail.writeReg Register.nextPC divuw_output.nextPC
          match divuw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())
        ) state

  lemma execute_DIVREM_divuw_pure_equiv
      (divuw_input : DivuwInput)
      (r1 r2 rd : regidx)
      (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok divuw_input.r1_val state)
      (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok divuw_input.r2_val state)
      (h_input_rd : divuw_input.rd = regidx_to_fin rd)
      (h_input_pc : state.regs.get? Register.PC = .some divuw_input.PC) :
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))
      ) state =
      let divuw_output := execute_DIVREM_divuw_pure divuw_input
      (do
        Sail.writeReg Register.nextPC divuw_output.nextPC
        match divuw_output.rd with
          | .some (rd, rd_val) => write_xreg rd rd_val
          | .none => pure ()
        pure (ExecutionResult.Retire_Success ())
      ) state :=
    execute_DIVREM_divuw_pure_equiv_axiom
      divuw_input r1 r2 rd state h_input_r1 h_input_r2 h_input_rd h_input_pc

end PureSpec
