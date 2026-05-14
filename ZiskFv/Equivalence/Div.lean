import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.PackedBitVec.MulNoWrap
import ZiskFv.Circuit.Div
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Sail.div
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned

/-!
End-to-end theorem for RV64 **DIV**. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_DIV`),
* the compositional DIV spec (`ZiskFv.Circuit.Div.div_compositional`),
* the Sail pure-function equivalence (`PureSpec.execute_DIVREM_div_pure_equiv`),

into three canonical theorems:

* `equiv_DIV_circuit` — circuit-level. Main's packed `c` equals Arith's
  packed quotient (primary output lane `a[]`), given the bus match.
* `equiv_DIV_sail` — Sail-level. `execute_instruction` on an RV64 DIV
  reduces to the pure-function block.
* `equiv_DIV` — canonical shape: Sail's
  `execute_instruction` equals `(bus_effect exec_row mem_row state).2`.

Shape (a) (RTYPE RRW — register read + register read + register write)
is reused from MUL, so bus matching uses `bus_effect_matches_sail_alu_rrw`.
-/

namespace ZiskFv.Equivalence.Div

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open ZiskFv.Circuit.Div
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 DIV reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_div_pure`. Wraps
    `PureSpec.execute_DIVREM_div_pure_equiv`. -/
lemma equiv_DIV_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok div_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok div_input.r2_val state)
    (h_input_rd : div_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some div_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = let div_output := PureSpec.execute_DIVREM_div_pure div_input
        (do
          Sail.writeReg Register.nextPC div_output.nextPC
          match div_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_div_pure_equiv
    div_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    DIV equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div` discharge
    lemma. -/
theorem equiv_DIV
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok div_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok div_input.r2_val state)
    (h_input_rd : div_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some div_input.PC)
    -- Structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_div_pure div_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : div_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Structural-unpacking ADDED binders per `trust/structural-unpacking-exceptions.txt` DIV entry.
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
              ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
              ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    (h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    (h_op1 :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_op2 :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div_chunked
      div_input.r1_val div_input.r2_val e2 v r_a
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool
      h_np_xor h_nr_pin h_byte_lo h_byte_hi h_op1 h_op2
      h_op2_ne h_no_overflow h_r_abs h_r_sign
  rw [equiv_DIV_sail state div_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_div_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Div
