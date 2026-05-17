import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.ZiskCircuit.Rem
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.SailSpec.rem
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned
import ZiskFv.Equivalence.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 **REM**. REM is the
**secondary** lane on a signed-DIV Arith row (`main_mul = main_div = 0`,
`secondary = 1`). Combines:

* `ZiskFv.Trusted.transpile_REM` (opcode 187),
* `Circuit.Rem.rem_compositional` (instantiates
  `arith_archetype_rem_bus_match` at `OP_REM`),
* `PureSpec.execute_DIVREM_rem_pure_equiv`.

Two canonical theorems:
* `equiv_REM_sail` — Sail-level: `execute_instruction` on an RV64 REM
  reduces to the pure-function block.
* `equiv_REM` — canonical target via
  `bus_effect_matches_sail_alu_rrw` (shape (a), RRW).

The Arith-internal correctness (carry chains → signed 64-bit
remainder) is delegated to future audit.
-/

namespace ZiskFv.Equivalence.Rem

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.ZiskCircuit.Rem
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 REM reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_rem_pure`. Wraps
    `PureSpec.execute_DIVREM_rem_pure_equiv`. -/
lemma equiv_REM_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rem_input : PureSpec.RemInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok rem_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok rem_input.r2_val state)
    (h_input_rd : rem_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some rem_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, false))) state
      = let rem_output := PureSpec.execute_DIVREM_rem_pure rem_input
        (do
          Sail.writeReg Register.nextPC rem_output.nextPC
          match rem_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_rem_pure_equiv
    rem_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    REM equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`execute_DIV_REM_pure ... .DRS`) directly;
    that equation is derived internally from circuit witnesses via
    the `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_rem` discharge
    lemma. -/
theorem equiv_REM
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rem_input : PureSpec.RemInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Structural-unpacking ADDED binders per `trust/structural-unpacking-exceptions.txt` REM entry.
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
      bus.e2.x0.val + bus.e2.x1.val * 256 + bus.e2.x2.val * 65536 + bus.e2.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      bus.e2.x4.val + bus.e2.x5.val * 256 + bus.e2.x6.val * 65536 + bus.e2.x7.val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    (h_rs1_value :
      rem_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      rem_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (rem_input.r1_val.toInt = -(2:ℤ)^63 ∧ rem_input.r2_val.toInt = -1))
    (h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < rem_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * rem_input.r1_val.toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_rem_chunked
      rem_input.r1_val rem_input.r2_val e2 v r_a
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool
      h_np_xor h_nr_pin h_byte_lo h_byte_hi h_rs1_value h_rs2_value
      h_op2_ne h_no_overflow h_r_abs h_r_sign
  rw [equiv_REM_sail state rem_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_rem_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Rem
