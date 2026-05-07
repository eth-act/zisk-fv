import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Sail.remw
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

/-!
End-to-end theorem for RV64M REMW (signed 32-bit remainder).

REMW is the W-variant sibling of DIVU. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
both call `execute_REMW` with `is_unsigned = true`.

Three theorems mirroring the DIVU pattern (shape-(a) — ALU/Arith bus):

* `equiv_REMW_circuit` — circuit-level (defined in terms of m.a/b lanes via
  `transpile_REMW`).
* `equiv_REMW_sail` — Sail-level wrapper for
  `execute_DIVREM_remw_pure_equiv`.
* `equiv_REMW` — canonical shape composing
  Sail + bus-effect via `bus_effect_matches_sail_alu_rrw`.

Plus V12 companion `equiv_REMW_from_bus`.
-/

namespace ZiskFv.Equivalence.Remw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main

/-- **Sail-level companion.** Wraps `execute_DIVREM_remw_pure_equiv`. -/
theorem equiv_REMW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state)
    (h_input_rd : remw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = let remw_output := PureSpec.execute_DIVREM_remw_pure remw_input
        (do
          Sail.writeReg Register.nextPC remw_output.nextPC
          match remw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_remw_pure_equiv
    remw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    REMW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `RdValDerivation.MulDivRemSigned.h_rd_val_mdrs_remw` discharge lemma. -/
theorem equiv_REMW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state)
    (h_input_rd : remw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_byte_sum_circuit :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
        + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned.h_rd_val_mdrs_remw
      remw_input.r1_val remw_input.r2_val e2
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_byte_sum_circuit
  rw [equiv_REMW_sail state remw_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remw_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp [h_rd_zero, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, dite_false]
    rw [h_rd_val]

end ZiskFv.Equivalence.Remw
