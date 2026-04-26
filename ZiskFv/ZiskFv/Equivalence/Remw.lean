import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.RV64D.remw
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64M REMW (signed 32-bit remainder).
Phase 5 follow-on Track J5.

REMW is the W-variant sibling of DIVU. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
both call `execute_REMW` with `is_unsigned = true`.

Three theorems mirroring the DIVU pattern (shape-(a) — ALU/Arith bus):

* `equiv_REMW` — circuit-level (defined in terms of m.a/b lanes via
  `transpile_REMW` per the Phase 5 axiom shape).
* `equiv_REMW_sail` — Sail-level wrapper for
  `execute_DIVREM_remw_pure_equiv`.
* `equiv_REMW_metaplan` — metaplan-target shape composing
  Sail + bus-effect via `bus_effect_matches_sail_alu_rrw`.

Plus V12 companion `equiv_REMW_metaplan_from_bus`.
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

/-- **Metaplan theorem.** Shape (a) ALU/Arith. -/
theorem equiv_REMW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
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
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_REMW_sail state remw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
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

/-- **V12 companion.** Drops `h_input_*` via chip_bus_hyps_alu_rrw. -/
theorem equiv_REMW_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : remw_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3, e0.x4, e0.x5, e0.x6, e0.x7])
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_r2_val : remw_input.r2_val
      = U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3, e1.x4, e1.x5, e1.x6, e1.x7])
    (h_pc : remw_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_idx : remw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_pc_read, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2 h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_bus
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state := by
    rw [h_r2_ptr, h_r2_val]; exact h_rs2_read
  have h_input_rd : remw_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some remw_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_REMW_metaplan state remw_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx h_rd_val


/-- Constructor: build a `PureSpec.RemwInput` from bus entries. -/
def RemwInput_of_bus
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) :
    PureSpec.RemwInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    r2_val := U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                          e1.x4, e1.x5, e1.x6, e1.x7]
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for REMW.** Bus-derived input form: 
    eliminates value-level match hyps via `RemwInput_of_bus`. -/
theorem equiv_REMW_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remw_pure (RemwInput_of_bus e0 e1 e2 exec_row)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb (RemwInput_of_bus e0 e1 e2 exec_row).r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb (RemwInput_of_bus e0 e1 e2 exec_row).r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2
    := by
  exact equiv_REMW_metaplan_from_bus state
    (RemwInput_of_bus e0 e1 e2 exec_row) r1 r2 rd
    exec_row e0 e1 e2
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl h_r2_ptr rfl rfl h_rd_ptr
    rfl h_rd_val

/-- **Track Q ALU/MUL/DIV fan-out for REMW.** Op-bus companion to
    `equiv_REMW_metaplan`: drops `h_input_r1` / `h_input_r2` in
    favour of an op-bus precondition. Mirrors
    `equiv_ADD_metaplan_op_bus`. -/
theorem equiv_REMW_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (op_entry : ZiskFv.Airs.OperationBus.OperationBusEntry FGL)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      remw_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      remw_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
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
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r1_val 31 0
         let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb remw_input.r2_val 31 0
         let q32 : BitVec 32 :=
           if r2_lo32 = 0#32
             then r1_lo32
             else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
               then 0#32
               else BitVec.ofInt 32 (Int.tmod r1_lo32.toInt r2_lo32.toInt)
         BitVec.signExtend 64 q32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_r1_read, h_r2_read⟩ :=
    ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_alu
      state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state := by
    rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state := by
    rw [h_b_match]; exact h_r2_read
  exact equiv_REMW_metaplan state remw_input r1 r2 rd exec_row e0 e1 e2 h_input_r1 h_input_r2 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val

end ZiskFv.Equivalence.Remw
