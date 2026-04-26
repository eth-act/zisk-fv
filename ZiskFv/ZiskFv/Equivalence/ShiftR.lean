import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.ShiftR
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.srlw
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 SRLW (Phase 2.5 D4f — `ShiftArchetype`
sibling validation of SLLW).

Mirrors `Equivalence.Shift` for SLLW, with the direction of the shift
swapped on the Sail side (`ropw.SRLW` vs `ropw.SLLW`). The Main-AIR
compositional lemma is the `ShiftArchetype` m32=1 instantiation at
`OP_SRL_W = 37`.

Emits three theorems matching the SLLW trio:

* `equiv_SRLW` — circuit-level: bus `a_hi = b_hi = 0` under m32=1.
* `equiv_SRLW_sail` — Sail-level: `execute_instruction` on an SRLW
  RTYPEW reduces to the pure spec block.
* `equiv_SRLW_metaplan` — metaplan target. Composes the Sail
  equivalence with the shape-(a) bus-effect lemma
  (`bus_effect_matches_sail_alu_rrw`) from Phase 2.5 D3.
-/

namespace ZiskFv.Equivalence.ShiftR

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.ShiftR

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SRLW theorem.** Given the SRLW-mode Main
    constraints (including `m32 = 1`) and the bus-match to a secondary
    entry, the entry carries zero high lanes. Direct instantiation of
    `ShiftArchetype`'s m32=1 macro at `OP_SRL_W`. -/
theorem equiv_SRLW
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : srlw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  srlw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SRLW reduces to the pure-function block. Wraps
    `PureSpec.execute_RTYPE_srlw_pure_equiv` at this module's export
    surface. -/
theorem equiv_SRLW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = let srlw_output := PureSpec.execute_RTYPE_srlw_pure srlw_input
        (do
          Sail.writeReg Register.nextPC srlw_output.nextPC
          match srlw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_srlw_pure_equiv
    srlw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 SRLW
    equals the state computed by applying `bus_effect` to the
    circuit's execution + memory bus rows.

    Same bus-shape as SLLW (shape (a) — register-read +
    register-read + register-write, discharged via
    `bus_effect_matches_sail_alu_rrw`). No `h_bus_execute_matches_sail`
    parameter remains. -/
theorem equiv_SRLW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    -- Phase 2.5 D3 structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure srlw_input.r1_val srlw_input.r2_val ropw.SRLW) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SRLW_sail state srlw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_srlw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]


/-- **Phase 5 V12 companion.** Drops `h_input_r1` / `h_input_r2` / 
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_SRLW_metaplan` after chip_bus_hyps + match composition.  -/
theorem equiv_SRLW_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Phase 2.5 D3 structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 5 V12: bus precondition + ptr/value match (replaces h_input_r1/r2/pc/rd).
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : srlw_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_r2_val : srlw_input.r2_val
      = U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                    e1.x4, e1.x5, e1.x6, e1.x7])
    (h_pc : srlw_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure srlw_input.r1_val srlw_input.r2_val ropw.SRLW) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2
    := by
  obtain ⟨h_pc_read, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2
      h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
      h_bus
  have h_input_r1 :
      read_xreg (regidx_to_fin r1) state
        = EStateM.Result.ok srlw_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_r2 :
      read_xreg (regidx_to_fin r2) state
        = EStateM.Result.ok srlw_input.r2_val state := by
    rw [h_r2_ptr, h_r2_val]; exact h_rs2_read
  have h_input_rd : srlw_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_SRLW_metaplan state srlw_input r1 r2 rd exec_row e0 e1 e2 h_input_r1 h_input_r2 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val


/-- Constructor: build a `PureSpec.SrlwInput` from bus entries. -/
def SrlwInput_of_bus
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) :
    PureSpec.SrlwInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    r2_val := U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                          e1.x4, e1.x5, e1.x6, e1.x7]
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for SRLW.** Bus-derived input form: 
    eliminates value-level match hyps via `SrlwInput_of_bus`. -/
theorem equiv_SRLW_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Phase 2.5 D3 structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure (SrlwInput_of_bus e0 e1 e2 exec_row)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 5 V12: bus precondition + ptr/value match (replaces h_input_r1/r2/pc/rd).
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure (SrlwInput_of_bus e0 e1 e2 exec_row).r1_val (SrlwInput_of_bus e0 e1 e2 exec_row).r2_val ropw.SRLW) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2

    := by
  exact equiv_SRLW_metaplan_from_bus state
    (SrlwInput_of_bus e0 e1 e2 exec_row) r1 r2 rd
    exec_row e0 e1 e2
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl h_r2_ptr rfl rfl h_rd_ptr
    rfl h_rd_val

/-- **Track Q ALU fan-out for SRLW.** Op-bus companion to
    `equiv_SRLW_metaplan`: drops `h_input_r1` / `h_input_r2` in favour
    of a single op-bus precondition. Mirrors `equiv_ADD_metaplan_op_bus`. -/
theorem equiv_SRLW_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (op_entry : OperationBusEntry FGL)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      srlw_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      srlw_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure srlw_input.r1_val srlw_input.r2_val ropw.SRLW) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_r1_read, h_r2_read⟩ :=
    ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_alu
      state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state := by
    rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state := by
    rw [h_b_match]; exact h_r2_read
  exact equiv_SRLW_metaplan state srlw_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx h_rd_val

end ZiskFv.Equivalence.ShiftR
