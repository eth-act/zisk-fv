import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Circuit.LoadUpperImmediate
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Sail.lui
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Equivalence.Bridge.ControlFlow
import ZiskFv.Equivalence.WriteValueProofs.JumpUType

/-!
End-to-end theorem for RV64 LUI. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LUI`),
* the compositional LUI spec
  (`ZiskFv.Circuit.LoadUpperImmediate.lui_pc_advance` +
  `lui_store_value_lo`/`_hi`),
* the Sail pure-function equivalence (`PureSpec.execute_LUI_pure_equiv`),

into a canonical theorem:

* `equiv_LUI` — the canonical shape:
  `execute_instruction (.UTYPE (imm, rd, uop.LUI)) state
    = (bus_effect exec_row mem_row state).2`.

The bus shape is **shape (c)** — two execution-bus entries (pc-read +
nextPC-write) and a single memory-bus rd-write entry. LUI uses
`store_pc = 0` but the shape-(c) `bus_effect_matches_sail_jump_rrw`
lemma is agnostic to `store_pc` (it only looks at the multiplicities
and address spaces on the two buses), so it reuses cleanly here.
-/

namespace ZiskFv.Equivalence.Lui

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.LoadUpperImmediate

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LUI reduces to the pure-function block supplied by
    `PureSpec.execute_LUI_pure`, given PC readability and the rd /
    imm input alignment.

    Wraps `PureSpec.execute_LUI_pure_equiv` to expose the Sail chain
    at this module's export surface. -/
lemma equiv_LUI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = let lui_output := PureSpec.execute_LUI_pure lui_input
        (do
          Sail.writeReg Register.nextPC lui_output.nextPC
          match lui_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_LUI_pure_equiv lui_input imm rd
    h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    LUI equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`signExtend (imm ++ 0)`) directly; that
    equation is derived internally from circuit witnesses via the
    `WriteValueProofs.JumpUType.h_rd_val_jut_lui` discharge lemma. -/
theorem equiv_LUI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- Sail-state input bridges
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    -- Bus-protocol structural hypotheses
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_LUI_pure lui_input).nextPC = nextPC_val)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Discharge parameters
    (h_circuit : ZiskFv.Tactics.UTypeArchetype.lui_archetype_circuit_holds m r_main next_pc) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- Discharge `h_imm_lo_nat` / `h_imm_hi_nat` via `transpile_LUI` (class #1).
  obtain ⟨h_imm_lo_nat, h_imm_hi_nat⟩ :=
    ZiskFv.Equivalence.Bridge.ControlFlow.lui_discharge_full
      m r_main next_pc imm h_circuit
  -- Discharge `h_lane_rd` via `main_store_pc_emission_bundle` (trust
  -- class #4).
  have h_lane_rd :=
    ZiskFv.Equivalence.Bridge.ControlFlow.lui_discharge_lanes
      m r_main next_pc e_rd h_circuit h_rd_mult h_rd_as
  have h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = BitVec.signExtend 64 (lui_input.imm ++ 0#12) := by
    have h := ZiskFv.Equivalence.WriteValueProofs.JumpUType.h_rd_val_jut_lui
      imm m r_main next_pc e_rd
      h_circuit h_lane_rd h_imm_lo_nat h_imm_hi_nat
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.2.2
    rw [← h_input_imm] at h
    exact h
  rw [equiv_LUI_sail state lui_input imm rd
        h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  simp only [h_nextPC_eq]
  simp only [PureSpec.execute_LUI_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Lui
