import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.LoadUpperImmediate
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.lui
import ZiskFv.Airs.BusHypotheses
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.Bridge.ControlFlow
import ZiskFv.EquivCore.WriteValueProofs.JumpUType
import ZiskFv.EquivCore.Promises.UType

/-!
End-to-end theorem for RV64 LUI. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LUI`),
* the compositional LUI spec
  (`ZiskFv.ZiskCircuit.LoadUpperImmediate.lui_pc_advance` +
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

namespace ZiskFv.EquivCore.Lui

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf_val_lt_256)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.LoadUpperImmediate


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
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- Structural promise bundle (11 fields, see Promises/UType.lean).
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    -- Discharge parameters
    (h_circuit : ZiskFv.Tactics.UTypeArchetype.lui_archetype_circuit_holds m r_main next_pc) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  obtain ⟨h_input_imm, h_input_rd, h_input_pc, h_exec_len, h_e0_mult,
          h_e1_mult, h_nextPC_matches, h_rd_mult, h_rd_as, h_nextPC_eq,
          h_rd_idx⟩ := promises
  -- Discharge `h_imm_lo_nat` / `h_imm_hi_nat` via `transpile_LUI` (class #1).
  obtain ⟨h_imm_lo_nat, h_imm_hi_nat⟩ :=
    ZiskFv.EquivCore.Bridge.ControlFlow.lui_discharge_full
      m r_main next_pc imm h_circuit
  -- Discharge `h_lane_rd` via `main_store_pc_emission_bundle` (trust
  -- class #4).
  have h_lane_rd :=
    ZiskFv.EquivCore.Bridge.ControlFlow.lui_discharge_lanes
      m r_main next_pc e_rd h_circuit h_rd_mult h_rd_as
  have h_rd_val :
      U64.toBV #v[(byteAt e_rd 0 : BitVec 8), (byteAt e_rd 1 : BitVec 8),
                  (byteAt e_rd 2 : BitVec 8), (byteAt e_rd 3 : BitVec 8),
                  (byteAt e_rd 4 : BitVec 8), (byteAt e_rd 5 : BitVec 8),
                  (byteAt e_rd 6 : BitVec 8), (byteAt e_rd 7 : BitVec 8)]
      = BitVec.signExtend 64 (lui_input.imm ++ 0#12) := by
    -- Per-byte ranges follow from `byteOf_val_lt_256` (definitional fact
    -- about `byteOf`'s `% 256` shape).
    have hb0 : (byteAt e_rd 0).val < 256 := byteOf_val_lt_256 e_rd.value_0 0
    have hb1 : (byteAt e_rd 1).val < 256 := byteOf_val_lt_256 e_rd.value_0 1
    have hb2 : (byteAt e_rd 2).val < 256 := byteOf_val_lt_256 e_rd.value_0 2
    have hb3 : (byteAt e_rd 3).val < 256 := byteOf_val_lt_256 e_rd.value_0 3
    have hb4 : (byteAt e_rd 4).val < 256 := byteOf_val_lt_256 e_rd.value_1 0
    have hb5 : (byteAt e_rd 5).val < 256 := byteOf_val_lt_256 e_rd.value_1 1
    have hb6 : (byteAt e_rd 6).val < 256 := byteOf_val_lt_256 e_rd.value_1 2
    have hb7 : (byteAt e_rd 7).val < 256 := byteOf_val_lt_256 e_rd.value_1 3
    have h := ZiskFv.EquivCore.WriteValueProofs.JumpUType.h_rd_val_jut_lui
      imm m r_main next_pc e_rd
      h_circuit h_lane_rd h_imm_lo_nat h_imm_hi_nat
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
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

end ZiskFv.EquivCore.Lui
