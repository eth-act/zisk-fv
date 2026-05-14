import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.AddUpperImmediatePC
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Sail.auipc
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Equivalence.Bridge.ControlFlow
import ZiskFv.Equivalence.WriteValueProofs.JumpUType

/-!
End-to-end theorem for RV64 AUIPC. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_AUIPC`),
* the compositional AUIPC spec
  (`ZiskFv.ZiskCircuit.AddUpperImmediatePC.auipc_pc_advance` +
  `auipc_store_value_lo`/`_hi`),
* the Sail pure-function equivalence (`PureSpec.execute_AUIPC_pure_equiv`),

into a canonical theorem:

* `equiv_AUIPC` — the canonical shape:
  `execute_instruction (.UTYPE (imm, rd, uop.AUIPC)) state
    = (bus_effect exec_row mem_row state).2`.

The bus shape is **shape (c)** — two execution-bus entries (pc-read +
nextPC-write) and a single memory-bus rd-write entry.

**PC-read wrinkle.** AUIPC's Sail spec reads the architectural PC via
`get_arch_pc()`, which after the `nextPC` write still returns the
original PC (`readReg_succ (writeReg_read_diff ...)` — PC and nextPC
are distinct registers in the Sail state). The pure-spec equivalence
lemma handles this bridge. The circuit side carries the PC via the
`store_pc` mechanic (`store_value[0] = pc + jmp_offset2 = pc + imm`),
which is captured by `auipc_store_value_lo`.
-/

namespace ZiskFv.Equivalence.Auipc

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.AddUpperImmediatePC

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 AUIPC reduces to the pure-function block supplied by
    `PureSpec.execute_AUIPC_pure`, given PC readability and the
    rd / imm input alignment.

    Wraps `PureSpec.execute_AUIPC_pure_equiv`. The pure-spec theorem
    bridges the `get_arch_pc` read-after-write-nextPC via
    `readReg_succ (writeReg_read_diff ...)`. -/
lemma equiv_AUIPC_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = let auipc_output := PureSpec.execute_AUIPC_pure auipc_input
        (do
          Sail.writeReg Register.nextPC auipc_output.nextPC
          match auipc_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_AUIPC_pure_equiv auipc_input imm rd
    h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    AUIPC equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`PC + signExtend (imm ++ 0)`) directly;
    that equation is derived internally from circuit witnesses via the
    `WriteValueProofs.JumpUType.h_rd_val_jut_auipc` discharge lemma. -/
theorem equiv_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Discharge parameters
    (h_circuit :
      ZiskFv.Tactics.UTypeArchetype.auipc_archetype_circuit_holds m r_main next_pc)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296)
     :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- Discharge `h_lane_lo`/`h_lane_hi` via `main_store_pc_emission_bundle`
  -- (trust class #4).
  obtain ⟨h_lane_lo, h_lane_hi⟩ :=
    ZiskFv.Equivalence.Bridge.ControlFlow.auipc_discharge_lanes
      m r_main next_pc e_rd h_circuit h_rd_mult h_rd_as
  -- Discharge `h_offset_bridge` via `transpile_AUIPC` (trust class #1).
  -- `h_no_wrap` gives `PC + signExt < GL_prime`; since `PC.toNat ≥ 0`,
  -- we deduce `signExt < GL_prime` (the no-wrap bound on the offset
  -- alone) and feed it to `auipc_offset_discharge`.
  have h_no_wrap_offset :
      (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat < GL_prime := by
    have := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h_no_wrap
    exact this
  have h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat :=
    ZiskFv.Equivalence.Bridge.ControlFlow.auipc_offset_discharge
      m r_main next_pc auipc_input.imm h_circuit h_no_wrap_offset
  have h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ 0#12) :=
    ZiskFv.Equivalence.WriteValueProofs.JumpUType.h_rd_val_jut_auipc
      auipc_input.PC auipc_input.imm m r_main next_pc e_rd
      h_circuit h_offset_bridge h_lane_lo h_lane_hi
      h_no_wrap h_lo_bound h_pc_offset_lt_2_32
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.2.2
  rw [equiv_AUIPC_sail state auipc_input imm rd
        h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  simp only [h_nextPC_eq]
  simp only [PureSpec.execute_AUIPC_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Auipc
