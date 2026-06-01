import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.AddUpperImmediatePC
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.auipc
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.EquivCore.Bridge.ControlFlow
import ZiskFv.EquivCore.WriteValueProofs.JumpUType
import ZiskFv.EquivCore.Promises.UType
import ZiskFv.Compliance.SharedBundles

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

namespace ZiskFv.EquivCore.Auipc

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf_val_lt_256)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.AddUpperImmediatePC


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
lemma equiv_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (nextPC_val : BitVec 64)
    -- Structural promise bundle (11 fields, see Promises/UType.lean).
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    -- Discharge parameters
    (h_circuit :
      ZiskFv.Tactics.UTypeArchetype.auipc_archetype_circuit_holds m r_main next_pc)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296)
     :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  obtain ⟨h_input_imm, h_input_rd, h_input_pc, h_exec_len, h_e0_mult,
          h_e1_mult, h_nextPC_matches, h_rd_mult, h_rd_as, h_nextPC_eq,
          h_rd_idx⟩ := promises
  -- Discharge `h_lane_lo`/`h_lane_hi` from the selected Clean Main
  -- `cMemMessage` row, rather than through `main_store_pc_emission_bundle`.
  obtain ⟨h_lane_lo, h_lane_hi⟩ := store_pc_mem.lanes
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
    ZiskFv.EquivCore.Bridge.ControlFlow.auipc_offset_discharge
      m r_main next_pc auipc_input.imm h_circuit h_no_wrap_offset
  -- Derive `h_lo_bound` from the PC/offset bridges and the existing
  -- 32-bit result bound, avoiding the legacy range bus.
  have h_lo_bound :
      (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296 := by
    obtain ⟨_h_subset, h_mode⟩ := h_circuit
    obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
    have h_pc_bridge : (m.pc r_main).val = auipc_input.PC.toNat :=
      ZiskFv.Trusted.transpile_PC_for_AUIPC m r_main auipc_input.PC h_ext h_op
    have h_no_wrap_fgl :
        (m.pc r_main).val + (m.jmp_offset2 r_main).val < GL_prime := by
      rw [h_pc_bridge, h_offset_bridge]
      exact h_no_wrap
    have h_fgl_val :
        (m.pc r_main + m.jmp_offset2 r_main : FGL).val =
          auipc_input.PC.toNat
            + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat := by
      rw [Fin.val_add, Nat.mod_eq_of_lt h_no_wrap_fgl, h_pc_bridge, h_offset_bridge]
    have h_bv_add :
        (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat =
          auipc_input.PC.toNat
            + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat := by
      rw [BitVec.toNat_add]
      have h_lt_64 :
          auipc_input.PC.toNat
            + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
              < 18446744073709551616 := by
        have h_gl_lt : GL_prime < 18446744073709551616 := by decide
        omega
      rw [Nat.mod_eq_of_lt h_lt_64]
    rw [h_fgl_val, ← h_bv_add]
    exact h_pc_offset_lt_2_32
  have h_rd_val :
      U64.toBV #v[(byteAt e_rd 0 : BitVec 8), (byteAt e_rd 1 : BitVec 8),
                  (byteAt e_rd 2 : BitVec 8), (byteAt e_rd 3 : BitVec 8),
                  (byteAt e_rd 4 : BitVec 8), (byteAt e_rd 5 : BitVec 8),
                  (byteAt e_rd 6 : BitVec 8), (byteAt e_rd 7 : BitVec 8)]
      = auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ 0#12) := by
    -- Per-byte ranges follow from `byteOf_val_lt_256` (definitional fact
    -- about `byteOf`'s `% 256` shape). `byteAt` is `@[reducible]` so it
    -- unfolds at type-check time to a `byteOf` call on either chunk.
    have hb0 : (byteAt e_rd 0).val < 256 := byteOf_val_lt_256 e_rd.value_0 0
    have hb1 : (byteAt e_rd 1).val < 256 := byteOf_val_lt_256 e_rd.value_0 1
    have hb2 : (byteAt e_rd 2).val < 256 := byteOf_val_lt_256 e_rd.value_0 2
    have hb3 : (byteAt e_rd 3).val < 256 := byteOf_val_lt_256 e_rd.value_0 3
    have hb4 : (byteAt e_rd 4).val < 256 := byteOf_val_lt_256 e_rd.value_1 0
    have hb5 : (byteAt e_rd 5).val < 256 := byteOf_val_lt_256 e_rd.value_1 1
    have hb6 : (byteAt e_rd 6).val < 256 := byteOf_val_lt_256 e_rd.value_1 2
    have hb7 : (byteAt e_rd 7).val < 256 := byteOf_val_lt_256 e_rd.value_1 3
    exact ZiskFv.EquivCore.WriteValueProofs.JumpUType.h_rd_val_jut_auipc
      auipc_input.PC auipc_input.imm m r_main next_pc e_rd
      h_circuit h_offset_bridge h_lane_lo h_lane_hi
      h_no_wrap h_lo_bound h_pc_offset_lt_2_32
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
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

end ZiskFv.EquivCore.Auipc
