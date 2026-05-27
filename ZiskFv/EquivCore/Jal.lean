import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Jal
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.jal
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.Bridge.ControlFlow
import ZiskFv.EquivCore.WriteValueProofs.JumpUType
import ZiskFv.EquivCore.Promises.Jump

/-!
End-to-end theorem for RV64 JAL. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_JAL`),
* the compositional JAL spec (`ZiskFv.ZiskCircuit.Jal.jal_pc_advance`),
* the Sail pure-function equivalence (`PureSpec.execute_JAL_pure_equiv`),

into a canonical theorem:

* `equiv_JAL` — the canonical shape:
  `execute_instruction (.JAL (imm, rd)) state
    = (bus_effect exec_row mem_row state).2`.

For JAL the operation bus is inactive (`is_external_op = 0`); only
the execution + memory bus entries matter.
-/

namespace ZiskFv.EquivCore.Jal

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf_val_lt_256)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Jal


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 JAL reduces to the pure-function block supplied by
    `PureSpec.execute_JAL_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` (no compressed extension)
    witness.

    Wraps `PureSpec.execute_JAL_pure_equiv` to expose the Sail chain at
    this module's export surface. -/
lemma equiv_JAL_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = let jal_output := PureSpec.execute_JAL_pure jal_input
        (do
          match jal_output.nextPC with
            | .some nextPC => Sail.writeReg Register.nextPC nextPC
            | .none => pure ()
          match jal_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          if jal_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !jal_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_JAL_pure_equiv jal_input imm rd
    h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    JAL equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`PC + 4`) directly; that equation is
    derived internally from circuit witnesses via the
    `WriteValueProofs.JumpUType.h_rd_val_jut_jal` discharge lemma. -/
theorem equiv_JAL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    -- Structural promise bundle (12 fields, see Promises/Jump.lean).
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    -- JAL-specific binders kept inline:
    (h_input_imm : jal_input.imm = imm)
    -- Happy-path hypothesis: no alignment fault under ZisK's RV64IM profile.
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    -- Discharge parameters
    (h_circuit : ZiskFv.ZiskCircuit.Jal.jal_circuit_holds m r_main next_pc)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296)
     :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  obtain ⟨h_input_rd, h_input_pc, h_input_misa, h_misa_c, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches, h_rd_mult, h_rd_as,
          h_success, h_nextPC_option, h_rd_idx⟩ := promises
  -- Discharge `h_jmp2` via `transpile_JAL` (class #1).
  have h_jmp2 : m.jmp_offset2 r_main = 4 :=
    ZiskFv.EquivCore.Bridge.ControlFlow.jal_discharge_full
      m r_main next_pc h_circuit
  -- Discharge `h_lane_lo`/`h_lane_hi` via `main_store_pc_emission_bundle`
  -- (trust class #4).
  obtain ⟨h_lane_lo, h_lane_hi⟩ :=
    ZiskFv.EquivCore.Bridge.ControlFlow.jal_discharge_lanes
      m r_main next_pc e_rd h_circuit h_rd_mult h_rd_as
  -- Derive `h_lo_bound : (m.pc + 4 : FGL).val < 2^32` row-natively from the
  -- byte-pack range bound `memory_entry_lo_val_lt_2_32` (Class #4 byte-range)
  -- combined with the JAL collapse of the lane-match equation. Replaces a
  -- caller-supplied hypothesis.
  have h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296 := by
    have h_sv := ZiskFv.ZiskCircuit.Jal.jal_store_value m r_main next_pc h_circuit
    have h_eq : ZiskFv.Airs.MemoryBus.memory_entry_lo e_rd = m.pc r_main + 4 := by
      have hl := h_lane_lo
      simp only [ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo] at hl
      rw [h_sv, h_jmp2] at hl
      exact hl
    rw [← h_eq]
    exact ZiskFv.Airs.MemoryBus.memory_entry_lo_val_lt_2_32 e_rd
  -- Per-byte ranges from `byteOf_val_lt_256` (chunk-shape replacement
  -- for the retired memory_bus_entry_byte_range_perm_sound axiom).
  have hb0 : (byteAt e_rd 0).val < 256 := byteOf_val_lt_256 e_rd.value_0 0
  have hb1 : (byteAt e_rd 1).val < 256 := byteOf_val_lt_256 e_rd.value_0 1
  have hb2 : (byteAt e_rd 2).val < 256 := byteOf_val_lt_256 e_rd.value_0 2
  have hb3 : (byteAt e_rd 3).val < 256 := byteOf_val_lt_256 e_rd.value_0 3
  have hb4 : (byteAt e_rd 4).val < 256 := byteOf_val_lt_256 e_rd.value_1 0
  have hb5 : (byteAt e_rd 5).val < 256 := byteOf_val_lt_256 e_rd.value_1 1
  have hb6 : (byteAt e_rd 6).val < 256 := byteOf_val_lt_256 e_rd.value_1 2
  have hb7 : (byteAt e_rd 7).val < 256 := byteOf_val_lt_256 e_rd.value_1 3
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.JumpUType.h_rd_val_jut_jal
      jal_input.PC m r_main next_pc e_rd
      h_circuit h_jmp2 h_lane_lo h_lane_hi
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [equiv_JAL_sail state jal_input imm rd misa_val
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  simp only [h_nextPC_option, h_not_throws, h_success, Bool.not_true]
  have h_bit0_neg :
      (!BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[0]! == 0#1)
      = false := by
    have h_t : (PureSpec.execute_JAL_pure jal_input).throws = false := h_not_throws
    simp only [PureSpec.execute_JAL_pure] at h_t
    exact h_t
  have h_bit1_neg :
      (!BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[1]! == 0#1)
      = false := by
    have h_s : (PureSpec.execute_JAL_pure jal_input).success = true := h_success
    simp only [PureSpec.execute_JAL_pure] at h_s
    simp_all
  simp only [PureSpec.execute_JAL_pure, h_rd_idx, h_bit0_neg, h_bit1_neg, Bool.false_or]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e_rd.ptr = 0
  · simp only [h_rd_zero, decide_true, ↓reduceDIte, Bool.false_eq_true,
               if_false, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, decide_false, ↓reduceDIte, Bool.false_eq_true,
               if_false, bind, pure, EStateM.bind, EStateM.pure]
    rw [h_rd_val]

/-! ## Misaligned-target companions

JAL is unconditional (no taken/not-taken case-split), so the misaligned cases
fire purely on the bits of `PC + sext imm`. Pure-spec encoding:
* `bit0_valid := (...[0]! == 0#1)`, `bit1_valid := (...[1]! == 0#1)`.
* `success := bit0_valid && bit1_valid`, `throws := !bit0_valid`.
* `rd := if !bit0_valid || !bit1_valid || rd = 0 then .none else ...`,
  so on either misaligned case the rd write is suppressed.

Misaligned-bit-1 case (bit0=0, bit1=1): throws=false, success=false,
nextPC = .some (PC + 4) → Sail emits `Memory_Exception` (E_Fetch_Addr_Align).
Misaligned-bit-0 case (bit0=1): throws=true → Sail throws Assertion. -/

end ZiskFv.EquivCore.Jal
