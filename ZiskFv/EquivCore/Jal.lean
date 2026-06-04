import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.Jal
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.jal
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.WriteValueProofs.JumpUType
import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 JAL. Combines:

* explicit JAL Main-row, provenance, and PC route facts,
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

/-- JAL `rd = x0` no-memory shape. Production/static lowering emits
    `storeNone` for x0, and Sail suppresses the x0 write, so the state effect
    is carried only by the execution bus. -/
lemma equiv_JAL_x0_no_memory
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (nextPC_val : BitVec 64)
    (promises : ZiskFv.EquivCore.Promises.JumpNoMemPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [] state).2 := by
  obtain ⟨h_input_rd, h_input_rd_zero, h_input_pc, h_input_misa, h_misa_c,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_success, h_nextPC_option⟩ := promises
  rw [equiv_JAL_sail state jal_input imm rd misa_val
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_jump_no_memory
        state exec_row nextPC_val
        (PureSpec.execute_JAL_pure jal_input).throws
        (PureSpec.execute_JAL_pure jal_input).success
        jal_input.PC (BitVec.signExtend 64 jal_input.imm)
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_not_throws h_success]
  simp only [h_nextPC_option]
  have h_rd_none :
      (PureSpec.execute_JAL_pure jal_input).rd = none := by
    simp [PureSpec.execute_JAL_pure, h_input_rd_zero]
  simp [h_rd_none]

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    JAL equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`PC + 4`) directly; that equation is
    derived internally from circuit witnesses via the
    `WriteValueProofs.JumpUType.h_rd_val_jut_jal` discharge lemma. -/
lemma equiv_JAL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (nextPC_val : BitVec 64)
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
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_pc_bridge : (m.pc r_main).val = jal_input.PC.toNat)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296)
     :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  obtain ⟨h_input_rd, h_input_pc, h_input_misa, h_misa_c, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches, h_rd_mult, h_rd_as,
          h_success, h_nextPC_option, h_rd_idx⟩ := promises
  -- Discharge `h_lane_lo`/`h_lane_hi` from the selected Clean Main
  -- `cMemMessage` row, rather than through `main_store_pc_emission_bundle`.
  obtain ⟨h_lane_lo, h_lane_hi⟩ := store_pc_mem.lanes
  -- Derive `h_lo_bound : (m.pc + 4 : FGL).val < 2^32` from the PC bridge
  -- and the existing link-address bound, avoiding the legacy range bus.
  have h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296 := by
    have h4 : ((4 : FGL)).val = 4 := by decide
    have h_no_wrap : (m.pc r_main).val + ((4 : FGL)).val < GL_prime := by
      rw [h_pc_bridge, h4]
      omega
    have h_fgl_val : (m.pc r_main + 4 : FGL).val = jal_input.PC.toNat + 4 := by
      rw [Fin.val_add, Nat.mod_eq_of_lt h_no_wrap, h_pc_bridge, h4]
    have h_bv_add : (jal_input.PC + 4#64).toNat = jal_input.PC.toNat + 4 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h_lt_64 : jal_input.PC.toNat + 4 < 18446744073709551616 := by
        have h_gl_lt : GL_prime < 18446744073709551616 := by decide
        omega
      rw [Nat.mod_eq_of_lt h_lt_64]
    rw [h_fgl_val, ← h_bv_add]
    exact h_pc_offset_lt_2_32
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
      h_circuit h_jmp2 h_pc_bridge h_lane_lo h_lane_hi
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
