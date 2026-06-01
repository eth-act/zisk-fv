import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.ZiskCircuit.Srai
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.srai
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.EquivCore.WriteValueProofs.BinaryShift
import ZiskFv.EquivCore.WriteValueProofs.SailBridge
import ZiskFv.EquivCore.Bridge.BinaryExtension
import ZiskFv.EquivCore.Promises.ShiftImm
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 SRAI (immediate sibling of SRA).

Mirrors `Equivalence.Slli` structurally, swapping `sop.SLLI` for
`sop.SRAI`.
-/

namespace ZiskFv.EquivCore.Srai

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Srai
open ZiskFv.Channels.MemoryBusBytes (byteAt)


/-- **Sail-level companion.** -/
lemma equiv_SRAI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srai_input.r1_val state)
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srai_input.PC) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = let srai_output := PureSpec.execute_SHIFTIOP_srai_pure srai_input
        (do
          Sail.writeReg Register.nextPC srai_output.nextPC
          match srai_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIOP_srai_pure_equiv
    srai_input r1 rd shamt h_input_r1 h_input_shamt h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SRAI equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.BinaryShift.h_rd_val_shift_srai_of_wf` discharge lemma. -/
lemma equiv_SRAI_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_b0_range : (v.b_0 r_binary).val < 2 ^ 24) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨h_input_r1, h_input_shamt, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- Project matches_entry into (op, c_lo, c_hi) sub-facts.
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  have h_op : (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA := by
    rw [← h_op_fgl, h_main_op]; decide
  -- Discharge h_input_r1_circuit + h_shift_pin via SailStateBridge + transpile_SRAI
  -- + matches_entry projection (m32 = 0; op_is_shift = 1).
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, _h_b_hi_t⟩ :=
    transpile_SRAI m r_main (regidx_to_fin r1) (regidx_to_fin rd) shamt
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op
  have h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary := by
    obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7⟩ :=
      h_bytes
    exact ⟨
      by simpa [h0.2.2.2.1] using h_wfs.1.1.1,
      by simpa [h1.2.2.2.1] using h_wfs.2.1.1.1,
      by simpa [h2.2.2.2.1] using h_wfs.2.2.1.1.1,
      by simpa [h3.2.2.2.1] using h_wfs.2.2.2.1.1.1,
      by simpa [h4.2.2.2.1] using h_wfs.2.2.2.2.1.1.1,
      by simpa [h5.2.2.2.1] using h_wfs.2.2.2.2.2.1.1.1,
      by simpa [h6.2.2.2.1] using h_wfs.2.2.2.2.2.2.1.1.1,
      by simpa [h7.2.2.2.1] using h_wfs.2.2.2.2.2.2.2.1.1 ⟩
  have h_input_r1_circuit :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0_of_a_range
      m v r_main r_binary (regidx_to_fin r1) srai_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1 h_op_is_shift h_match
      h_a_range
  have h_shift_pin_shamt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_immediate_eq_of_shift_match_of_b0_range
      m v r_main r_binary shamt h_b_lo_t h_op_is_shift h_match
      h_bytes h_wfs h_b0_range
  have h_shift_pin : srai_input.shamt.toNat = (v.free_in_b r_binary).val % 64 := by
    rw [h_input_shamt]; exact h_shift_pin_shamt
  -- Derive 8 e2 byte ranges from `byteAt_val_lt_256` (chunk-shape
  -- replacement for the retired memory_bus_entry_byte_range_perm_sound axiom).
  have h_e2_0 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 0
  have h_e2_1 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 1
  have h_e2_2 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 2
  have h_e2_3 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 3
  have h_e2_4 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 4
  have h_e2_5 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 5
  have h_e2_6 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 6
  have h_e2_7 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 7
  obtain ⟨hc_lo_sum_lt, hc_hi_sum_lt⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_sra_c_sums_lt_of_wf
      v r_binary h_op h_bytes h_wfs h_a_range
  have hc0 : (v.free_in_c_0 r_binary).val < 4294967296 := by omega
  have hc2 : (v.free_in_c_2 r_binary).val < 4294967296 := by omega
  have hc4 : (v.free_in_c_4 r_binary).val < 4294967296 := by omega
  have hc6 : (v.free_in_c_6 r_binary).val < 4294967296 := by omega
  have hc8 : (v.free_in_c_8 r_binary).val < 4294967296 := by omega
  have hc10 : (v.free_in_c_10 r_binary).val < 4294967296 := by omega
  have hc12 : (v.free_in_c_12 r_binary).val < 4294967296 := by omega
  have hc14 : (v.free_in_c_14 r_binary).val < 4294967296 := by omega
  have hc1 : (v.free_in_c_1 r_binary).val < 4294967296 := by omega
  have hc3 : (v.free_in_c_3 r_binary).val < 4294967296 := by omega
  have hc5 : (v.free_in_c_5 r_binary).val < 4294967296 := by omega
  have hc7 : (v.free_in_c_7 r_binary).val < 4294967296 := by omega
  have hc9 : (v.free_in_c_9 r_binary).val < 4294967296 := by omega
  have hc11 : (v.free_in_c_11 r_binary).val < 4294967296 := by omega
  have hc13 : (v.free_in_c_13 r_binary).val < 4294967296 := by omega
  have hc15 : (v.free_in_c_15 r_binary).val < 4294967296 := by omega
  set shift : ℕ := srai_input.shamt.toNat with h_shift_def
  have h_discharge :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryShift.h_rd_val_shift_srai_of_wf
      m v r_main r_binary e2 srai_input.r1_val shift h_op h_bytes h_wfs h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.EquivCore.WriteValueProofs.SailBridge.sail_srai_bridge
      srai_input.r1_val srai_input.shamt shift h_shift_def
  have h_rd_val : U64.toBV #v[byteAt e2 0, byteAt e2 1, byteAt e2 2, byteAt e2 3,
                              byteAt e2 4, byteAt e2 5, byteAt e2 6, byteAt e2 7]
      = execute_SHIFTIOP_pure srai_input.r1_val srai_input.shamt sop.SRAI := by
    rw [h_discharge, h_bridge]
  rw [equiv_SRAI_sail state srai_input r1 rd shamt
        h_input_r1 h_input_shamt h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_SHIFTIOP_srai_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

-- legacy `equiv_SRAI` (bin_ext_table_consumer_wf route) deleted in T4-purge P3.3.

lemma equiv_SRAI_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_main_active, h_main_op⟩ := pins
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SRA := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inr (Or.inl h_op_v_eq)))
  exact equiv_SRAI_of_wf state srai_input r1 rd shamt m v r_main 0 bus
    promises ⟨h_main_active, h_main_op⟩ h_match_v h_lane_rd
    h_bytes h_wfs h_op_is_shift (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range)

end ZiskFv.EquivCore.Srai
