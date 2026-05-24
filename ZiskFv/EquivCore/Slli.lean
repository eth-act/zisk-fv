import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.ZiskCircuit.Slli
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.slli
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.EquivCore.WriteValueProofs.BinaryShift
import ZiskFv.EquivCore.WriteValueProofs.SailBridge
import ZiskFv.EquivCore.Bridge.BinaryExtension
import ZiskFv.EquivCore.Promises.ShiftImm
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 SLLI (immediate sibling of SLL).

Mirrors `Equivalence.Sll` structurally, with the Sail instruction
swapped for `instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)`.

**Note on bus shape.** Sail's `execute_SHIFTIOP` has a single register
read (of `rs1`) whereas the Main-AIR emission pattern used by
`bus_effect_matches_sail_alu_rrw` supplies three memory-bus entries
(two reads + one write). The equivalence theorem here reuses the
three-entry interface: the caller supplies `[e0, e1, e2]` and the
downstream bus-emission audit must justify the second read
(`e1`) as a redundant re-read of `rs1` (or prove the actual Zisk
microinstruction emits only one memory-bus read, in which case a new
shape-variant lemma is needed). We keep the archetype
interface uniform with SLL / SRLW; audit flag surfaces in
`docs/fv/trusted-base.md`.
-/

namespace ZiskFv.EquivCore.Slli

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Slli


/-- **Sail-level companion.** Wraps
    `PureSpec.execute_SHIFTIOP_slli_pure_equiv`. -/
lemma equiv_SLLI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slli_input.r1_val state)
    (h_input_shamt : slli_input.shamt = shamt)
    (h_input_rd : slli_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slli_input.PC) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
      = let slli_output := PureSpec.execute_SHIFTIOP_slli_pure slli_input
        (do
          Sail.writeReg Register.nextPC slli_output.nextPC
          match slli_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIOP_slli_pure_equiv
    slli_input r1 rd shamt h_input_r1 h_input_shamt h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SLLI equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.BinaryShift.h_rd_val_shift_slli` discharge lemma. -/
theorem equiv_SLLI_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Discharge parameters
    -- Discharge parameters
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (_h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_op_is_shift : v.op_is_shift r_binary = 1) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
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
  have h_op : (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL := by
    rw [← h_op_fgl, h_main_op]; decide
  -- Discharge c-lo/c-hi sum bounds from row-level axioms.
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      m v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      m v r_main r_binary h_match_chi
  -- Discharge h_input_r1_circuit + h_shift_pin via SailStateBridge + transpile_SLLI
  -- + matches_entry projection (m32 = 0; op_is_shift = 1).
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, _h_b_hi_t⟩ :=
    transpile_SLLI m r_main (regidx_to_fin r1) (regidx_to_fin rd) shamt
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op
  have h_input_r1_circuit :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0
      m v r_main r_binary (regidx_to_fin r1) slli_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1 h_op_is_shift h_match
  have h_shift_pin_shamt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_immediate_eq_of_shift_match
      m v r_main r_binary shamt h_b_lo_t h_op_is_shift h_match
  have h_shift_pin : slli_input.shamt.toNat = (v.free_in_b r_binary).val % 64 := by
    rw [h_input_shamt]; exact h_shift_pin_shamt
  -- Derive 8 e2 byte ranges from `memory_bus_entry_byte_range_perm_sound`.
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  -- Derive the 8 a-byte ranges + 16 c-byte 32-bit ranges from
  -- `binary_extension_columns_in_range` (BinaryExtension AIR's
  -- range-check soundness axiom on the trust ledger). This discharges
  -- the 17 per-byte *promise hypotheses* without any caller obligation.
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, _hb,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
          hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, _, _⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_columns_in_range v r_binary
  have h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary :=
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
  set shift : ℕ := slli_input.shamt.toNat with h_shift_def
  have h_discharge :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryShift.h_rd_val_shift_slli
      m v r_main r_binary e2 slli_input.r1_val shift h_op h_bytes h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.EquivCore.WriteValueProofs.SailBridge.sail_slli_bridge
      slli_input.r1_val slli_input.shamt shift h_shift_def
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_SHIFTIOP_pure slli_input.r1_val slli_input.shamt sop.SLLI := by
    rw [h_discharge, h_bridge]
  rw [equiv_SLLI_sail state slli_input r1 rd shamt
        h_input_r1 h_input_shamt h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_SHIFTIOP_slli_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- Canonical SLLI equivalence. The signature is unchanged; this legacy route
    derives BinaryExtension table well-formedness and `op_is_shift` through the
    existing table-consumer theorem, then delegates to `equiv_SLLI_of_wf`. -/
theorem equiv_SLLI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes :=
    ⟨ ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e0 h_bytes.h0.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e1 h_bytes.h1.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e2 h_bytes.h2.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e3 h_bytes.h3.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e4 h_bytes.h4.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e5 h_bytes.h5.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e6 h_bytes.h6.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e7 h_bytes.h7.1 ⟩
  have h_op_is_shift_fact :=
    ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SLL := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift r_binary = 1 :=
    h_op_is_shift_fact.1 (Or.inl h_op_v_eq)
  exact equiv_SLLI_of_wf state slli_input r1 rd shamt m v r_main r_binary bus
    promises ⟨h_main_active, h_main_op⟩ h_match h_lane_rd h_bytes h_wfs h_op_is_shift

end ZiskFv.EquivCore.Slli
