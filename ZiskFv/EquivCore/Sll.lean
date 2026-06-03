import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.ZiskCircuit.Sll
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.sll
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.EquivCore.WriteValueProofs.BinaryShift
import ZiskFv.EquivCore.WriteValueProofs.SailBridge
import ZiskFv.EquivCore.Bridge.BinaryExtension
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 SLL (64-bit sibling of SLLW).

Mirrors `Equivalence.Shift` (SLLW), with the direction unchanged but
the width flag flipped: `m32 = 0` here instead of `m32 = 1`. The
Main-AIR compositional lemma is the `ShiftArchetype` **passthrough**
instantiation at `OP_SLL = 33` — the high lanes `a_hi` / `b_hi` flow
verbatim to the `BinaryExtension` SM rather than being zeroed.

Emits three theorems matching the SLLW trio:

* `equiv_SLL_sail` — Sail-level: `execute_instruction` on a SLL RTYPE
  reduces to the pure spec block.
* `equiv_SLL` — canonical fused theorem. Derives `h_rd_val`
  internally via `WriteValueProofs.BinaryShift.h_rd_val_shift_sll`
  + `WriteValueProofs.SailBridge.sail_sll_bridge`.
-/

namespace ZiskFv.EquivCore.Sll

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Sll
open ZiskFv.Channels.MemoryBusBytes (byteAt)


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SLL reduces to the pure-function block. Wraps
    `PureSpec.execute_RTYPE_sll_pure_equiv`. -/
lemma equiv_SLL_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sll_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sll_input.r2_val state)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sll_input.PC) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = let sll_output := PureSpec.execute_RTYPE_sll_pure sll_input
        (do
          Sail.writeReg Register.nextPC sll_output.nextPC
          match sll_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_sll_pure_equiv
    sll_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SLL equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.BinaryShift.h_rd_val_shift_sll` discharge lemma.

    **Canonical exemplar for the BinaryExtension shape.**
    The a-byte ranges, c-lane ranges, and c-lane sum bounds are all derived
    from the exact static BinaryExtensionTable row facts threaded through the
    Clean shift provider. SLL therefore no longer consumes the legacy generic
    range-bus soundness axiom. -/
lemma equiv_SLL_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_input_r1_circuit :
      sll_input.r1_val = ZiskFv.AirsClean.BinaryExtension.validA64 v r_binary)
    (h_shift_pin :
      sll_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.validShiftAmount v r_binary)
    (h_b0_range : (v.b_0 r_binary).val < 2 ^ 24) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- Project matches_entry into the (op, c_lo, c_hi) sub-facts the proof
  -- body consumes.
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  have h_op : (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL := by
    rw [← h_op_fgl, h_main_op]; decide
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
  -- Derive 8 e2 byte ranges from `byteAt_val_lt_256` (chunk-shape
  -- replacement for the retired memory_bus_entry_byte_range_perm_sound
  -- axiom). Net **−8 binders** on `equiv_SLL`.
  have h_e2_0 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 0
  have h_e2_1 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 1
  have h_e2_2 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 2
  have h_e2_3 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 3
  have h_e2_4 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 4
  have h_e2_5 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 5
  have h_e2_6 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 6
  have h_e2_7 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 7
  -- Derive the c-byte ranges and c-lane sum bounds from the exact static
  -- BinaryExtensionTable rows, with no range-bus axiom.
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
          hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_sll_c_lanes_lt_of_wf
      v r_binary h_op h_bytes h_wfs
  obtain ⟨hc_lo_sum_lt, hc_hi_sum_lt⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_sll_c_sums_lt_of_wf
      v r_binary h_op h_bytes h_wfs h_a_range
  set shift : ℕ := sll_input.r2_val.toNat % 64 with h_shift_def
  have h_discharge :=
    ZiskFv.EquivCore.WriteValueProofs.BinaryShift.h_rd_val_shift_sll_of_wf
      m v r_main r_binary e2 sll_input.r1_val shift h_op h_bytes h_wfs h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.EquivCore.WriteValueProofs.SailBridge.sail_sll_bridge
      sll_input.r1_val sll_input.r2_val shift h_shift_def
  have h_rd_val : U64.toBV #v[byteAt e2 0, byteAt e2 1, byteAt e2 2, byteAt e2 3,
                              byteAt e2 4, byteAt e2 5, byteAt e2 6, byteAt e2 7]
      = execute_RTYPE_pure sll_input.r1_val sll_input.r2_val rop.SLL := by
    rw [h_discharge, h_bridge]
  rw [equiv_SLL_sail state sll_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_sll_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

-- legacy `equiv_SLL` (bin_ext_table_consumer_wf route) deleted in T4-purge P3.3.

lemma equiv_SLL_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_input_r1_row : sll_input.r1_val = ZiskFv.AirsClean.BinaryExtension.rowA64 row)
    (h_shift_pin_row :
      sll_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount row)
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
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
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SLL := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inl h_op_v_eq)
  exact equiv_SLL_of_wf state sll_input r1 r2 rd m v r_main 0 bus
    promises ⟨h_main_active, h_main_op⟩ h_match_v h_lane_rd
    h_bytes h_wfs h_op_is_shift
    (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validA64,
        ZiskFv.AirsClean.BinaryExtension.rowA64,
        ZiskFv.AirsClean.BinaryExtension.validOfRow]
      using h_input_r1_row)
    (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validShiftAmount,
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount,
        ZiskFv.AirsClean.BinaryExtension.validOfRow]
      using h_shift_pin_row)
    (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range)

end ZiskFv.EquivCore.Sll
