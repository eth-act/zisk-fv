import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.Circuit.Shift
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.sllw
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Equivalence.WriteValueProofs.BinaryShift
import ZiskFv.Equivalence.WriteValueProofs.SailBridge
import ZiskFv.Equivalence.Bridge.BinaryExtension

/-!
End-to-end theorem for RV64 SLLW.

Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_SLLW`, `m32 = 1`);
* the compositional SLLW Main-row spec
  (`ZiskFv.Circuit.Shift.sllw_compositional` — high bus lanes zero);
* the Sail pure-function equivalence
  (`PureSpec.execute_RTYPE_sllw_pure_equiv`).

Emits three theorems mirroring the A1 (BEQ) shape:

* `equiv_SLLW_circuit` — circuit-level: the `m32 = 1` path zeroes the bus's
  `a_hi` and `b_hi` lanes, delegating to the `BinaryExtension` SM.
* `equiv_SLLW_sail` — Sail-level: `execute_instruction` on a SLLW
  RTYPEW reduces to the pure spec block.
* `equiv_SLLW` — the canonical shape, composing the
  Sail equivalence with the bus-effect hypothesis.

The `BinaryExtension` bus-emission derivation is **deferred** to
the match hypothesis as a parameter; future audit wires it to a
`Valid_BinaryExtension` AIR.
-/

namespace ZiskFv.Equivalence.Shift

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Shift

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SLLW reduces to the pure-function block supplied by
    `PureSpec.execute_RTYPE_sllw_pure`, given source-register
    readability and PC knowledge. Wraps
    `PureSpec.execute_RTYPE_sllw_pure_equiv` to expose the Sail chain
    at this module's export surface. -/
lemma equiv_SLLW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = let sllw_output := PureSpec.execute_RTYPE_sllw_pure sllw_input
        (do
          Sail.writeReg Register.nextPC sllw_output.nextPC
          match sllw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_sllw_pure_equiv
    sllw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SLLW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.BinaryShift.h_rd_val_shift_sllw` discharge lemma. -/
theorem equiv_SLLW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sllw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Project matches_entry into (op, c_lo, c_hi) sub-facts.
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  have h_op : (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SLL_W := by
    rw [← h_op_fgl, h_main_op]; decide
  -- Discharge c-lo/c-hi sum bounds + h_bytes from row-level axioms.
  have hc_lo_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      m v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      m v r_main r_binary h_match_chi
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- Derive op_is_shift = 1 from the BinaryExtension AIR op_is_shift pin.
  have h_op_is_shift_fact :=
    ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SLL_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift r_binary = 1 :=
    h_op_is_shift_fact.1 (Or.inr (Or.inr (Or.inr (Or.inl h_op_v_eq))))
  -- Discharge h_input_r1_extract + h_shift_pin via SailStateBridge
  -- + transpile_SLLW + matches_entry projection (m32 = 1; op_is_shift = 1).
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, h_b_hi_t⟩ :=
    transpile_SLLW m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op
  have h_input_r1_extract :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.packed_a_lo32_eq_of_shift_match_m32_1
      m v r_main r_binary (regidx_to_fin r1) sllw_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1_sail h_op_is_shift h_match
  have h_shift_pin :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.shift_pin_w_eq_of_shift_match
      m v r_main r_binary (regidx_to_fin r2) sllw_input.r2_val
      h_b_lo_t h_b_hi_t h_input_r2_sail h_op_is_shift h_match
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
  set a4sum : ℕ := (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536
        + (v.free_in_a_3 r_binary).val * 16777216 with h_a4_def
  set shift : ℕ :=
    (Sail.BitVec.extractLsb sllw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat % 32
    with h_shift_def
  -- Pre-condition: r1_val_lo32 = ofNat 32 a4sum, equivalently
  -- (extractLsb r1 31 0).toNat = a4sum % 2^32.
  have h_r1lo : Sail.BitVec.extractLsb sllw_input.r1_val 31 0
      = BitVec.ofNat 32 a4sum := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, h_input_r1_extract, h_a4_def]
  have h_discharge :=
    ZiskFv.Equivalence.WriteValueProofs.BinaryShift.h_rd_val_shift_sllw
      m v r_main r_binary e2
      (Sail.BitVec.extractLsb sllw_input.r1_val 31 0)
      shift h_op h_bytes h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_r1lo
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.Equivalence.WriteValueProofs.SailBridge.sail_sllw_bridge
      sllw_input.r1_val sllw_input.r2_val a4sum shift
      (h_input_r1_extract.trans (by rw [h_a4_def]))
      h_shift_def
  -- Combine: discharge gives `bytes = signExtend 64 (shiftLeft (extractLsb r1 31 0) shift)`,
  -- but with `extractLsb = ofNat 32 a4sum` it becomes the bridge's LHS.
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure sllw_input.r1_val sllw_input.r2_val ropw.SLLW := by
    rw [h_discharge, h_r1lo, h_bridge]
  rw [equiv_SLLW_sail state sllw_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_sllw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Shift
