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
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Equivalence.WriteValueProofs.BinaryShift
import ZiskFv.Equivalence.WriteValueProofs.SailBridge
import ZiskFv.Equivalence.Bridge.BinaryExtension

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

namespace ZiskFv.Equivalence.Sll

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Sll

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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
    17 *promise hypotheses* dropped from caller burden — `h_a_range`
    (8 a-byte ranges, as a single bundled struct binder) + 16 c-byte
    32-bit range hypotheses (`hc_lo_0..7`, `hc_hi_0..7`) — all derived
    inside the proof from
    `ZiskFv.Airs.BinaryExtension.binary_extension_columns_in_range`
    (BinaryExtension AIR's range-check soundness axiom). Sum bounds
    `hc_{lo,hi}_sum_lt` are genuinely stronger than per-byte ranges
    (sum of 8×32-bit can overflow 2^32) and remain caller-supplied
    until a follow-up consumes `h_match_clo`/`h_match_chi` +
    `main_columns_in_range`. Net: 17 binders removed, none added. -/
theorem equiv_SLL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sll_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sll_input.r2_val state)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sll_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sll_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Project matches_entry into the (op, c_lo, c_hi) sub-facts the proof
  -- body consumes.
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  have h_op : (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL := by
    rw [← h_op_fgl, h_main_op]; decide
  -- Discharge c-lo/c-hi sum bounds from the projected match equations
  -- plus `main_columns_in_range` + `binary_extension_columns_in_range`.
  have hc_lo_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      m v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      m v r_main r_binary h_match_chi
  -- Discharge h_bytes via the BinaryExtension row → 8-byte table-entry axiom.
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- Derive op_is_shift = 1 from the BinaryExtension AIR op_is_shift pin.
  have h_op_is_shift_fact :=
    ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SLL := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift r_binary = 1 :=
    h_op_is_shift_fact.1 (Or.inl h_op_v_eq)
  -- Discharge h_input_r1_circuit via the SailStateBridge + transpile_SLL
  -- + matches_entry's `a_lo`/`a_hi` projection (with m32 = 0 collapse and
  -- op_is_shift = 1 collapse).
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, h_b_hi_t⟩ :=
    transpile_SLL m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op
  have h_input_r1_circuit :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0
      m v r_main r_binary (regidx_to_fin r1) sll_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1_sail h_op_is_shift h_match
  have h_shift_pin :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.shift_pin_eq_of_shift_match_m32_0
      m v r_main r_binary (regidx_to_fin r2) sll_input.r2_val
      h_m32 h_b_lo_t h_b_hi_t h_input_r2_sail h_op_is_shift h_match
  -- Derive 8 e2 byte ranges from `memory_bus_entry_byte_range_perm_sound`.
  -- Net **−8 binders** on `equiv_SLL` (h_e2_0..h_e2_7 removed; no new
  -- caller obligations added — the trust footprint shrinks).
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  -- Derive the 8 a-byte ranges + 16 c-byte 32-bit ranges from
  -- `binary_extension_columns_in_range`. This discharges the 17
  -- per-byte *promise hypotheses* without any caller obligation.
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, _hb,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
          hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, _, _⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_columns_in_range v r_binary
  have h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary :=
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
  set shift : ℕ := sll_input.r2_val.toNat % 64 with h_shift_def
  have h_discharge :=
    ZiskFv.Equivalence.WriteValueProofs.BinaryShift.h_rd_val_shift_sll
      m v r_main r_binary e2 sll_input.r1_val shift h_op h_bytes h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.Equivalence.WriteValueProofs.SailBridge.sail_sll_bridge
      sll_input.r1_val sll_input.r2_val shift h_shift_def
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPE_pure sll_input.r1_val sll_input.r2_val rop.SLL := by
    rw [h_discharge, h_bridge]
  rw [equiv_SLL_sail state sll_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
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

end ZiskFv.Equivalence.Sll
