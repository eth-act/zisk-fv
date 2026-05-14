import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.Circuit.Addw
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.addw
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.RTypeWArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.WriteValueProofs.Arith
import ZiskFv.Equivalence.WriteValueProofs.SailBridge
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Equivalence.Bridge.Binary
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges

/-!
End-to-end theorem for RV64 ADDW. Mirrors the shape
of `Equivalence.Sub` / `Equivalence.MulW` with:

* `transpile_ADDW` (opcode `OP_ADD_W = 26`, `m32 = 1`);
* `PureSpec.execute_RTYPE_addw_pure` / `execute_RTYPE_addw_pure_equiv`;
* `addw_compositional` (the RTypeWArchetype specialization at
  `OP_ADD_W`).

Three canonical theorems:

* `equiv_ADDW_circuit` — circuit-level: Main's packed `c` equals the bus
  entry's packed `c`.
* `equiv_ADDW_sail` — Sail-level: `execute_instruction` reduces to
  the pure-spec block.
* `equiv_ADDW` — canonical shape, discharged via
  shape (a) bus-emission (`bus_effect_matches_sail_alu_rrw` —
  register-read + register-read + register-write, same as
  SUB/MUL/MULW).
-/

namespace ZiskFv.Equivalence.Addw

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Addw
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDW
    reduces to `PureSpec.execute_RTYPE_addw_pure`. Wraps
    `PureSpec.execute_RTYPE_addw_pure_equiv`. -/
lemma equiv_ADDW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok addw_input.r2_val state)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = let addw_output := PureSpec.execute_RTYPE_addw_pure addw_input
        (do
          Sail.writeReg Register.nextPC addw_output.nextPC
          match addw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_addw_pure_equiv
    addw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    ADDW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.Arith.h_rd_val_arith_addw` discharge lemma
    composed with `SailBridge.sail_addw_bridge`. -/
theorem equiv_ADDW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok addw_input.r2_val state)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Binary AIR provider witness + activation/op + matches_entry.
    -- Replaces 8 loose a_i/b_i quantifiers, 8 byte-range hypotheses
    -- (ha0..ha3, hb0..hb3), and 2 input-bridge promise hypotheses.
    (v : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL) (r_binary : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addw : m.op r_main = OP_ADD_W)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_ADD
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_ADD
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_ADD
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_ADD
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) c3 cin3 fl3 pi3)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val = 1)
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648))
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- 8 e2 byte-range *promise hypotheses* discharged via
  -- `Bridge.Binary.e2_byte_ranges_discharge`.
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Equivalence.Bridge.Binary.e2_byte_ranges_discharge e2
  have ha0 : (v.free_in_a_0 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_0_lt_256 v r_binary
  have ha1 : (v.free_in_a_1 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_1_lt_256 v r_binary
  have ha2 : (v.free_in_a_2 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_2_lt_256 v r_binary
  have ha3 : (v.free_in_a_3 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_3_lt_256 v r_binary
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_0_lt_256 v r_binary
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_1_lt_256 v r_binary
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_2_lt_256 v r_binary
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_3_lt_256 v r_binary
  -- Input bridges: derive `h_input_r{1,2}_extract` (low-32-bit extract
  -- form) from `transpile_ADDW` + Step 1.7b SailStateBridge +
  -- `matches_entry`'s a_lo/b_lo conjuncts. Mirrors SUBW's derivation
  -- (W-variants share the same row contract modulo opcode literal).
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
          + (v.free_in_a_2 r_binary).val * 65536
          + (v.free_in_a_3 r_binary).val * 16777216) % 2^32 := by
    obtain ⟨_, _, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
      transpile_ADDW m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
        (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
        h_main_active h_main_op_addw
    have h_r1_main :=
      ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r1) addw_input.r1_val (m.a_0 r_main) (m.a_1 r_main)
        h_a_lo_t h_a_hi_t h_input_r1
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
    obtain ⟨_, _, h_a_lo_m, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    have h_a0_val : (m.a_0 r_main).val =
        (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216 := by
      rw [h_a_lo_m]
      have h_cast :
          v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
            + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary
          = ((((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
                + (v.free_in_a_2 r_binary).val * 65536
                + (v.free_in_a_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
        push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    rw [h_r1_main]
    have h_byte_lt : (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
                     + (v.free_in_a_2 r_binary).val * 65536
                     + (v.free_in_a_3 r_binary).val * 16777216 < 4294967296 := by omega
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
               BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.shiftRight_zero,
               show (31 - 0 + 1 : ℕ) = 32 from rfl,
               show (2:ℕ)^32 = 4294967296 from rfl,
               show (2:ℕ)^64 = 18446744073709551616 from rfl]
    rw [h_a0_val]
    omega
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
          + (v.free_in_b_2 r_binary).val * 65536
          + (v.free_in_b_3 r_binary).val * 16777216) % 2^32 := by
    obtain ⟨_, _, _, _, _, _, _, _, h_b_lo_t, h_b_hi_t⟩ :=
      transpile_ADDW m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
        (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
        h_main_active h_main_op_addw
    have h_r2_main :=
      ZiskFv.Equivalence.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r2) addw_input.r2_val (m.b_0 r_main) (m.b_1 r_main)
        h_b_lo_t h_b_hi_t h_input_r2
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
    obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
    have h_b0_val : (m.b_0 r_main).val =
        (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
        + (v.free_in_b_2 r_binary).val * 65536 + (v.free_in_b_3 r_binary).val * 16777216 := by
      rw [h_b_lo_m]
      have h_cast :
          v.free_in_b_0 r_binary + 256 * v.free_in_b_1 r_binary
            + 65536 * v.free_in_b_2 r_binary + 16777216 * v.free_in_b_3 r_binary
          = ((((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
                + (v.free_in_b_2 r_binary).val * 65536
                + (v.free_in_b_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
        push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    rw [h_r2_main]
    have h_byte_lt : (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
                     + (v.free_in_b_2 r_binary).val * 65536
                     + (v.free_in_b_3 r_binary).val * 16777216 < 4294967296 := by omega
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
               BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.shiftRight_zero,
               show (31 - 0 + 1 : ℕ) = 32 from rfl,
               show (2:ℕ)^32 = 4294967296 from rfl,
               show (2:ℕ)^64 = 18446744073709551616 from rfl]
    rw [h_b0_val]
    omega
  set a32sum : ℕ := (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
                  + (v.free_in_a_2 r_binary).val * 65536
                  + (v.free_in_a_3 r_binary).val * 16777216 with h_a32_def
  set b32sum : ℕ := (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
                  + (v.free_in_b_2 r_binary).val * 65536
                  + (v.free_in_b_3 r_binary).val * 16777216 with h_b32_def
  have h_discharge :=
    ZiskFv.Equivalence.WriteValueProofs.Arith.h_rd_val_arith_addw
      m r_main e2
      (v.free_in_a_0 r_binary) (v.free_in_a_1 r_binary)
      (v.free_in_a_2 r_binary) (v.free_in_a_3 r_binary)
      (v.free_in_b_0 r_binary) (v.free_in_b_1 r_binary)
      (v.free_in_b_2 r_binary) (v.free_in_b_3 r_binary)
      c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 fl0 fl1 fl2 fl3 pi0 pi1 pi2 pi3
      h_byte_0 h_byte_1 h_byte_2 h_byte_3
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_cin0 h_cin1 h_cin2 h_cin3
      h_pi0 h_pi1 h_pi2 h_pi3 h_sext_choice
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      a32sum b32sum h_a32_def h_b32_def
  have h_bridge :=
    ZiskFv.Equivalence.WriteValueProofs.SailBridge.sail_addw_bridge
      addw_input.r1_val addw_input.r2_val a32sum b32sum
      (h_input_r1_extract.trans (by rw [h_a32_def]))
      (h_input_r2_extract.trans (by rw [h_b32_def]))
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure addw_input.r1_val addw_input.r2_val ropw.ADDW := by
    rw [h_discharge, h_bridge]
  rw [equiv_ADDW_sail state addw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_addw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Addw
