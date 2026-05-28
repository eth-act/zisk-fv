import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Sub
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.sub
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALURTypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.Arith
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 SUB. Mirrors
`Equivalence.MulH` / `Equivalence.Shift` shape:

* `transpile_SUB` (opcode 11) in place of `transpile_ADD` (opcode 10);
* `PureSpec.execute_RTYPE_sub_pure` / `execute_RTYPE_sub_pure_equiv`

* `sub_compositional` (the archetype specialization at `OP_SUB`) in
  place of `add_compositional`.

Two canonical theorems:

* `equiv_SUB_sail` — Sail-level: `execute_instruction` reduces to the
  pure-spec block.
* `equiv_SUB` — canonical shape, discharged via shape
  (a) bus-emission (`bus_effect_matches_sail_alu_rrw`).
-/

namespace ZiskFv.EquivCore.Sub

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Sub
open ZiskFv.Tactics.ALURTypeArchetype


/-- **Sail-level companion.** `execute_instruction` on an RV64 SUB
    reduces to `PureSpec.execute_RTYPE_sub_pure`. Wraps
    `PureSpec.execute_RTYPE_sub_pure_equiv`. -/
lemma equiv_SUB_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sub_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sub_input.r2_val state)
    (h_input_rd : sub_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sub_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = let sub_output := PureSpec.execute_RTYPE_sub_pure sub_input
        (do
          Sail.writeReg Register.nextPC sub_output.nextPC
          match sub_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_sub_pure_equiv
    sub_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- Variant of `equiv_SUB` whose BinaryTable byte-chain hypotheses carry
    static-provider `wf_properties` facts instead of multiplicity-based table
    consumer facts. This is the opcode-core bridge needed by the C7 static
    BinaryTable route. -/
theorem equiv_SUB_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Binary AIR provider witness + row index + activation/op + bus match.
    -- Together these replace the 16 loose a_i/b_i quantifiers, 16 byte-range
    -- hypotheses, and 2 input-bridge promise hypotheses from origin/main.
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r_binary : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    -- Loose output bytes c_i and per-byte carry/flag/pos quantifiers stay;
    -- the rd-value derivation lemma consumes them as-is.
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) c3 cin3 fl3 pi3)
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) c4 cin4 fl4 pi4)
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) c5 cin5 fl5 pi5)
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) c6 cin6 fl6 pi6)
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) c7 cin7 fl7 pi7)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1) (h_pi7 : pi7.val = 1)
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sub⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- 8 e2 byte-range *promise hypotheses* discharged via the
  -- memory-bus byte-range axiom (`Bridge.Binary.e2_byte_ranges_discharge`).
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
  have ha0 : (v.free_in_a_0 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_0
    rw [← h_a]; exact h_wf.1.1
  have ha1 : (v.free_in_a_1 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_1
    rw [← h_a]; exact h_wf.1.1
  have ha2 : (v.free_in_a_2 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_2
    rw [← h_a]; exact h_wf.1.1
  have ha3 : (v.free_in_a_3 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_3
    rw [← h_a]; exact h_wf.1.1
  have ha4 : (v.free_in_a_4 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_4
    rw [← h_a]; exact h_wf.1.1
  have ha5 : (v.free_in_a_5 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_5
    rw [← h_a]; exact h_wf.1.1
  have ha6 : (v.free_in_a_6 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_6
    rw [← h_a]; exact h_wf.1.1
  have ha7 : (v.free_in_a_7 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_7
    rw [← h_a]; exact h_wf.1.1
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_0
    rw [← h_b]; exact h_wf.1.2.1
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_1
    rw [← h_b]; exact h_wf.1.2.1
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_2
    rw [← h_b]; exact h_wf.1.2.1
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_3
    rw [← h_b]; exact h_wf.1.2.1
  have hb4 : (v.free_in_b_4 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_4
    rw [← h_b]; exact h_wf.1.2.1
  have hb5 : (v.free_in_b_5 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_5
    rw [← h_b]; exact h_wf.1.2.1
  have hb6 : (v.free_in_b_6 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_6
    rw [← h_b]; exact h_wf.1.2.1
  have hb7 : (v.free_in_b_7 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_7
    rw [← h_b]; exact h_wf.1.2.1
  -- Input bridges derived from `transpile_SUB` (state-bridged via
  -- `SailStateBridge`) plus `matches_entry`'s a-/b-lane
  -- conjuncts (m32 = 0 collapses the high-lane disjunction). Replaces
  -- the two `h_input_r{1,2}_circuit` *promise hypotheses*.
  have h_input_r1_circuit : sub_input.r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
    obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, _, _⟩ :=
      transpile_SUB m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
        (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
        h_main_active h_main_op_sub
    have h_r1_main :=
      ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r1) sub_input.r1_val (m.a_0 r_main) (m.a_1 r_main)
        h_a_lo_t h_a_hi_t h_input_r1
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd,
               opBus_row_Binary] at h_lane_eqs
    obtain ⟨_, _, h_a_lo_m, h_a_hi_m, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [h_m32] at h_a_hi_m
    simp only [one_sub_zero_mul] at h_a_hi_m
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
    have h_a1_val : (m.a_1 r_main).val =
        (v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
        + (v.free_in_a_6 r_binary).val * 65536 + (v.free_in_a_7 r_binary).val * 16777216 := by
      rw [h_a_hi_m]
      have h_cast :
          v.free_in_a_4 r_binary + 256 * v.free_in_a_5 r_binary
            + 65536 * v.free_in_a_6 r_binary + 16777216 * v.free_in_a_7 r_binary
          = ((((v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
                + (v.free_in_a_6 r_binary).val * 65536
                + (v.free_in_a_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
        push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    rw [h_r1_main]
    apply congrArg (BitVec.ofNat 64)
    rw [h_a0_val, h_a1_val]
    ring
  have h_input_r2_circuit : sub_input.r2_val
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536 + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936) := by
    obtain ⟨_, h_m32, _, _, _, _, _, _, h_b_lo_t, h_b_hi_t⟩ :=
      transpile_SUB m r_main (regidx_to_fin r1) (regidx_to_fin r2) (regidx_to_fin rd)
        (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
        h_main_active h_main_op_sub
    have h_r2_main :=
      ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r2) sub_input.r2_val (m.b_0 r_main) (m.b_1 r_main)
        h_b_lo_t h_b_hi_t h_input_r2
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd,
               opBus_row_Binary] at h_lane_eqs
    obtain ⟨_, _, _, _, h_b_lo_m, h_b_hi_m, _, _, _, _, _, _⟩ := h_lane_eqs
    rw [h_m32] at h_b_hi_m
    simp only [one_sub_zero_mul] at h_b_hi_m
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
    have h_b1_val : (m.b_1 r_main).val =
        (v.free_in_b_4 r_binary).val + (v.free_in_b_5 r_binary).val * 256
        + (v.free_in_b_6 r_binary).val * 65536 + (v.free_in_b_7 r_binary).val * 16777216 := by
      rw [h_b_hi_m]
      have h_cast :
          v.free_in_b_4 r_binary + 256 * v.free_in_b_5 r_binary
            + 65536 * v.free_in_b_6 r_binary + 16777216 * v.free_in_b_7 r_binary
          = ((((v.free_in_b_4 r_binary).val + (v.free_in_b_5 r_binary).val * 256
                + (v.free_in_b_6 r_binary).val * 65536
                + (v.free_in_b_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
        push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    rw [h_r2_main]
    apply congrArg (BitVec.ofNat 64)
    rw [h_b0_val, h_b1_val]
    ring
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.Arith.h_rd_val_arith_sub_of_wf
      m r_main e2 sub_input.r1_val sub_input.r2_val
      (v.free_in_a_0 r_binary) (v.free_in_a_1 r_binary) (v.free_in_a_2 r_binary) (v.free_in_a_3 r_binary)
      (v.free_in_a_4 r_binary) (v.free_in_a_5 r_binary) (v.free_in_a_6 r_binary) (v.free_in_a_7 r_binary)
      (v.free_in_b_0 r_binary) (v.free_in_b_1 r_binary) (v.free_in_b_2 r_binary) (v.free_in_b_3 r_binary)
      (v.free_in_b_4 r_binary) (v.free_in_b_5 r_binary) (v.free_in_b_6 r_binary) (v.free_in_b_7 r_binary)
      c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
      fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
      pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
      h_pi0 h_pi1 h_pi2 h_pi3 h_pi4 h_pi5 h_pi6 h_pi7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_r2_circuit
  rw [equiv_SUB_sail state sub_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_sub_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- Static-provider BinaryTable route for `equiv_SUB`.

    The table lookup itself is discharged through Clean static-table
    `wf_properties` facts. The 64-bit mode/op pins are still explicit because
    they are row-shape facts, not consequences of table membership. -/
theorem equiv_SUB_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (r_main r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_core : ZiskFv.Airs.Binary.core_every_row v r_binary)
    (h_mode32_zero : v.mode32 r_binary = 0)
    (h_b_op : (v.b_op r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sub⟩ := pins
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_lookup
      v r_binary offset env h_static
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB h_core h_mode32_zero h_b_op
  have h_carry_7_zero :=
    ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_SUB_of_static_chain
      v r_binary out h_core.2.1
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, _, _, h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_lane_eqs
  have h_match_clo :
      m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
        + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero]
    ring
  have h_match_chi :
      m.c_1 r_main = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
        + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216 := by
    rw [h_c_hi_m]
    ring
  exact ZiskFv.EquivCore.Sub.equiv_SUB_of_wf
    state sub_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_binary
    ⟨h_main_active, h_main_op_sub⟩
    h_match
    (v.free_in_c_0 r_binary) (v.free_in_c_1 r_binary) (v.free_in_c_2 r_binary)
    (v.free_in_c_3 r_binary) (v.free_in_c_4 r_binary) (v.free_in_c_5 r_binary)
    (v.free_in_c_6 r_binary) (v.free_in_c_7 r_binary)
    (0 : FGL) (v.carry_0 r_binary) (v.carry_1 r_binary) (v.carry_2 r_binary)
    (v.carry_3 r_binary) (v.carry_4 r_binary) (v.carry_5 r_binary) (v.carry_6 r_binary)
    (v.carry_0 r_binary) (v.carry_1 r_binary) (v.carry_2 r_binary) (v.carry_3 r_binary)
    (v.carry_4 r_binary) (v.carry_5 r_binary) (v.carry_6 r_binary) (v.carry_7 r_binary)
    (2 * v.use_first_byte r_binary) (0 : FGL) (0 : FGL) (v.mode32 r_binary)
    (0 : FGL) (0 : FGL) (0 : FGL) (1 - v.mode32 r_binary)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.c0_lt out.c1_lt out.c2_lt out.c3_lt out.c4_lt out.c5_lt out.c6_lt out.c7_lt
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_ne
    out.pi4_ne out.pi5_ne out.pi6_ne out.pi7_eq
    h_match_clo h_match_chi h_lane_rd

/-- Row-native static-provider BinaryTable route for `equiv_SUB`. -/
theorem equiv_SUB_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_zero : row.mode.mode32 = 0)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_sub⟩ := pins
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_SUB h_core
      h_mode32_zero h_b_op
  have h_carry_7_zero :=
    ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_SUB_of_static_chain
      v 0 out h_core.2.1
  have h_lane_eqs := h_match_v
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, _, _, h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_lane_eqs
  have h_match_clo :
      m.c_0 r_main = v.free_in_c_0 0 + v.free_in_c_1 0 * 256
        + v.free_in_c_2 0 * 65536 + v.free_in_c_3 0 * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero]
    ring
  have h_match_chi :
      m.c_1 r_main = v.free_in_c_4 0 + v.free_in_c_5 0 * 256
        + v.free_in_c_6 0 * 65536 + v.free_in_c_7 0 * 16777216 := by
    rw [h_c_hi_m]
    ring
  exact ZiskFv.EquivCore.Sub.equiv_SUB_of_wf
    state sub_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v 0
    ⟨h_main_active, h_main_op_sub⟩
    h_match_v
    (v.free_in_c_0 0) (v.free_in_c_1 0) (v.free_in_c_2 0)
    (v.free_in_c_3 0) (v.free_in_c_4 0) (v.free_in_c_5 0)
    (v.free_in_c_6 0) (v.free_in_c_7 0)
    (0 : FGL) (v.carry_0 0) (v.carry_1 0) (v.carry_2 0)
    (v.carry_3 0) (v.carry_4 0) (v.carry_5 0) (v.carry_6 0)
    (v.carry_0 0) (v.carry_1 0) (v.carry_2 0) (v.carry_3 0)
    (v.carry_4 0) (v.carry_5 0) (v.carry_6 0) (v.carry_7 0)
    (2 * v.use_first_byte 0) (0 : FGL) (0 : FGL) (v.mode32 0)
    (0 : FGL) (0 : FGL) (0 : FGL) (1 - v.mode32 0)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.c0_lt out.c1_lt out.c2_lt out.c3_lt out.c4_lt out.c5_lt out.c6_lt out.c7_lt
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_ne
    out.pi4_ne out.pi5_ne out.pi6_ne out.pi7_eq
    h_match_clo h_match_chi h_lane_rd

end ZiskFv.EquivCore.Sub
