import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Field.GoldilocksBridge
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.Add
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.EquivCore.Bridge.BinaryAdd
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.add
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.Arith
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Airs.Binary.Binary
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 ADD. Combines:

* explicit ADD source-lane and Main-row mode facts,
* the compositional ADD spec (`ZiskFv.ZiskCircuit.Add.add_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_RTYPE_add_pure_equiv`),

into two companion theorems:

* `equiv_ADD_sail` — Sail-level. States `LeanRV64D.execute_instruction`
  on an RV64 ADD reduces to a concrete monadic block writing
  `r1_val + r2_val` (BitVec 64, wraps mod 2^64) to `rd` and
  advancing `nextPC`. Discharged via `execute_RTYPE_add_pure_equiv`.
-/

namespace ZiskFv.EquivCore.Add

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Add

def binaryValidA64 (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r : ℕ) : BitVec 64 :=
  BitVec.ofNat 64
    ((v.free_in_a_0 r).val + (v.free_in_a_1 r).val * 256
      + (v.free_in_a_2 r).val * 65536 + (v.free_in_a_3 r).val * 16777216
      + (v.free_in_a_4 r).val * 4294967296
      + (v.free_in_a_5 r).val * 1099511627776
      + (v.free_in_a_6 r).val * 281474976710656
      + (v.free_in_a_7 r).val * 72057594037927936)

def binaryValidB64 (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r : ℕ) : BitVec 64 :=
  BitVec.ofNat 64
    ((v.free_in_b_0 r).val + (v.free_in_b_1 r).val * 256
      + (v.free_in_b_2 r).val * 65536 + (v.free_in_b_3 r).val * 16777216
      + (v.free_in_b_4 r).val * 4294967296
      + (v.free_in_b_5 r).val * 1099511627776
      + (v.free_in_b_6 r).val * 281474976710656
      + (v.free_in_b_7 r).val * 72057594037927936)

def binaryRowA64 (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) : BitVec 64 :=
  BitVec.ofNat 64
    ((row.aBytes.free_in_a_0).val + (row.aBytes.free_in_a_1).val * 256
      + (row.aBytes.free_in_a_2).val * 65536 + (row.aBytes.free_in_a_3).val * 16777216
      + (row.aBytes.free_in_a_4).val * 4294967296
      + (row.aBytes.free_in_a_5).val * 1099511627776
      + (row.aBytes.free_in_a_6).val * 281474976710656
      + (row.aBytes.free_in_a_7).val * 72057594037927936)

def binaryRowB64 (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) : BitVec 64 :=
  BitVec.ofNat 64
    ((row.bBytes.free_in_b_0).val + (row.bBytes.free_in_b_1).val * 256
      + (row.bBytes.free_in_b_2).val * 65536 + (row.bBytes.free_in_b_3).val * 16777216
      + (row.bBytes.free_in_b_4).val * 4294967296
      + (row.bBytes.free_in_b_5).val * 1099511627776
      + (row.bBytes.free_in_b_6).val * 281474976710656
      + (row.bBytes.free_in_b_7).val * 72057594037927936)


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an RV64
    ADD (`.RTYPE (r2, r1, rd, rop.ADD)`) reduces to the pure function
    block supplied by `PureSpec.execute_RTYPE_add_pure`, given that the
    source registers are readable and the PC is known. Wraps
    `PureSpec.execute_RTYPE_add_pure_equiv` to expose the Sail chain at
    this module's export surface, consumed by `equiv_ADD` below. -/
lemma equiv_ADD_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = let add_output := PureSpec.execute_RTYPE_add_pure add_input
        (do
          Sail.writeReg Register.nextPC add_output.nextPC
          match add_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_add_pure_equiv
    add_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.**
    Sail's `execute_instruction` on an RV64 ADD equals the state
    computed by applying `bus_effect` to the circuit's execution and
    memory bus rows.

    The cross-AIR matching (`matches_entry`), per-chunk byte ranges
    on BinaryAdd, and the per-chunk-form input bridges that pre-pilot
    `equiv_ADD` accepted as caller obligations are now derived inside
    the proof body via
    `ZiskFv.EquivCore.Bridge.BinaryAdd.add_discharge`, which
    consumes `op_bus_perm_sound_BinaryAdd` (PLONK soundness on
    `OPERATION_BUS_ID = 5000`) and `binary_add_columns_in_range`
    (range-check bus soundness on BinaryAdd's `bits(N)` columns) —
    both in the *trust ledger*.

    Net reduction in the *anti-laundering metric* vs. origin/main
    pre-discharge: −2 binders. (Further reductions possible by
    deriving `h_input_r{1,2}_main` from the narrow ADD operand bridge +
    a state bridge, or by universalizing `h_main_subset` / `h_main_mode`
    from `Valid_Main` constraints.)

    Row-explicit variant of `equiv_ADD`: caller supplies the BinaryAdd
    row witness `r_binary` and the cross-AIR `matches_entry` predicate
    directly, bypassing `op_bus_perm_sound_BinaryAdd`. This is the
    canonical proof body; `equiv_ADD` below is a thin forwarder that
    derives `r_binary` + `h_match` via the axiom. -/
lemma equiv_ADD_with_match
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (b : Valid_BinaryAdd FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_add_mode m r_main)
    (h_b_core : ZiskFv.Airs.BinaryAdd.core_every_row b r_binary)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_binary))
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_b_lo_t : m.b_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r2)))
    (h_b_hi_t : m.b_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r2)))
    (h_a_range : a_chunks_in_range b r_binary)
    (h_b_range : b_chunks_in_range b r_binary)
    (h_c_range : c_chunks_in_range b r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ := bounds
  obtain ⟨h_input_r1_sail, h_input_r2_sail, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨h_circuit, h_a_range, h_b_range, h_c_range,
          h_input_r1_circuit, h_input_r2_circuit⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryAdd.add_discharge_with_match
      m b r_main r_binary h_main_subset h_main_mode h_b_core h_match
      h_a_range h_b_range h_c_range
      state (regidx_to_fin r1) (regidx_to_fin r2)
      add_input.r1_val add_input.r2_val
      h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t
      h_input_r1_sail h_input_r2_sail
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.Arith.h_rd_val_arith_add
      m b r_main r_binary e2 add_input
      h_circuit h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a_range h_b_range h_c_range
      h_input_r1_circuit h_input_r2_circuit
  rw [equiv_ADD_sail state add_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_add_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

-- Legacy `equiv_ADD` (BinaryAdd-arm thin forwarder using
-- op_bus_perm_sound_BinaryAdd) deleted in T4-purge P3.10.

/-- **Binary-arm equiv_ADD** (T2.2 multi-provider migration).
    Takes a Valid_Binary witness with an 8-byte chain at OP_ADD and the
    op-bus matches_entry against the Binary provider's emission. Mirrors
    `equiv_SUB_of_wf` with OP_SUB → OP_ADD and subtraction → addition;
    uses explicit `m32 = 0` and source-register lane equalities. The Binary AIR
    serves 64-bit ADD as an alternate provider to BinaryAdd
    (per `binary.pil:22`, OP_ADD = 0x0A is in Binary's coverage). -/
lemma equiv_ADD_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r_binary : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (_h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) c3 cin3 fl3 pi3)
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) c4 cin4 fl4 pi4)
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) c5 cin5 fl5 pi5)
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) c6 cin6 fl6 pi6)
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
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
    (h_input_r1_circuit : add_input.r1_val = binaryValidA64 v r_binary)
    (h_input_r2_circuit : add_input.r2_val = binaryValidB64 v r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
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
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.Arith.h_rd_val_arith_add_of_wf
      m r_main e2 add_input.r1_val add_input.r2_val
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
  rw [equiv_ADD_sail state add_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_add_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- Row-native static-provider BinaryTable route for `equiv_ADD`.
    Mirror of `equiv_SUB_of_static_row`: takes a concrete Clean
    `BinaryRow` + `StaticBinaryTableWfFacts row` + `mode32 = 0` +
    `b_op = OP_ADD` pins, derives the 8-byte chain via
    `byte_chain_discharge_64_of_static_row`, the final-byte
    `carry_7 = 0` via `carry_7_zero_ADD_of_static_chain`, projects
    Main↔Binary c-lane matches via `matches_entry`, and delegates to
    `equiv_ADD_of_wf`. -/
lemma equiv_ADD_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_zero : row.mode.mode32 = 0)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD)
    (h_input_r1_row : add_input.r1_val = binaryRowA64 row)
    (h_input_r2_row : add_input.r2_val = binaryRowB64 row)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core
      h_mode32_zero h_b_op
  have h_carry_7_zero :=
    ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_ADD_of_static_chain
      v 0 out h_core h_core.2.1
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
  exact ZiskFv.EquivCore.Add.equiv_ADD_of_wf
    state add_input r1 r2 rd m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v 0
    ⟨h_main_active, h_main_op_add⟩
    h_match_v
    (v.free_in_c_0 0) (v.free_in_c_1 0) (v.free_in_c_2 0)
    (v.free_in_c_3 0) (v.free_in_c_4 0) (v.free_in_c_5 0)
    (v.free_in_c_6 0) (v.free_in_c_7 0)
    (0 : FGL) (v.carry_0 0) (v.carry_1 0) (v.carry_2 0)
    (v.carry_3 0) (v.carry_4 0) (v.carry_5 0) (v.carry_6 0)
    (ZiskFv.AirsClean.Binary.lookupFlags012Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_0 0))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_1 0))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_2 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_3 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_4 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_5 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_6 0))
    (ZiskFv.AirsClean.Binary.lookupFlags7Row (ZiskFv.AirsClean.Binary.rowAt v 0))
    (2 * v.use_first_byte 0) (0 : FGL) (0 : FGL) (v.mode32 0)
    (0 : FGL) (0 : FGL) (0 : FGL) (1 - v.mode32 0)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.c0_lt out.c1_lt out.c2_lt out.c3_lt out.c4_lt out.c5_lt out.c6_lt out.c7_lt
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_ne
    out.pi4_ne out.pi5_ne out.pi6_ne out.pi7_eq
    h_match_clo h_match_chi
    (by simpa [v, binaryValidA64, binaryRowA64, ZiskFv.AirsClean.Binary.validOfRow]
      using h_input_r1_row)
    (by simpa [v, binaryValidB64, binaryRowB64, ZiskFv.AirsClean.Binary.validOfRow]
      using h_input_r2_row)
    h_lane_rd

/-- **BinaryAdd-arm row-native equiv_ADD** (T2.2b multi-provider migration).
    Takes a concrete Clean `BinaryAddRow` plus the four BinaryAdd row
    constraints in `core_every_row` form at row 0 of the `validOfRow`
    view, the op-bus `matches_entry` against the Clean BinaryAdd row's
    emission, and the usual Main-side pieces. Delegates to canonical
    `equiv_ADD` with `validOfRow row` as the validator and `r_binary = 0`.
    The op_bus_perm_sound_BinaryAdd existential is bypassed — the row
    witness comes from the caller (typically the family-balance
    extraction). -/
lemma equiv_ADD_of_binaryadd_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.BinaryAdd.core_every_row
      (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_main_subset : add_subset_holds m r_main)
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_b_lo_t : m.b_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r2)))
    (h_b_hi_t : m.b_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r2)))
    (h_m32 : m.m32 r_main = 0)
    (h_a_range : a_chunks_in_range (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_b_range : b_chunks_in_range (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_c_range : c_chunks_in_range (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  let b := ZiskFv.AirsClean.BinaryAdd.validOfRow row
  -- Derive m.flag r_main = 0 via matches_entry's flag-slot projection
  -- (BinaryAdd's bus row pins flag := 0).
  have h_match_b :
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b 0) := by
    simpa [b, ZiskFv.AirsClean.BinaryAdd.validOfRow,
      ZiskFv.AirsClean.BinaryAdd.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_BinaryAdd] using h_match
  have h_flag : m.flag r_main = 0 := by
    have := h_match_b
    simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd] at this
    exact this.2.2.2.2.2.2.2.2.1
  have h_main_mode : main_row_in_add_mode m r_main :=
    ⟨h_main_active, h_main_op_add, h_m32, h_flag⟩
  -- Discharge the 8 e2 byte ranges via the chunk-byte projection lemma.
  have h_e2_0 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 0
  have h_e2_1 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 1
  have h_e2_2 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 2
  have h_e2_3 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 3
  have h_e2_4 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 4
  have h_e2_5 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 5
  have h_e2_6 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 6
  have h_e2_7 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 7
  -- Route through `equiv_ADD_with_match` (skips op_bus_perm_sound_BinaryAdd);
  -- caller-supplied `h_match_b` is the BinaryAdd-row form of `h_match`.
  exact ZiskFv.EquivCore.Add.equiv_ADD_with_match
    state add_input r1 r2 rd m b r_main 0
    ⟨exec_row, e0, e1, e2⟩
    promises h_main_subset h_main_mode h_core h_match_b
    h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t
    h_a_range h_b_range h_c_range h_lane_rd
    ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩

end ZiskFv.EquivCore.Add
