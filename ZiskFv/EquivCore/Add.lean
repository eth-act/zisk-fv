import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Field.GoldilocksBridge
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
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
import ZiskFv.Airs.Binary.BinaryRanges

/-!
End-to-end theorem for RV64 ADD. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_ADD`),
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
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Add


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
    deriving `h_input_r{1,2}_main` from `transpile_ADD` + a state-
    bridge, or by universalizing `h_main_subset` / `h_main_mode`
    from `Valid_Main` constraints.) -/
theorem equiv_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (badd : ZiskFv.Compliance.BinaryAddWitness)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    -- Structural promise bundle (15 fields, see Promises/RType.lean).
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_add_mode m r_main)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨b, h_b_core⟩ := badd
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ := bounds
  obtain ⟨h_input_r1_sail, h_input_r2_sail, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- *Promise discharge* via the BinaryAdd bridge (with SailStateBridge
  -- deriving the input bridges from the Sail-form `read_xreg` facts
  -- that `equiv_ADD_sail` consumes).
  obtain ⟨r_binary, h_circuit, h_a_range, h_b_range, h_c_range,
          h_input_r1_circuit, h_input_r2_circuit⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryAdd.add_discharge
      m b r_main h_main_subset h_main_mode h_b_core
      state (regidx_to_fin r1) (regidx_to_fin r2)
      add_input.r1_val add_input.r2_val
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

/-- **Binary-arm equiv_ADD** (T2.2 multi-provider migration).
    Takes a Valid_Binary witness with an 8-byte chain at OP_ADD and the
    op-bus matches_entry against the Binary provider's emission. Mirrors
    `equiv_SUB_of_wf` with OP_SUB → OP_ADD and subtraction → addition;
    uses `transpile_ADD` (different argument order from SUB) to derive
    m32 = 0 and the source-register lane equalities. The Binary AIR
    serves 64-bit ADD as an alternate provider to BinaryAdd
    (per `binary.pil:22`, OP_ADD = 0x0A is in Binary's coverage). -/
theorem equiv_ADD_of_wf
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
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
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
  have ha0 : (v.free_in_a_0 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_0_lt_256 v r_binary
  have ha1 : (v.free_in_a_1 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_1_lt_256 v r_binary
  have ha2 : (v.free_in_a_2 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_2_lt_256 v r_binary
  have ha3 : (v.free_in_a_3 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_3_lt_256 v r_binary
  have ha4 : (v.free_in_a_4 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_4_lt_256 v r_binary
  have ha5 : (v.free_in_a_5 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_5_lt_256 v r_binary
  have ha6 : (v.free_in_a_6 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_6_lt_256 v r_binary
  have ha7 : (v.free_in_a_7 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_a_7_lt_256 v r_binary
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_0_lt_256 v r_binary
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_1_lt_256 v r_binary
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_2_lt_256 v r_binary
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_3_lt_256 v r_binary
  have hb4 : (v.free_in_b_4 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_4_lt_256 v r_binary
  have hb5 : (v.free_in_b_5 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_5_lt_256 v r_binary
  have hb6 : (v.free_in_b_6 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_6_lt_256 v r_binary
  have hb7 : (v.free_in_b_7 r_binary).val < 256 := ZiskFv.Airs.Binary.bin_b_7_lt_256 v r_binary
  -- transpile_ADD layout (different from SUB):
  --   (a_0_lane, a_1_lane, b_0_lane, b_1_lane, m32, set_pc, store_pc, jmp1, jmp2)
  have h_input_r1_circuit : add_input.r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
    obtain ⟨h_a_lo_t, h_a_hi_t, _, _, h_m32, _, _, _, _⟩ :=
      transpile_ADD m r_main
        (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
        (regidx_to_fin r1) (regidx_to_fin r2)
        h_main_active h_main_op_add
    have h_r1_main :=
      ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r1) add_input.r1_val (m.a_0 r_main) (m.a_1 r_main)
        h_a_lo_t h_a_hi_t h_input_r1
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
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
  have h_input_r2_circuit : add_input.r2_val
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536 + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936) := by
    obtain ⟨_, _, h_b_lo_t, h_b_hi_t, h_m32, _, _, _, _⟩ :=
      transpile_ADD m r_main
        (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
        (regidx_to_fin r1) (regidx_to_fin r2)
        h_main_active h_main_op_add
    have h_r2_main :=
      ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
        state (regidx_to_fin r2) add_input.r2_val (m.b_0 r_main) (m.b_1 r_main)
        h_b_lo_t h_b_hi_t h_input_r2
    have h_lane_eqs := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
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

end ZiskFv.EquivCore.Add
