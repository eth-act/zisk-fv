import Mathlib

import ZiskFv.EquivCore.Div
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_DIV` trust-discharge wrapper
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.EquivCore.Promises


/-- **Trust-discharged wrapper for `equiv_DIV`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `div_input`, `r1`, `r2`, `rd`)
       and the structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    2. The two AIR validators with their selected row indices
       (`m : Valid_Main`, `r_main`, `v : Valid_ArithDiv`, `r_a`).
       In Compliance.lean's downstream caller these collapse into
       a single `(m, v)` shared across every per-opcode invocation;
       per-opcode work supplies `r_main` (from Main's program counter
       handshake) and `r_a` (which a follow-up will derive existentially
       from OpBus instead of accepting as a parameter).
    3. The two activation pins (`h_main_active`, `h_main_op_div`).
       In Compliance.lean these are themselves derived from the
       Main AIR's ROM-handshake on the row that hosts the DIV
       instruction.
    4. The structural exec/mem row shape — exactly what
       `equiv_DIV` already accepts; passed through unchanged
       (these are *constructibility* obligations on the bus
       protocol, NOT promise hypotheses on Sail outputs).
    5. The SPEC-PRE preconditions on the Sail input
       (`h_input_r1`, `h_input_r2`, `h_input_rd`, `h_input_pc`,
       `h_op2_ne`, `h_no_overflow`).
    6. The universal-per-row constructibility obligations (the
       per-row Arith-AIR constraints: `h_chain`, `h_na_bool`,
       `h_nb_bool`, `h_nr_bool`, `h_np_xor`). In Compliance.lean
       these collapse into a single
       `∀ r, arith_div_row_well_formed v r`.
    7. The two remaining promise hypotheses (`h_byte_lo`/`h_byte_hi`
      , `h_rs1_value`/`h_rs2_value`) plus `h_rd_idx`.

    Derived internally (NOT caller-supplied):
    * `h_op_arith : v.op r_a = 186 ∨ v.op r_a = 187` — from the
      `matches_entry` op-slot equality (op-bus permutation).
    * `h_sext`, `h_m32`, `h_div` — from
      row-native `ArithTableSpec` plus finite-table projections.
    * `h_nr_pin` — from
      `arith_table_op_div_rem_signed_d_sign_pin` (existing).
    * `h_r_abs`, `h_r_sign` — from `arith_div_remainder_bound`
      () composed with `h_rs1_value`/`h_rs2_value`.

    After  closure the wrapper carries 35 binders / 22
    hypotheses (vs. 37/24 pre- and 43/32 on `equiv_DIV`); both
    `h_rs1_value` and `h_rs2_value` are now derived internally via the new
    class-#6b sign-witness MSB pins (`arith_div_np_eq_msb_of_dividend`
    / `arith_div_nb_eq_msb_of_divisor`) composed with the generic
    `signed_packed_toInt_eq_of_read_xreg` Sail-state bridge. The
    narrowing of `h_main_op_div` to `OP_DIV` (was `OP_DIV ∨ OP_REM`)
    eliminates the vestigial REM dispatch path; a parallel pilot
    `equiv_REM` is the proper future home for REM
    discharge. -/
theorem equiv_DIV_of_table
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    -- ============ DISCHARGE INPUTS ============
    -- AIR validators + row indices. Compliance.lean shares (m, v)
    -- across opcodes; per-opcode caller supplies the row indices.
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    -- Activation / opcode pin on Main.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    -- Cross-AIR row selection: the OpBus permutation gives an
    -- existential `r_a`; we accept it explicitly here so the bridge
    -- shape stays simple (Compliance.lean will obtain `r_a` via
    -- `op_bus_perm_sound_ArithDiv` and pass it in). The matching
    -- predicate carries `m.op r_main = v.op r_a`.
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    -- ============ STRUCTURAL PROMISE BUNDLE (15 fields) ============
    -- Subsumes the prior inline structural bus / exec shape +
    -- Sail-side state predicate binders.
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    -- ============ UNIVERSAL-PER-ROW VALIDITY (constructibility) ============
    -- Per-row Arith-AIR constraints, EXTENDED bundle: the standard
    -- carry-chain (constraints 6-8 + 31-38) PLUS constraint 46
    -- (`bus_res1` normalization at `arith.pil:263`, required for
    -- the  hi-lane discharge via `div_bus_res1_eq_a_hi`).
    -- Compliance.lean collapses this into the universal
    -- `∀ r, arith_div_row_well_formed v r` parameter.
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  have h_arith_table := arith_table.spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_div⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_input_r1 := promises.input_r1_eq
  have h_input_r2 := promises.input_r2_eq
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal () ============
  -- `matches_entry`'s op-slot equality projects to
  -- `m.op r_main = v.op r_a` (the bus opcode column IS the
  -- v.op column on the prove side, per `arith.pil:269`).
  have h_op_eq := arith_div_primary_op_eq h_match_primary
  have h_op_arith_div : v.op r_a = 186 := by
    rw [h_op_eq, h_main_op_div]; simp [OP_DIV]
  have h_op_arith : v.op r_a = 186 ∨ v.op r_a = 187 := Or.inl h_op_arith_div
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_div_primary_projections h_match_primary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : ZiskFv.Airs.ArithDiv.bus_res1_eq_div v r_a :=
    ZiskFv.Airs.ArithDiv.bus_res1_eq_div_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins () ============
  obtain ⟨h_sext, h_m32, h_div⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_signed_mode_pin
      v r_a h_arith_table h_op_arith
  -- ============ DISCHARGE main_div/main_mul selector pins ( hi prep) ============
  -- `op = 186 (DIV)` pins `main_div = 1, main_mul = 0` as a finite-table
  -- projection from the same shared ArithTable lookup membership.
  obtain ⟨h_main_div_one, h_main_mul_zero⟩ :=
    (ZiskFv.AirsClean.ArithTableProjections.Div.div_rem_main_selector_pin
      v r_a h_arith_table h_op_arith).1 h_op_arith_div
  -- ============ DISCHARGE h_nr_pin (existing trust ledger) ============
  have h_nr_pin_fgl :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_d_sign_pin
      v r_a h_sext h_m32 h_div h_op_arith
  have h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
      ∨ ((toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0) := by
    rcases h_nr_pin_fgl with h_eq | ⟨hd0, hd1, hd2, hd3⟩
    · left; rw [h_eq]
    · right
      refine ⟨by ring, hd0, hd1, hd2, hd3⟩
  -- ============ DISCHARGE h_byte_lo / h_byte_hi () ============
  -- Bundle delivers BOTH the `e2.x0..x3` (lo) pack and the
  -- `e2.x4..x7` (hi) pack as ℕ-form equalities tied to Main's
  -- `c_0`/`c_1` columns. Op-bus `matches_entry` gives FGL equalities
  -- on the c_lo / c_hi slots of `opBus_row_ArithDiv`:
  --   c_lo: m.c_0 r_main = v.a_0 r_a + v.a_1 r_a * 65536
  --   c_hi: m.c_1 r_main = v.bus_res1 r_a
  -- The lo side is direct. For the hi side we further apply
  -- `div_bus_res1_eq_a_hi` (BusRes1) under the DIV-primary mode pins
  -- (`main_div = 1`, `main_mul = 0`, plus `sext = 0`, `m32 = 0`,
  -- plus per-row constraint 46) to get `v.bus_res1 = v.a_2 + v.a_3 * 65536`.
  -- Both lanes lift FGL → ℕ via the chunk-range axiom on `v.a_*` (each
  -- < 2^16, so the rhs is < 2^32 < GL_prime — no modular reduction).
  have h_bundle := arith_mem.c_lane_vals
  have h_chunks_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_chunks_range_perm_sound e2
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_chunks_range.1, h_bundle.1]
  have h_byte_hi_to_c1 : (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (m.c_1 r_main).val := by
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_hi_val_sum_eq e2 h_chunks_range.2, h_bundle.2]
  -- Chunk-range bounds for v.{a,b,c,d}_0..3 — extract all sixteen at once.
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_div_columns_in_range v r_a
  -- Byte-lane equations via the cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_a0_lt h_a1_lt
  -- ============ DISCHARGE h_byte_hi (hi lane) ============
  -- `div_bus_res1_eq_a_hi` consumes constraint 46 + the four mode pins.
  have h_bus_res1_eq : v.bus_res1 r_a = v.a_2 r_a + v.a_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.div_bus_res1_eq_a_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_one
  have h_c1_eq_FGL' : m.c_1 r_main = v.a_2 r_a + v.a_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_a2_lt h_a3_lt
  -- ============ DISCHARGE h_rs1_value / h_rs2_value () ============
  -- Combine `transpile_DIV` (Main lane equalities at `sail_to_rv64 state`),
  -- the op-bus `matches_entry` (Main a/b lanes = ArithDiv c[] / b[] packings),
  -- chunk-range bounds, the new MSB pins on `np` / `nb`, and the generic
  -- signed Sail-state bridge to derive the signed packed-lane integer
  -- equations for r1 / r2 that `equiv_DIV` consumes.
  -- transpile_DIV + packed_lane_eq_of_read_xreg → unsigned r_val packings.
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_DIV
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_div
  have h_r1_packed_bv :
      div_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) div_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      div_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) div_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  -- Unsigned r1/r2 toNat = packed4 via end-to-end non-W operand bridge.
  have h_r1_toNat := arith_rs_toNat_eq_packed4_nonW
    (m.a_0 r_main) (m.a_1 r_main) (m.m32 r_main)
    h_a_lo_eq_FGL h_a_hi_eq_FGL _h_m32_m h_r1_packed_bv
    h_c0_lt h_c1_lt h_c2_lt h_c3_lt
  have h_r2_toNat := arith_rs_toNat_eq_packed4_nonW
    (m.b_0 r_main) (m.b_1 r_main) (m.m32 r_main)
    h_b_lo_eq_FGL h_b_hi_eq_FGL _h_m32_m h_r2_packed_bv
    h_b0_lt h_b1_lt h_b2_lt h_b3_lt
  -- MSB pins on np / nb (the class-#6b axioms).
  have h_np_msb := ZiskFv.Airs.Arith.arith_div_np_eq_msb_of_dividend
    v r_a h_sext h_m32 h_div h_op_arith
  have h_nb_msb := ZiskFv.Airs.Arith.arith_div_nb_eq_msb_of_divisor
    v r_a h_sext h_m32 h_div h_op_arith
  -- signed-form bridge → h_rs1_value / h_rs2_value.
  have h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r1 h_r1_toNat ⟨h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt⟩ h_np_msb
  have h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r2 h_r2_toNat ⟨h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt⟩ h_nb_msb
  -- ============ DISCHARGE h_r_abs, h_r_sign () ============
  -- `arith_div_remainder_bound` gives the bound in terms of the
  -- AIR's signed `b - nb·2^64` and `c - np·2^64` packings; we
  -- rewrite via `h_rs2_value` and `h_rs1_value` to land on `r2.toInt` /
  -- `r1.toInt` shapes that `equiv_DIV` consumes.
  obtain ⟨h_r_abs_air, h_r_sign_air⟩ :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound v r_a h_sext h_m32 h_div h_op_arith
  have h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs := by
    rw [h_rs2_value]; exact h_r_abs_air
  have h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt := by
    rw [h_rs1_value]; exact h_r_sign_air
  -- ============ Delegate to `equiv_DIV` ============
  -- The Sail `instruction.DIV` LHS matches; all derived hypotheses fit.
  exact ZiskFv.EquivCore.Div.equiv_DIV
    state div_input r1 r2 rd
    ⟨exec_row, e0, e1, e2⟩
    promises
    v r_a h_chain h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_sext h_m32 h_div h_byte_lo h_byte_hi h_rs1_value h_rs2_value
    h_op2_ne h_no_overflow h_r_abs h_r_sign

/-- Compatibility wrapper preserving the current canonical surface while
    the Compliance dispatcher is migrated to row-native table witnesses. -/
theorem equiv_DIV
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact equiv_DIV_of_table
    state div_input r1 r2 rd bus m r_main v r_a pins h_match_primary promises arith_mem
    h_op2_ne h_no_overflow h_row_constraints
    arith_table
    h_na_bool h_nb_bool h_nr_bool h_np_xor

end ZiskFv.Compliance
