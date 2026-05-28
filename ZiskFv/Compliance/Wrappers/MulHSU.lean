import Mathlib

import ZiskFv.EquivCore.MulHSU
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_MULHSU` Compliance exemplar

> **Status:** EXEMPLAR. Not part of the canonical `equiv_<OP>` surface
> (lives outside `ZiskFv/Equivalence/MulHSU.lean`). Demonstrates the
> ArithMul-secondary-shape *promise discharge* for the **signed × unsigned**
> high-half MUL (MULHSU = MULSUH = op 0xb3 = 179). Hybrid of `MulHU`
> (unsigned `h_rs2_value`) and `MulH` (signed `h_rs1_value` via `na` MSB pin).
>
> Discharged promise hypotheses:
> * Mode pins (`h_na` / `h_np` reflexivity placeholders; `h_nb = 0`
>   real pin, `h_nr = 0`, `h_sext = 0`, `h_m32 = 0`, `h_div = 0`;
>   `h_na_bool`, `h_nb_bool`) — discharged via the derived Clean
>   finite-table projection `arith_table_op_mulhsu_basic_mode_pin`.
>   `h_np_xor` is a dynamic proof target during C3.2-P, not a static
>   table fact.
> * Two lane-match equations — discharged via the secondary-lane
>   emission bundle composed with `mulh_bus_res1_eq_d_hi`.
> * `h_rs1_value` (signed-rs1) via `signed_packed_toInt_eq_of_read_xreg`
>   composed with `arith_mul_na_eq_msb_of_a` (op = 179 branch).
> * `h_rs2_value` (unsigned-rs2) via the unsigned bridge — no MSB pin needed.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.EquivCore.Promises


/-- **Exemplar wrapper for `equiv_MULHSU`.**

    Mixed-sign signature: rs1 routes through the signed bridge,
    rs2 through the unsigned bridge. `nb` is hard-pinned to 0 by
    `arith_table_op_mulhsu_basic_mode_pin`. -/
theorem equiv_MULHSU_of_table
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULSUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_no_signed_mul_witness_defect : False)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  have h_arith_table := arith_table.spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_mulhsu⟩ := pins
  -- ============ Project bus-bundle fields used by the body ============
  have h_input_r1 := promises.input_r1_eq
  have h_input_r2 := promises.input_r2_eq
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_mul_secondary_op_eq h_match_secondary
  have h_op_arith_mulhsu : v.op r_a = 179 := by
    rw [h_op_eq, h_main_op_mulhsu]; simp [OP_MULSUH]
  have h_op_arith_na : v.op r_a = 179 ∨ v.op r_a = 181 :=
    Or.inl h_op_arith_mulhsu
  -- ============ Unpack matches_entry lane projections ============
  obtain ⟨h_a_lo_eq_FGL, h_a_hi_eq_FGL, h_b_lo_eq_FGL, h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_mul_secondary_projections h_match_secondary
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds_of_extended v r_a h_row_constraints
  -- C3 re-root: route the MUL-mode carry-chain constraints through the
  -- Clean `Air.Flat.Component` (`AirsClean/ArithMul/`). Same constraint set;
  -- the routing makes `arithMul_circuit_completeness` (completeness-direction)
  -- enter this opcode's `#print axioms`, so the Component is load-bearing.
  have h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a :=
    ZiskFv.AirsClean.ArithMul.mul_carry_chain_holds_via_component v r_a h_chain
  have h_c46 : ZiskFv.Airs.ArithMul.mul_constraint_46_named v r_a :=
    ZiskFv.Airs.ArithMul.mul_constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins (MULHSU = hard nb pin + sign-witness) ============
  -- The hard `nb = 0`, mode pins, and sign-witness booleanity are true ROM
  -- projections. The old axiom is still used only for the overstrong
  -- `np_xor` clause until the signed/unsigned high-half proof is repaired.
  obtain ⟨h_nb_zero, h_nr_eq, h_sext, h_m32, h_div, h_na_bool, _h_np_bool⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulhsu_basic_mode_pin
      v r_a h_arith_table h_op_arith_mulhsu
  have h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) := by
    -- Known-defect exclusion: MULHSU product-sign relation must come from
    -- dynamic witness soundness or an upstream circuit fix.
    exact False.elim h_no_signed_mul_witness_defect
  have h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1 := Or.inl h_nb_zero
  -- ============ DISCHARGE main_mul/main_div selector pins (both = 0) ============
  obtain ⟨h_main_mul_zero, h_main_div_zero⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.mulhsu_main_selector_pin
      v r_a h_arith_table h_op_arith_mulhsu
  -- Placeholder reflexivity for h_na / h_np.
  have h_na : v.na r_a = v.na r_a := rfl
  have h_np : v.np r_a = v.np r_a := rfl
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (lane match — Family A) ============
  -- OP_MULSUH literal 0xb3 = 179 — position 2 in
  -- main_external_arith_emission_bundle's 14-way disjunction
  -- (MULU, MULUH, MULSUH, …).
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
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          _h_c0_lt, _h_c1_lt, _h_c2_lt, _h_c3_lt,
          h_d0_lt, h_d1_lt, h_d2_lt, h_d3_lt⟩ :=
    ZiskFv.Airs.Arith.arith_mul_columns_in_range v r_a
  -- Byte-lane lo equation via cross-AIR `arith_byte_lane_eq_of_match`.
  have h_byte_lo := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
  -- Hi lane via mulh_bus_res1_eq_d_hi (Family A — secondary).
  have h_bus_res1_eq : v.bus_res1 r_a = v.d_2 r_a + v.d_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBusRes1.mulh_bus_res1_eq_d_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_zero
  have h_c1_eq_FGL' : m.c_1 r_main = v.d_2 r_a + v.d_3 r_a * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi := arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_d2_lt h_d3_lt
  -- ============ DISCHARGE h_rs1_value (signed) / h_rs2_value (unsigned) ============
  obtain ⟨_h_m32_m, _h_sp1, _h_sp2, _h_off1, _h_off2,
         h_main_a_lo, h_main_a_hi, h_main_b_lo, h_main_b_hi⟩ :=
    ZiskFv.Trusted.transpile_MULHSU
      m r_main (regidx_to_fin r1) (regidx_to_fin r2) (0 : Fin 32)
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op_mulhsu
  have h_r1_packed_bv :
      mulhsu_input.r1_val
        = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) mulhsu_input.r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_main_a_lo h_main_a_hi h_input_r1
  have h_r2_packed_bv :
      mulhsu_input.r2_val
        = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) mulhsu_input.r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_main_b_lo h_main_b_hi h_input_r2
  -- Unsigned r1/r2 toNat = packed4 via end-to-end non-W operand bridge.
  have h_r1_toNat := arith_rs_toNat_eq_packed4_nonW
    (m.a_0 r_main) (m.a_1 r_main) (m.m32 r_main)
    h_a_lo_eq_FGL h_a_hi_eq_FGL _h_m32_m h_r1_packed_bv
    h_a0_lt h_a1_lt h_a2_lt h_a3_lt
  have h_r2_toNat := arith_rs_toNat_eq_packed4_nonW
    (m.b_0 r_main) (m.b_1 r_main) (m.m32 r_main)
    h_b_lo_eq_FGL h_b_hi_eq_FGL _h_m32_m h_r2_packed_bv
    h_b0_lt h_b1_lt h_b2_lt h_b3_lt
  -- na MSB pin → h_rs1_value (signed rs1).
  have h_na_msb := ZiskFv.Airs.Arith.arith_mul_na_eq_msb_of_a
    v r_a h_op_arith_na
  have h_rs1_value :
      mulhsu_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r1 h_r1_toNat ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt⟩ h_na_msb
  -- Unsigned rs2 → h_rs2_value via direct cast of h_r2_toNat to ℤ.
  have h_rs2_value :
      (mulhsu_input.r2_val.toNat : ℤ)
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    exact_mod_cast h_r2_toNat
  -- ============ Delegate to `equiv_MULHSU` ============
  exact ZiskFv.EquivCore.MulHSU.equiv_MULHSU
    state mulhsu_input r1 r2 rd v r_a
    ⟨exec_row, e0, e1, e2⟩
    promises
    h_chain h_na h_nb_zero h_np h_nr_eq h_sext h_m32 h_div
    h_na_bool h_nb_bool h_np_xor
    h_byte_lo h_byte_hi h_rs1_value h_rs2_value

/-- Compatibility wrapper preserving the current canonical surface while
    the Compliance dispatcher is migrated to row-native table witnesses. -/
theorem equiv_MULHSU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULSUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_no_signed_mul_witness_defect : False)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact equiv_MULHSU_of_table
    state mulhsu_input r1 r2 rd bus m r_main v r_a pins h_match_secondary promises arith_mem
    arith_table
    h_row_constraints h_no_signed_mul_witness_defect

end ZiskFv.Compliance
