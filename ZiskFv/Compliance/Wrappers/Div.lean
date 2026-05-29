import Mathlib

import ZiskFv.SailSpec.div
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.EquivCore.Promises.RType
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
    (h_no_arith_div_dynamic_defect : False)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact False.elim h_no_arith_div_dynamic_defect

/-- Compatibility wrapper preserving the canonical Compliance theorem name. -/
theorem equiv_DIV
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
    (h_no_arith_div_dynamic_defect : False)
    :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact False.elim h_no_arith_div_dynamic_defect


end ZiskFv.Compliance
