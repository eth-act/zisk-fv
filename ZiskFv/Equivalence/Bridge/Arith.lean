import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.CarryChain
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge

/-!
# Arith discharge bridge (Mul + Div)

Implements *promise discharge* for the Arith-AIR opcode shapes:
multiplication (`MUL` / `MULH` / `MULHU` / `MULHSU` / `MULW` via
`ArithMul`) and division (`DIV` / `DIVU` / `DIVW` / `DIVUW` / `REM` /
`REMU` / `REMW` / `REMUW` via `ArithDiv`).

The bridge has three API entry points (one per OpBus axiom):
* `arith_mul_discharge_conservative` — consumes
  `op_bus_perm_sound_ArithMul`.
* `arith_div_discharge_conservative` — consumes
  `op_bus_perm_sound_ArithDiv` (primary bus tuple).
* `arith_div_secondary_discharge_conservative` — consumes
  `op_bus_perm_sound_ArithDivSecondary` (companion remainder /
  quotient bus tuple).

Each entry point delivers the existential row witness `r_a` for the
Arith AIR plus the `matches_entry` cross-AIR consistency conjunct.
Downstream `equiv_<OP>` proofs (Step 3) project that conjunct into
the loose `a₀..a₃ b₀..b₃ c₀..c₃ d₀..d₃` byte-bundle equations the
current MUL / DIV equivs accept as caller obligations.

What remains caller-supplied (this conservative pass):

* The carry-chain hypotheses `hC31..hC38` (modeled in
  `ZiskFv/Airs/Arith/CarryChain.lean` as derivable from per-row
  arithmetic constraints; deferrable to a follow-up PR that
  promotes the loose byte-bundle to `Valid_ArithMul` /
  `Valid_ArithDiv` columns and consumes `CarryChain.lean`
  directly).
* The per-byte range bounds on the loose elements (no
  `arith_columns_in_range` axiom in the trust ledger yet; adding
  one is a separate trust-ledger decision).

(Cross-reference: the BinaryAdd bridge in `Bridge/BinaryAdd.lean`
is the worked example for ArithMul, and Binary's
`binary_discharge_conservative` in `Bridge/Binary.lean` shows the
conservative shape used here.)
-/

namespace ZiskFv.Equivalence.Bridge.Arith

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **ArithMul discharge bridge (conservative).** Replaces the
    per-opcode `r_a` row-index parameter + `h_match` cross-AIR
    *promise hypothesis* on MUL-shape opcodes
    (`MUL` / `MULH` / `MULHU` / `MULHSU` / `MULW`) with a derivation
    rooted at `op_bus_perm_sound_ArithMul` (Phase A).

    Caller obligations after this discharge:
    * `h_main_active : m.is_external_op r_main = 1`
    * `h_main_op_in_set` (the 4-way disjunction in the OpBus axiom;
      each call site pins a specific MUL literal: 0x90/0x91/0x92/0xb0).

    Outputs: existential `r_a` + `matches_entry`. -/
theorem arith_mul_discharge_conservative
    (m : Valid_Main C FGL FGL) (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = 0x90 ∨ m.op r_main = 0x91 ∨ m.op r_main = 0x92
               ∨ m.op r_main = 0xb0) :
    ∃ r_a,
      matches_entry (opBus_row_Main m r_main) (ZiskFv.Airs.ArithMul.opBus_row_Arith a r_a) :=
  op_bus_perm_sound_ArithMul m a r_main h_main_active h_main_op

/-- **ArithDiv (primary) discharge bridge (conservative).** Replaces
    the per-opcode `r_a` + `h_match` for the primary division bus
    tuple. Each `equiv_<OP>` for the DIV family supplies the
    8-way disjunction over `0xa0..0xa7`. -/
theorem arith_div_discharge_conservative
    (m : Valid_Main C FGL FGL) (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = 0xa0 ∨ m.op r_main = 0xa1 ∨ m.op r_main = 0xa2
               ∨ m.op r_main = 0xa3 ∨ m.op r_main = 0xa4 ∨ m.op r_main = 0xa5
               ∨ m.op r_main = 0xa6 ∨ m.op r_main = 0xa7) :
    ∃ r_a,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv a r_a) :=
  op_bus_perm_sound_ArithDiv m a r_main h_main_active h_main_op

/-- **ArithDiv (secondary remainder/quotient) discharge bridge
    (conservative).** Each DIV-family `equiv_<OP>` needs both the
    primary and secondary handshakes for the bus protocol; this
    entry point delivers the secondary's matches_entry conjunct. -/
theorem arith_div_secondary_discharge_conservative
    (m : Valid_Main C FGL FGL) (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = 0xa0 ∨ m.op r_main = 0xa1 ∨ m.op r_main = 0xa2
               ∨ m.op r_main = 0xa3 ∨ m.op r_main = 0xa4 ∨ m.op r_main = 0xa5
               ∨ m.op r_main = 0xa6 ∨ m.op r_main = 0xa7) :
    ∃ r_a,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary a r_a) :=
  op_bus_perm_sound_ArithDivSecondary m a r_main h_main_active h_main_op

/-- **ArithMul chunk-range discharge at any row.** All 16 chunks
    (`a_0..a_3`, `b_0..b_3`, `c_0..c_3`, `d_0..d_3`) are < 2^16.
    Pure consequence of `arith_mul_columns_in_range`. -/
theorem arith_mul_chunk_ranges_at_holds
    (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536 :=
  ZiskFv.Airs.Arith.arith_mul_columns_in_range a r

/-- **ArithDiv chunk-range discharge at any row.** Mirror of
    `arith_mul_chunk_ranges_at_holds` for the Div view. -/
theorem arith_div_chunk_ranges_at_holds
    (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL) (r : ℕ) :
    (a.a_0 r).val < 65536 ∧ (a.a_1 r).val < 65536
  ∧ (a.a_2 r).val < 65536 ∧ (a.a_3 r).val < 65536
  ∧ (a.b_0 r).val < 65536 ∧ (a.b_1 r).val < 65536
  ∧ (a.b_2 r).val < 65536 ∧ (a.b_3 r).val < 65536
  ∧ (a.c_0 r).val < 65536 ∧ (a.c_1 r).val < 65536
  ∧ (a.c_2 r).val < 65536 ∧ (a.c_3 r).val < 65536
  ∧ (a.d_0 r).val < 65536 ∧ (a.d_1 r).val < 65536
  ∧ (a.d_2 r).val < 65536 ∧ (a.d_3 r).val < 65536 :=
  ZiskFv.Airs.Arith.arith_div_columns_in_range a r

/-! ## CarryChain re-exports — packed multiplication / division
    identities derived from the per-row carry-chain constraints.

    Re-exports of the `arith_{mul,div}_{un,}signed_packed_correct_bundled`
    lemmas from `Airs/Arith/{Mul,Div}.lean` under the Bridge namespace
    so downstream `equiv_<OP>` consumers (Step 3) discharge the
    `hC31..hC38` and friends caller hypotheses through a single Bridge
    import path. The underlying derivation is `CarryChain.lean`'s
    `arith_{mul,div}_{un,}signed_carry_identity`. -/

/-- **MUL-unsigned packed correctness (bundled).** Re-export of
    `ZiskFv.Airs.ArithMul.arith_mul_unsigned_packed_correct_bundled`. -/
abbrev mul_unsigned_packed :=
  @ZiskFv.Airs.ArithMul.arith_mul_unsigned_packed_correct_bundled

/-- **MUL-signed packed correctness.** Re-export of
    `ZiskFv.Airs.ArithMul.arith_mul_signed_packed_correct`. -/
abbrev mul_signed_packed :=
  @ZiskFv.Airs.ArithMul.arith_mul_signed_packed_correct

/-- **DIV-unsigned packed correctness (bundled).** Re-export of
    `ZiskFv.Airs.ArithDiv.arith_div_unsigned_packed_correct_bundled`. -/
abbrev div_unsigned_packed :=
  @ZiskFv.Airs.ArithDiv.arith_div_unsigned_packed_correct_bundled

/-- **DIV-signed packed correctness.** Re-export of
    `ZiskFv.Airs.ArithDiv.arith_div_signed_packed_correct`. -/
abbrev div_signed_packed :=
  @ZiskFv.Airs.ArithDiv.arith_div_signed_packed_correct

end ZiskFv.Equivalence.Bridge.Arith
