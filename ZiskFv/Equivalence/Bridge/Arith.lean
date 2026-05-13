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

/-! ## Per-opcode discharge helpers — unsigned-mode carry-chain witnesses

The MUL / MULHU / DIVU / REMU equivs currently take 22 loose carry-shape
binders (7 cy witnesses + 7 cy range bounds + 8 hC equations). The
helpers below consume the row-level `mul_carry_chain_holds` /
`div_carry_chain_holds` predicate (from `Valid_<AIR>`-derived
constraint extraction) plus the unsigned-mode pins, and deliver the
witness pack as an existential. Trust footprint:
`arith_{mul,div}_carry_columns_in_range_unsigned`.
-/

section UnsignedChainWitnesses

open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open Arith.extraction

/-- **MUL-unsigned chain witnesses (existential bundle).**

    Given the row-level carry-chain constraint set
    (`mul_carry_chain_holds v r_a` = constraints 6/7/8 + 31..38) plus
    the unsigned-mode pins (`na = nb = np = nr = sext = m32 = div = 0`),
    deliver an existential pack of seven carry witnesses + their range
    bounds + the eight named-column carry-chain identities in the form
    consumed by the MUL / MULHU rd-value derivations.

    Carry-range bounds are discharged by
    `arith_mul_carry_columns_in_range_unsigned` (trust ledger).
    Carry-chain identities are derived from constraints 31..38 by
    rewriting selectors to mode-zero / fab-one / na_fb-nb_fa-zero
    form (constraints 6/7/8 supply the last). -/
theorem mul_unsigned_chain_witnesses
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (h_chain : mul_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (_h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0)
    (h_div : v.div r_a = 0) :
    ∃ cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL,
      cy₀.val < 131072 ∧ cy₁.val < 131072 ∧ cy₂.val < 131072 ∧ cy₃.val < 131072
    ∧ cy₄.val < 131072 ∧ cy₅.val < 131072 ∧ cy₆.val < 131072
    ∧ (v.a_0 r_a * v.b_0 r_a = v.c_0 r_a + cy₀ * 65536)
    ∧ (v.a_1 r_a * v.b_0 r_a + v.a_0 r_a * v.b_1 r_a + cy₀ = v.c_1 r_a + cy₁ * 65536)
    ∧ (v.a_2 r_a * v.b_0 r_a + v.a_1 r_a * v.b_1 r_a + v.a_0 r_a * v.b_2 r_a + cy₁
        = v.c_2 r_a + cy₂ * 65536)
    ∧ (v.a_3 r_a * v.b_0 r_a + v.a_2 r_a * v.b_1 r_a + v.a_1 r_a * v.b_2 r_a
        + v.a_0 r_a * v.b_3 r_a + cy₂ = v.c_3 r_a + cy₃ * 65536)
    ∧ (v.a_3 r_a * v.b_1 r_a + v.a_2 r_a * v.b_2 r_a + v.a_1 r_a * v.b_3 r_a + cy₃
        = v.d_0 r_a + cy₄ * 65536)
    ∧ (v.a_3 r_a * v.b_2 r_a + v.a_2 r_a * v.b_3 r_a + cy₄
        = v.d_1 r_a + cy₅ * 65536)
    ∧ (v.a_3 r_a * v.b_3 r_a + cy₅ = v.d_2 r_a + cy₆ * 65536)
    ∧ (cy₆ = v.d_3 r_a) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Extract fab = 1, na_fb = 0, nb_fa = 0 from constraints 6/7/8 + mode.
  simp only [constraint_6_every_row, constraint_7_every_row, constraint_8_every_row,
             ← v.na_def, ← v.nb_def] at h6 h7 h8
  simp only [h_na, h_nb] at h6 h7 h8
  have h_fab : Circuit.main v.circuit (id := 1) (column := 30) (row := r_a) (rotation := 0)
    = (1 : FGL) := by linear_combination h6
  have h_nafb : Circuit.main v.circuit (id := 1) (column := 31) (row := r_a) (rotation := 0)
    = (0 : FGL) := by linear_combination h7
  have h_nbfa : Circuit.main v.circuit (id := 1) (column := 32) (row := r_a) (rotation := 0)
    = (0 : FGL) := by linear_combination h8
  -- Unfold constraints 31..38 to named-column form + mode-zero substitution.
  simp only [constraint_31_every_row, constraint_32_every_row,
             constraint_33_every_row, constraint_34_every_row,
             constraint_35_every_row, constraint_36_every_row,
             constraint_37_every_row, constraint_38_every_row,
             ← v.a_0_def, ← v.a_1_def, ← v.a_2_def, ← v.a_3_def,
             ← v.b_0_def, ← v.b_1_def, ← v.b_2_def, ← v.b_3_def,
             ← v.c_0_def, ← v.c_1_def, ← v.c_2_def, ← v.c_3_def,
             ← v.d_0_def, ← v.d_1_def, ← v.d_2_def, ← v.d_3_def,
             ← v.na_def, ← v.nb_def, ← v.np_def, ← v.nr_def,
             ← v.m32_def, ← v.div_def]
    at h31 h32 h33 h34 h35 h36 h37 h38
  simp only [h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
             mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  -- Carry range bounds (axiom).
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ :=
    ZiskFv.Airs.Arith.arith_mul_carry_columns_in_range_unsigned v r_a h_na h_nb h_np h_nr
  -- Package the existential witnesses (cy_i = Circuit.main at column i).
  refine ⟨_, _, _, _, _, _, _, hr0, hr1, hr2, hr3, hr4, hr5, hr6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h31
  · linear_combination h32
  · linear_combination h33
  · linear_combination h34
  · linear_combination h35
  · linear_combination h36
  · linear_combination h37
  · linear_combination h38

/-- **DIV-unsigned chain witnesses (existential bundle).**

    Same as `mul_unsigned_chain_witnesses` but for the Div view: DIVU /
    REMU rows have `div = 1` (instead of 0) so the `d_i` summands
    appear additively in chunks 0..3 and the upper-half d-chunks vanish.

    PIL: `arith.pil:205-209` (carry chain); selectors per
    `arith_table.pil`'s `divu`/`remu` row. -/
theorem div_unsigned_chain_witnesses
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_chain : div_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (_h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0)
    (h_div : v.div r_a = 1) :
    ∃ cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL,
      cy₀.val < 131072 ∧ cy₁.val < 131072 ∧ cy₂.val < 131072 ∧ cy₃.val < 131072
    ∧ cy₄.val < 131072 ∧ cy₅.val < 131072 ∧ cy₆.val < 131072
    ∧ (v.a_0 r_a * v.b_0 r_a + v.d_0 r_a = v.c_0 r_a + cy₀ * 65536)
    ∧ (v.a_1 r_a * v.b_0 r_a + v.a_0 r_a * v.b_1 r_a + v.d_1 r_a + cy₀
        = v.c_1 r_a + cy₁ * 65536)
    ∧ (v.a_2 r_a * v.b_0 r_a + v.a_1 r_a * v.b_1 r_a + v.a_0 r_a * v.b_2 r_a
        + v.d_2 r_a + cy₁
        = v.c_2 r_a + cy₂ * 65536)
    ∧ (v.a_3 r_a * v.b_0 r_a + v.a_2 r_a * v.b_1 r_a + v.a_1 r_a * v.b_2 r_a
        + v.a_0 r_a * v.b_3 r_a + v.d_3 r_a + cy₂
        = v.c_3 r_a + cy₃ * 65536)
    ∧ (v.a_3 r_a * v.b_1 r_a + v.a_2 r_a * v.b_2 r_a + v.a_1 r_a * v.b_3 r_a + cy₃
        = cy₄ * 65536)
    ∧ (v.a_3 r_a * v.b_2 r_a + v.a_2 r_a * v.b_3 r_a + cy₄ = cy₅ * 65536)
    ∧ (v.a_3 r_a * v.b_3 r_a + cy₅ = cy₆ * 65536)
    ∧ (cy₆ = 0) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  simp only [constraint_6_every_row, constraint_7_every_row, constraint_8_every_row,
             ← v.na_def, ← v.nb_def] at h6 h7 h8
  simp only [h_na, h_nb] at h6 h7 h8
  have h_fab : Circuit.main v.circuit (id := 1) (column := 30) (row := r_a) (rotation := 0)
    = (1 : FGL) := by linear_combination h6
  have h_nafb : Circuit.main v.circuit (id := 1) (column := 31) (row := r_a) (rotation := 0)
    = (0 : FGL) := by linear_combination h7
  have h_nbfa : Circuit.main v.circuit (id := 1) (column := 32) (row := r_a) (rotation := 0)
    = (0 : FGL) := by linear_combination h8
  simp only [constraint_31_every_row, constraint_32_every_row,
             constraint_33_every_row, constraint_34_every_row,
             constraint_35_every_row, constraint_36_every_row,
             constraint_37_every_row, constraint_38_every_row,
             ← v.a_0_def, ← v.a_1_def, ← v.a_2_def, ← v.a_3_def,
             ← v.b_0_def, ← v.b_1_def, ← v.b_2_def, ← v.b_3_def,
             ← v.c_0_def, ← v.c_1_def, ← v.c_2_def, ← v.c_3_def,
             ← v.d_0_def, ← v.d_1_def, ← v.d_2_def, ← v.d_3_def,
             ← v.na_def, ← v.nb_def, ← v.np_def, ← v.nr_def,
             ← v.m32_def, ← v.div_def]
    at h31 h32 h33 h34 h35 h36 h37 h38
  simp only [h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
             mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ :=
    ZiskFv.Airs.Arith.arith_div_carry_columns_in_range_unsigned v r_a h_na h_nb h_np h_nr
  refine ⟨_, _, _, _, _, _, _, hr0, hr1, hr2, hr3, hr4, hr5, hr6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h31
  · linear_combination h32
  · linear_combination h33
  · linear_combination h34
  · linear_combination h35
  · linear_combination h36
  · linear_combination h37
  · linear_combination h38

end UnsignedChainWitnesses

end ZiskFv.Equivalence.Bridge.Arith
