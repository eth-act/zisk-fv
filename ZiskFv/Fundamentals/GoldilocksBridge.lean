import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler

/-!
Goldilocks ↔ `BitVec 64` bridge lemmas.

Composes `equiv_ADD_circuit` (Goldilocks field arithmetic on 32-bit lanes) with
`equiv_ADD_sail` (`BitVec 64` arithmetic) via:

* `lane_lo_lane_hi_recombine_eq_toNat` — the two 32-bit lanes of a `BitVec 64`,
  viewed as `FGL`, reassemble to `(bv.toNat : FGL)`.
* `add_bv_toNat_eq_field_sum_minus_carry` — `BitVec 64` addition absorbs into
  the field sum modulo a carry-out term `cout * 2^64`.

**Caveat on field reduction.** `GL_prime = 2^64 - 2^32 + 1 < 2^64`, so a
`BitVec 64` *can* exceed `GL_prime` — the coercion `(bv.toNat : FGL)` already
performs the necessary `ZMod` reduction. The lemmas below are phrased to
expose the Goldilocks-level equation, not the `Nat` representative.

**Namespace.** Everything lives under `Goldilocks`. `lane_lo`/`lane_hi` come
from `ZiskFv.Trusted` (re-opened here).
-/

namespace Goldilocks

open ZiskFv.Trusted

/-- `4294967296 = 2^32` as an `FGL` literal. Computational identity. -/
lemma FGL_2_pow_32_val : ((4294967296 : FGL)).val = 4294967296 := by
  decide

/-- `lane_lo` lifts a `BitVec 64` to `FGL` by taking the low 32 bits as the
    `Fin GL_prime` representative. -/
lemma lane_lo_val (bv : BitVec 64) : (lane_lo bv).val = bv.toNat % 4294967296 := rfl

/-- `lane_hi` lifts a `BitVec 64` to `FGL` by taking the high 32 bits. -/
lemma lane_hi_val (bv : BitVec 64) : (lane_hi bv).val = bv.toNat / 4294967296 % 4294967296 := rfl

/-- The `lane_hi` representative actually equals `bv.toNat / 2^32` because
    `bv.toNat < 2^64` so `bv.toNat / 2^32 < 2^32` already. -/
lemma lane_hi_val_eq_div (bv : BitVec 64) :
    (lane_hi bv).val = bv.toNat / 4294967296 := by
  rw [lane_hi_val]
  have h_bv_lt : bv.toNat < 18446744073709551616 := by
    have := bv.isLt; simpa using this
  have h_div_lt : bv.toNat / 4294967296 < 4294967296 := by omega
  exact Nat.mod_eq_of_lt h_div_lt

/-- **Bridge 1: lane recombination.** For any `bv : BitVec 64`,

        lane_lo bv + lane_hi bv * 2^32  =  (bv.toNat : FGL)

    in the Goldilocks field. Proof: compute on `Fin GL_prime` representatives
    via the `Nat` identity `b = (b % 2^32) + (b / 2^32) * 2^32`, then close by
    extensionality of `Fin`-valued equality. -/
lemma lane_lo_lane_hi_recombine_eq_toNat (bv : BitVec 64) :
    (lane_lo bv + lane_hi bv * 4294967296 : FGL) = (bv.toNat : FGL) := by
  -- Move everything to `ZMod GL_prime` (= FGL) via `Nat`-arithmetic.
  have h_nat : bv.toNat = bv.toNat % 4294967296 + bv.toNat / 4294967296 * 4294967296 := by
    have := Nat.mod_add_div bv.toNat 4294967296
    omega
  -- Cast the Nat identity to FGL.
  have h_cast : (bv.toNat : FGL) =
      ((bv.toNat % 4294967296 : ℕ) : FGL) + ((bv.toNat / 4294967296 : ℕ) : FGL) * 4294967296 := by
    conv_lhs => rw [h_nat]
    push_cast
    ring
  rw [h_cast]
  -- Reduce lane_lo and lane_hi to their Nat.cast forms.
  have hlo : (lane_lo bv : FGL) = ((bv.toNat % 4294967296 : ℕ) : FGL) := by
    unfold lane_lo
    -- `(⟨n, h⟩ : FGL) = (n : FGL)` iff `(n : FGL).val = n`, which holds when `n < p`.
    have hlt : bv.toNat % 4294967296 < GL_prime := by
      have : bv.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
      omega
    apply Fin.ext
    rw [Fin.val_natCast]
    exact (Nat.mod_eq_of_lt hlt).symm
  have hhi : (lane_hi bv : FGL) = ((bv.toNat / 4294967296 : ℕ) : FGL) := by
    unfold lane_hi
    have h_bv_lt : bv.toNat < 18446744073709551616 := by
      have := bv.isLt; simpa using this
    have h_div_lt : bv.toNat / 4294967296 < 4294967296 := by omega
    have hlt : bv.toNat / 4294967296 < GL_prime := by omega
    apply Fin.ext
    show bv.toNat / 4294967296 % 4294967296 = (((bv.toNat / 4294967296 : ℕ)) : FGL).val
    rw [Fin.val_natCast]
    rw [Nat.mod_eq_of_lt h_div_lt, Nat.mod_eq_of_lt hlt]
  rw [hlo, hhi]

/-- Exact carry-out predicate for `BitVec 64` addition. -/
def add_carry_out (a b : BitVec 64) : FGL :=
  if a.toNat + b.toNat ≥ 18446744073709551616 then 1 else 0

/-- **Bridge 2: carry absorption.** The `BitVec 64` wrap-around of an
    addition, viewed in Goldilocks, equals the field sum minus a carry-out
    weighted by `2^64`. Concretely:

        ((a + b).toNat : FGL) = (a.toNat : FGL) + (b.toNat : FGL)
                              - cout * (4294967296 * 4294967296)

    where `cout = 1` iff `a.toNat + b.toNat ≥ 2^64`, else `0`.

    The factored `4294967296 * 4294967296` (rather than `18446744073709551616`)
    is deliberate: it matches the carry-chain coefficient in `equiv_ADD_circuit` and
    lets `linear_combination` close the composition in `Equivalence/Add.lean`
    (see CLAUDE.md trap 2: `ring` treats the two literal forms as distinct
    polynomial atoms). -/
lemma add_bv_toNat_eq_field_sum_minus_carry (a b : BitVec 64) :
    ((a + b).toNat : FGL) =
      (a.toNat : FGL) + (b.toNat : FGL) - add_carry_out a b * (4294967296 * 4294967296) := by
  unfold add_carry_out
  have ha : a.toNat < 18446744073709551616 := by
    have := a.isLt; simpa using this
  have hb : b.toNat < 18446744073709551616 := by
    have := b.isLt; simpa using this
  have h_add : (a + b).toNat = (a.toNat + b.toNat) % 18446744073709551616 := by
    simp [BitVec.toNat_add]
  split_ifs with hcarry
  · -- Carry case.
    have h_sum_lt : a.toNat + b.toNat < 2 * 18446744073709551616 := by omega
    have h_eq : (a.toNat + b.toNat) % 18446744073709551616 =
                 a.toNat + b.toNat - 18446744073709551616 := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_add, h_eq]
    -- Push the Nat subtraction into FGL via `Nat.cast_sub`; `push_cast`
    -- reduces `(18446744073709551616 : FGL)` to `2^32 - 1` (= `2^64 mod p`)
    -- and `4294967296 * 4294967296` collapses to the same value, so the
    -- goal closes by `ring` once both sides are in the same normal form.
    rw [Nat.cast_sub (by omega : 18446744073709551616 ≤ a.toNat + b.toNat)]
    push_cast
    ring
  · -- No-carry case: mod is a no-op.
    have h_sum_lt : a.toNat + b.toNat < 18446744073709551616 := by omega
    rw [h_add, Nat.mod_eq_of_lt h_sum_lt]
    push_cast
    ring

end Goldilocks
