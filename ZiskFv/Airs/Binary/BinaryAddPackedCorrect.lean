import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Binary.BinaryAdd

/-!
**K1-A: BinaryAdd carry-chain → `BitVec 64` lift.**

Lifts ZisK's `BinaryAdd` carry-chain constraints (field-level) to the
semantic 64-bit unsigned addition identity:

```
  BitVec.ofNat 64 (a_0.val + a_1.val · 2^32)
  + BitVec.ofNat 64 (b_0.val + b_1.val · 2^32)
  = BitVec.ofNat 64 (c_chunks_0.val + c_chunks_1.val · 2^16
                    + c_chunks_2.val · 2^32 + c_chunks_3.val · 2^48)
```

i.e., the 64-bit addition of the two operands equals the 64-bit result.
The statement uses `BitVec.ofNat 64` of the constituent chunk Nat values
(not FGL-packed `.val`) to keep the final `omega` goal linear.

Note on packing vs. FGL `.val`: `a_0 + a_1 · 2^32 : FGL` can exceed `GL_prime`
(max value is `2^64 - 1 > GL_prime = 2^64 - 2^32 + 1`), so we cannot equate
`(a_packed.val)` with the raw Nat sum `a_0.val + a_1.val · 2^32`.  The theorem
is therefore stated directly in terms of chunk `.val`s.

**Proof pipeline:**
1. `carry_chain_0_nat`, `carry_chain_1_nat` — lift each FGL carry-chain
   equality to ℕ.  Both sides of each chain are `< GL_prime` under range
   bounds, so `congr_arg Fin.val` + `Fin.val_natCast` + `omega` closes.
2. `binary_add_chunks_eq_bv_add` — combine the two ℕ chain equations with
   boolean `cout` bounds (`cout.val ∈ {0,1}`) and close the BitVec goal by
   `apply BitVec.eq_of_toNat_eq` + `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]`
   + `omega`.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.Airs.BinaryAdd

open Goldilocks
open ZiskFv.Airs.BinaryAdd

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Range predicates -/

/-- Each 32-bit lane of the first operand is in `[0, 2^32)`. -/
@[simp]
def a_chunks_in_range (v : Valid_BinaryAdd C FGL FGL) (row : ℕ) : Prop :=
  (v.a_0 row).val < 4294967296 ∧ (v.a_1 row).val < 4294967296

/-- Each 32-bit lane of the second operand is in `[0, 2^32)`. -/
@[simp]
def b_chunks_in_range (v : Valid_BinaryAdd C FGL FGL) (row : ℕ) : Prop :=
  (v.b_0 row).val < 4294967296 ∧ (v.b_1 row).val < 4294967296

/-- Each 16-bit result chunk is in `[0, 2^16)`. -/
@[simp]
def c_chunks_in_range (v : Valid_BinaryAdd C FGL FGL) (row : ℕ) : Prop :=
  (v.c_chunks_0 row).val < 65536
    ∧ (v.c_chunks_1 row).val < 65536
    ∧ (v.c_chunks_2 row).val < 65536
    ∧ (v.c_chunks_3 row).val < 65536

/-! ## Boolean extraction helper -/

/-- An FGL element satisfying `x * (1 - x) = 0` is either `0` or `1`.
    Immediate from `mul_eq_zero` in the field. -/
lemma fgl_boolean_cases {x : FGL} (h : x * (1 - x) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · left; exact h
  · right; exact (sub_eq_zero.mp h).symm

/-- From `x = 0 ∨ x = 1` in FGL, the `.val` satisfies `x.val = 0 ∨ x.val = 1`. -/
lemma fgl_boolean_val_cases {x : FGL} (h : x = 0 ∨ x = 1) : x.val = 0 ∨ x.val = 1 := by
  rcases h with rfl | rfl <;> simp

/-! ## Carry-chain lift to ℕ

Each carry-chain constraint is a FGL equation.  Under range bounds all terms
are `< GL_prime`, so the field equality lifts to ℕ via
`congr_arg Fin.val` + `Fin.val_natCast` + `omega`.

Bound check for carry_chain_0: LHS < 2·2^32 = 2^33 < GL_prime. ✓
  RHS ≤ 1·2^32 + (2^16-1)·2^16 + (2^16-1) = 2^32 + 2^32 - 2^16 + 2^16 - 1 < 2·2^32. ✓
Bound check for carry_chain_1: LHS ≤ 2^33 + 1 < GL_prime. ✓
  RHS ≤ 1·2^32 + (2^16-1)·2^16 + (2^16-1) < 2·2^32. ✓ -/

/-- **Low-lane carry chain, ℕ level.**

    `a_0.val + b_0.val = cout_0.val · 2^32 + c_chunks_1.val · 2^16 + c_chunks_0.val` -/
lemma carry_chain_0_nat
    (v : Valid_BinaryAdd C FGL FGL) (row : ℕ)
    (h_bool0 : boolean_cout_0 v row)
    (h_carry0 : carry_chain_0 v row)
    (h_a0 : (v.a_0 row).val < 4294967296)
    (h_b0 : (v.b_0 row).val < 4294967296)
    (h_c0 : (v.c_chunks_0 row).val < 65536)
    (h_c1 : (v.c_chunks_1 row).val < 65536) :
    (v.a_0 row).val + (v.b_0 row).val
      = (v.cout_0 row).val * 4294967296
        + (v.c_chunks_1 row).val * 65536
        + (v.c_chunks_0 row).val := by
  -- FGL equation from carry chain.
  have h_fgl : v.a_0 row + v.b_0 row
      = v.cout_0 row * 4294967296 + v.c_chunks_1 row * 65536 + v.c_chunks_0 row := by
    simp only [carry_chain_0] at h_carry0; linear_combination h_carry0
  -- cout_0.val ∈ {0, 1}.
  have h_cout0_val : (v.cout_0 row).val = 0 ∨ (v.cout_0 row).val = 1 :=
    fgl_boolean_val_cases (fgl_boolean_cases
      (by simp only [boolean_cout_0] at h_bool0; exact h_bool0))
  -- Rewrite as Nat casts in FGL so .val works.
  have h_rhs_cast : v.cout_0 row * 4294967296 + v.c_chunks_1 row * 65536 + v.c_chunks_0 row
      = (((v.cout_0 row).val * 4294967296 + (v.c_chunks_1 row).val * 65536
          + (v.c_chunks_0 row).val : ℕ) : FGL) := by push_cast; ring
  have h_lhs_cast : v.a_0 row + v.b_0 row
      = (((v.a_0 row).val + (v.b_0 row).val : ℕ) : FGL) := by push_cast; ring
  rw [h_lhs_cast, h_rhs_cast] at h_fgl
  have heq := congr_arg Fin.val h_fgl
  simp only [Fin.val_natCast] at heq
  -- heq : lhs % GL_prime = rhs % GL_prime; both < GL_prime (from range bounds + bool), so omega.
  omega

/-- **High-lane carry chain, ℕ level.**

    `a_1.val + b_1.val + cout_0.val = cout_1.val · 2^32 + c_chunks_3.val · 2^16 + c_chunks_2.val` -/
lemma carry_chain_1_nat
    (v : Valid_BinaryAdd C FGL FGL) (row : ℕ)
    (h_bool0 : boolean_cout_0 v row)
    (h_bool1 : boolean_cout_1 v row)
    (h_carry1 : carry_chain_1 v row)
    (h_a1 : (v.a_1 row).val < 4294967296)
    (h_b1 : (v.b_1 row).val < 4294967296)
    (h_c2 : (v.c_chunks_2 row).val < 65536)
    (h_c3 : (v.c_chunks_3 row).val < 65536) :
    (v.a_1 row).val + (v.b_1 row).val + (v.cout_0 row).val
      = (v.cout_1 row).val * 4294967296
        + (v.c_chunks_3 row).val * 65536
        + (v.c_chunks_2 row).val := by
  have h_fgl : v.a_1 row + v.b_1 row + v.cout_0 row
      = v.cout_1 row * 4294967296 + v.c_chunks_3 row * 65536 + v.c_chunks_2 row := by
    simp only [carry_chain_1] at h_carry1; linear_combination h_carry1
  have h_cout0_val : (v.cout_0 row).val = 0 ∨ (v.cout_0 row).val = 1 :=
    fgl_boolean_val_cases (fgl_boolean_cases
      (by simp only [boolean_cout_0] at h_bool0; exact h_bool0))
  have h_cout1_val : (v.cout_1 row).val = 0 ∨ (v.cout_1 row).val = 1 :=
    fgl_boolean_val_cases (fgl_boolean_cases
      (by simp only [boolean_cout_1] at h_bool1; exact h_bool1))
  have h_rhs_cast : v.cout_1 row * 4294967296 + v.c_chunks_3 row * 65536 + v.c_chunks_2 row
      = (((v.cout_1 row).val * 4294967296 + (v.c_chunks_3 row).val * 65536
          + (v.c_chunks_2 row).val : ℕ) : FGL) := by push_cast; ring
  have h_lhs_cast : v.a_1 row + v.b_1 row + v.cout_0 row
      = (((v.a_1 row).val + (v.b_1 row).val + (v.cout_0 row).val : ℕ) : FGL) := by push_cast; ring
  rw [h_lhs_cast, h_rhs_cast] at h_fgl
  have heq := congr_arg Fin.val h_fgl
  simp only [Fin.val_natCast] at heq
  omega

/-! ## `BitVec 64` addition theorem — main result -/

/-- **BinaryAdd `BitVec 64` addition theorem.**

    Given carry-chain constraints (`core_every_row`) and range bounds on all
    operand and result chunks, the BinaryAdd AIR computes 64-bit unsigned
    addition.  The statement uses `BitVec.ofNat 64` of the constituent chunk
    Nat values to keep the final `omega` goal linear (FGL-packed `.val` would
    not equal the Nat sum when the sum ≥ GL_prime).

    **Proof sketch:** The ℕ carry chains give:
    * `a_0.val + b_0.val = cout_0.val · 2^32 + c_chunks_1.val · 2^16 + c_chunks_0.val`
    * `a_1.val + b_1.val + cout_0.val = cout_1.val · 2^32 + c_chunks_3.val · 2^16 + c_chunks_2.val`

    Combining with `cout_1.val ∈ {0,1}`, the `BitVec.toNat` form of the goal
    reduces to a modular-arithmetic statement that `omega` closes. -/
theorem binary_add_chunks_eq_bv_add
    (v : Valid_BinaryAdd C FGL FGL) (row : ℕ)
    (h_chain : core_every_row v row)
    (h_a_range : a_chunks_in_range v row)
    (h_b_range : b_chunks_in_range v row)
    (h_c_range : c_chunks_in_range v row) :
    BitVec.ofNat 64 ((v.a_0 row).val + (v.a_1 row).val * 4294967296)
    + BitVec.ofNat 64 ((v.b_0 row).val + (v.b_1 row).val * 4294967296)
    = BitVec.ofNat 64
        ((v.c_chunks_0 row).val
          + (v.c_chunks_1 row).val * 65536
          + (v.c_chunks_2 row).val * 4294967296
          + (v.c_chunks_3 row).val * 281474976710656) := by
  obtain ⟨h_a0, h_a1⟩ := h_a_range
  obtain ⟨h_b0, h_b1⟩ := h_b_range
  obtain ⟨h_c0, h_c1, h_c2, h_c3⟩ := h_c_range
  obtain ⟨h_bool0, h_carry0, h_bool1, h_carry1⟩ := h_chain
  have heq0 := carry_chain_0_nat v row h_bool0 h_carry0 h_a0 h_b0 h_c0 h_c1
  have heq1 := carry_chain_1_nat v row h_bool0 h_bool1 h_carry1 h_a1 h_b1 h_c2 h_c3
  have h_cout1_val : (v.cout_1 row).val = 0 ∨ (v.cout_1 row).val = 1 :=
    fgl_boolean_val_cases (fgl_boolean_cases
      (by simp only [boolean_cout_1] at h_bool1; exact h_bool1))
  set a0v := (v.a_0 row).val
  set a1v := (v.a_1 row).val
  set b0v := (v.b_0 row).val
  set b1v := (v.b_1 row).val
  set c0v := (v.c_chunks_0 row).val
  set c1v := (v.c_chunks_1 row).val
  set c2v := (v.c_chunks_2 row).val
  set c3v := (v.c_chunks_3 row).val
  set k0  := (v.cout_0 row).val
  set k1  := (v.cout_1 row).val
  have h_av : a0v + a1v * 4294967296 < 4294967296 * 4294967296 := by omega
  have h_bv : b0v + b1v * 4294967296 < 4294967296 * 4294967296 := by omega
  have h_cv : c0v + c1v * 65536 + c2v * 4294967296 + c3v * 281474976710656
      < 4294967296 * 4294967296 := by omega
  apply BitVec.eq_of_toNat_eq
  -- Rewrite the toNat of (BitVec.ofNat 64 n) to (n % 2^64) using show to
  -- expose the structure with explicit literals, then strip the mods.
  -- The goal is: (ofNat 64 a_nat + ofNat 64 b_nat).toNat = (ofNat 64 c_nat).toNat
  -- After BitVec.toNat_add: ((ofNat 64 a_nat).toNat + (ofNat 64 b_nat).toNat) % 2^64
  --   = (ofNat 64 c_nat).toNat
  -- After BitVec.toNat_ofNat: (a_nat % 2^64 + b_nat % 2^64) % 2^64 = c_nat % 2^64
  -- We use `show` to introduce the explicit literal form and then close by omega
  -- chains from heq0, heq1, h_cout1_val.
  show (BitVec.ofNat 64 (a0v + a1v * 4294967296)
        + BitVec.ofNat 64 (b0v + b1v * 4294967296)).toNat
      = (BitVec.ofNat 64 (c0v + c1v * 65536 + c2v * 4294967296 + c3v * 281474976710656)).toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h_av, Nat.mod_eq_of_lt h_bv, Nat.mod_eq_of_lt h_cv]
  -- Goal: (a_nat + b_nat) % 2^64 = c_nat
  -- Carry chain: a_nat + b_nat = c_nat + k1 * 2^64.
  have h_lo : a0v + b0v = k0 * 4294967296 + c1v * 65536 + c0v := heq0
  have h_hi : a1v + b1v + k0 = k1 * 4294967296 + c3v * 65536 + c2v := heq1
  have h_sum : a0v + a1v * 4294967296 + (b0v + b1v * 4294967296)
      = (a0v + b0v) + (a1v + b1v) * 4294967296 := by ring
  rw [h_sum, h_lo]
  have h_rearrange : k0 * 4294967296 + c1v * 65536 + c0v + (a1v + b1v) * 4294967296
      = c0v + c1v * 65536 + (a1v + b1v + k0) * 4294967296 := by ring
  rw [h_rearrange, h_hi]
  have h_expand : c0v + c1v * 65536 + (k1 * 4294967296 + c3v * 65536 + c2v) * 4294967296
      = c0v + c1v * 65536 + c2v * 4294967296 + c3v * 281474976710656
        + k1 * (4294967296 * 4294967296) := by ring
  rw [h_expand]
  show (c0v + c1v * 65536 + c2v * 4294967296 + c3v * 281474976710656
        + k1 * (4294967296 * 4294967296)) % (4294967296 * 4294967296)
      = c0v + c1v * 65536 + c2v * 4294967296 + c3v * 281474976710656
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h_cv

end ZiskFv.Airs.BinaryAdd
