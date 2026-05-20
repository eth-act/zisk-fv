import ZiskFv.AirsClean.BinaryAdd.Spec
import Mathlib.Tactic.LinearCombination

/-!
# BinaryAdd Soundness (Clean form)

Proves that the four BinaryAdd constraints (declared in
`Constraints.lean`) imply the Spec (declared in `Spec.lean`):

  `cPacked = (packed32 a + packed32 b) % 2 ^ 64`.

## Adaptation insight

The spike's proof used the `ZMod.val_add_of_lt` / `ZMod.val_mul`
machinery with `[Fact (p > 2^65)]`. Specializing to `FGL = Fin GL_prime`
exposed a `Fin.val` ↔ `ZMod.val` pattern-matching gap.

**The clean workaround:** for `Fin n` the `.val` of arithmetic
*reduces definitionally* — `(a + b : Fin n).val = (a.val + b.val) % n`
and `(a * b : Fin n).val = (a.val * b.val) % n` are both `rfl`.
Combined with `Nat.mod_eq_of_lt`, this gives the same Nat-level
carry-chain equations the spike derived, but without going through
the `ZMod.val_*` lemma surface at all.

## Trust note

No axioms added. This file proves the Spec from the four constraints.
Step 4 (the next stacked commit) will build on this to provide the
compatibility lemma with `Valid_BinaryAdd` and retire one axiom
(floor 116 → 115).
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks

/-- All carry-chain sub-sums in BinaryAdd are bounded by
    `2 * 2^32 + 2^16 < 2^34 ≪ GL_prime`. -/
lemma GL_lower_bound : 2 ^ 34 < GL_prime := by decide

instance Fact_GL_one_lt : Fact (1 < GL_prime) := ⟨by decide⟩

/-- Boolean values: if `cout * (1 - cout) = 0` in `FGL`, then
    `cout.val ∈ {0, 1}`. -/
lemma bool_val_cases {x : FGL} (h : x * (1 + -x) = 0) :
    x.val = 0 ∨ x.val = 1 := by
  have h' : x * (1 - x) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h1
  · left
    subst h0; rfl
  · right
    have hx1 : x = 1 := by linear_combination -h1
    subst hx1; rfl

/-- `((c : ℕ) : FGL).val = c` whenever `c < GL_prime`. -/
lemma val_of_nat (c : ℕ) (h : c < GL_prime) : ((c : ℕ) : FGL).val = c := by
  simp [Fin.val_natCast, Nat.mod_eq_of_lt h]

/-- Lift an FGL equation to the Nat level. -/
lemma val_congr {x y : FGL} (h : x = y) : x.val = y.val :=
  congr_arg Fin.val h

/-- Specific literal vals. -/
lemma val_2_32 : ((4294967296 : ℕ) : FGL).val = 4294967296 := by decide
lemma val_2_16 : ((65536 : ℕ) : FGL).val = 65536 := by decide

/-! ## Carry-chain Nat-level equations -/

/-- Low-half carry chain: from the two F-level constraints (cout_0
    boolean + carry equation) plus 32-bit range bounds on operands
    and 16-bit range bounds on result chunks, derive the Nat
    equation `a_0 + b_0 = cout_0 * 2^32 + c_1 * 2^16 + c_0`. -/
lemma carry_chain_lo_nat
    {a_0 b_0 c_chunks_0 c_chunks_1 cout_0 : FGL}
    (h_bool : cout_0 * (1 + -cout_0) = 0)
    (h_carry : a_0 + b_0 + -(cout_0 * 4294967296 + c_chunks_1 * 65536 + c_chunks_0) = 0)
    (h_a0 : a_0.val < 2 ^ 32) (h_b0 : b_0.val < 2 ^ 32)
    (h_c0 : c_chunks_0.val < 2 ^ 16) (h_c1 : c_chunks_1.val < 2 ^ 16) :
    a_0.val + b_0.val
      = cout_0.val * 4294967296 + c_chunks_1.val * 65536 + c_chunks_0.val := by
  have hp := GL_lower_bound
  have h_cout_le : cout_0.val ≤ 1 := by
    rcases bool_val_cases h_bool with h | h <;> omega
  -- F-level equation
  have h_eq : a_0 + b_0 = cout_0 * 4294967296 + c_chunks_1 * 65536 + c_chunks_0 := by
    linear_combination h_carry
  -- Lift to Nat via val_congr
  have h_val := val_congr h_eq
  -- LHS: (a_0 + b_0).val = (a_0.val + b_0.val) % GL_prime, and sum < GL_prime.
  have h_lhs : (a_0 + b_0 : FGL).val = a_0.val + b_0.val := by
    show (a_0.val + b_0.val) % GL_prime = a_0.val + b_0.val
    apply Nat.mod_eq_of_lt; omega
  -- RHS sub-terms: use definitional reduction of Fin mul.
  have h_cout_mul : (cout_0 * 4294967296 : FGL).val = cout_0.val * 4294967296 := by
    show (cout_0.val * ((4294967296 : FGL).val)) % GL_prime = cout_0.val * 4294967296
    rw [show ((4294967296 : FGL).val) = 4294967296 from by decide]
    apply Nat.mod_eq_of_lt
    have : cout_0.val * 4294967296 ≤ 1 * 4294967296 := Nat.mul_le_mul_right _ h_cout_le
    omega
  have h_c1_mul : (c_chunks_1 * 65536 : FGL).val = c_chunks_1.val * 65536 := by
    show (c_chunks_1.val * ((65536 : FGL).val)) % GL_prime = c_chunks_1.val * 65536
    rw [show ((65536 : FGL).val) = 65536 from by decide]
    apply Nat.mod_eq_of_lt
    have : c_chunks_1.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : (0:Nat) < 65536)).mpr h_c1
    omega
  -- RHS sum: (cout_0 * 4294967296 + c_chunks_1 * 65536).val = ...
  have h_sum_mul : (cout_0 * 4294967296 + c_chunks_1 * 65536 : FGL).val
                 = cout_0.val * 4294967296 + c_chunks_1.val * 65536 := by
    show ((cout_0 * 4294967296 : FGL).val + (c_chunks_1 * 65536 : FGL).val) % GL_prime
       = cout_0.val * 4294967296 + c_chunks_1.val * 65536
    rw [h_cout_mul, h_c1_mul]
    apply Nat.mod_eq_of_lt
    have h1 : cout_0.val * 4294967296 ≤ 4294967296 := by
      have : cout_0.val * 4294967296 ≤ 1 * 4294967296 := Nat.mul_le_mul_right _ h_cout_le
      omega
    have h2 : c_chunks_1.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : (0:Nat) < 65536)).mpr h_c1
    omega
  -- Full RHS sum
  have h_rhs : (cout_0 * 4294967296 + c_chunks_1 * 65536 + c_chunks_0 : FGL).val
             = cout_0.val * 4294967296 + c_chunks_1.val * 65536 + c_chunks_0.val := by
    show ((cout_0 * 4294967296 + c_chunks_1 * 65536 : FGL).val + c_chunks_0.val) % GL_prime
       = cout_0.val * 4294967296 + c_chunks_1.val * 65536 + c_chunks_0.val
    rw [h_sum_mul]
    apply Nat.mod_eq_of_lt
    have h1 : cout_0.val * 4294967296 ≤ 4294967296 := by
      have : cout_0.val * 4294967296 ≤ 1 * 4294967296 := Nat.mul_le_mul_right _ h_cout_le
      omega
    have h2 : c_chunks_1.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : (0:Nat) < 65536)).mpr h_c1
    omega
  rw [h_lhs, h_rhs] at h_val
  exact h_val

/-- High-half carry chain — same shape as `carry_chain_lo_nat`, with
    cout_0 (Nat-bounded ≤ 1) added to the LHS. -/
lemma carry_chain_hi_nat
    {a_1 b_1 c_chunks_2 c_chunks_3 cout_0 cout_1 : FGL}
    (h_bool_1 : cout_1 * (1 + -cout_1) = 0)
    (h_cout0_le : cout_0.val ≤ 1)
    (h_carry : a_1 + b_1 + cout_0 + -(cout_1 * 4294967296 + c_chunks_3 * 65536 + c_chunks_2) = 0)
    (h_a1 : a_1.val < 2 ^ 32) (h_b1 : b_1.val < 2 ^ 32)
    (h_c2 : c_chunks_2.val < 2 ^ 16) (h_c3 : c_chunks_3.val < 2 ^ 16) :
    a_1.val + b_1.val + cout_0.val
      = cout_1.val * 4294967296 + c_chunks_3.val * 65536 + c_chunks_2.val := by
  have hp := GL_lower_bound
  have h_cout1_le : cout_1.val ≤ 1 := by
    rcases bool_val_cases h_bool_1 with h | h <;> omega
  have h_eq : a_1 + b_1 + cout_0 = cout_1 * 4294967296 + c_chunks_3 * 65536 + c_chunks_2 := by
    linear_combination h_carry
  have h_val := val_congr h_eq
  -- LHS: (a_1 + b_1 + cout_0).val
  have h_lhs_inner : (a_1 + b_1 : FGL).val = a_1.val + b_1.val := by
    show (a_1.val + b_1.val) % GL_prime = a_1.val + b_1.val
    apply Nat.mod_eq_of_lt; omega
  have h_lhs : (a_1 + b_1 + cout_0 : FGL).val = a_1.val + b_1.val + cout_0.val := by
    show ((a_1 + b_1 : FGL).val + cout_0.val) % GL_prime = _
    rw [h_lhs_inner]
    apply Nat.mod_eq_of_lt; omega
  -- RHS: same shape as lo
  have h_cout_mul : (cout_1 * 4294967296 : FGL).val = cout_1.val * 4294967296 := by
    show (cout_1.val * ((4294967296 : FGL).val)) % GL_prime = cout_1.val * 4294967296
    rw [show ((4294967296 : FGL).val) = 4294967296 from by decide]
    apply Nat.mod_eq_of_lt
    have : cout_1.val * 4294967296 ≤ 1 * 4294967296 := Nat.mul_le_mul_right _ h_cout1_le
    omega
  have h_c3_mul : (c_chunks_3 * 65536 : FGL).val = c_chunks_3.val * 65536 := by
    show (c_chunks_3.val * ((65536 : FGL).val)) % GL_prime = c_chunks_3.val * 65536
    rw [show ((65536 : FGL).val) = 65536 from by decide]
    apply Nat.mod_eq_of_lt
    have : c_chunks_3.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : (0:Nat) < 65536)).mpr h_c3
    omega
  have h_sum_mul : (cout_1 * 4294967296 + c_chunks_3 * 65536 : FGL).val
                 = cout_1.val * 4294967296 + c_chunks_3.val * 65536 := by
    show ((cout_1 * 4294967296 : FGL).val + (c_chunks_3 * 65536 : FGL).val) % GL_prime = _
    rw [h_cout_mul, h_c3_mul]
    apply Nat.mod_eq_of_lt
    have h1 : cout_1.val * 4294967296 ≤ 4294967296 := by
      have : cout_1.val * 4294967296 ≤ 1 * 4294967296 := Nat.mul_le_mul_right _ h_cout1_le
      omega
    have h2 : c_chunks_3.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : (0:Nat) < 65536)).mpr h_c3
    omega
  have h_rhs : (cout_1 * 4294967296 + c_chunks_3 * 65536 + c_chunks_2 : FGL).val
             = cout_1.val * 4294967296 + c_chunks_3.val * 65536 + c_chunks_2.val := by
    show ((cout_1 * 4294967296 + c_chunks_3 * 65536 : FGL).val + c_chunks_2.val) % GL_prime = _
    rw [h_sum_mul]
    apply Nat.mod_eq_of_lt
    have h1 : cout_1.val * 4294967296 ≤ 4294967296 := by
      have : cout_1.val * 4294967296 ≤ 1 * 4294967296 := Nat.mul_le_mul_right _ h_cout1_le
      omega
    have h2 : c_chunks_3.val * 65536 < 65536 * 65536 :=
      (Nat.mul_lt_mul_right (by omega : (0:Nat) < 65536)).mpr h_c3
    omega
  rw [h_lhs, h_rhs] at h_val
  exact h_val

/-! ## Row-level soundness theorem -/

/-- BinaryAdd row soundness from explicit column range bounds: the four
    constraints + the 8 `bits(N)` column range bounds imply the Spec.

    This is the form the Clean `Component`'s `soundness` field consumes —
    the range bounds arrive from `range_bus_sound` (the range-checker bus),
    so the Component's `Assumptions` can be `True`. The carry-pin conjuncts
    of `Assumptions` are *not* needed here. -/
theorem soundness_of_ranges (row : BinaryAddRow FGL)
    (h_a0 : row.a_0.val < 2 ^ 32) (h_a1 : row.a_1.val < 2 ^ 32)
    (h_b0 : row.b_0.val < 2 ^ 32) (h_b1 : row.b_1.val < 2 ^ 32)
    (h_c0 : row.c_chunks_0.val < 2 ^ 16) (h_c1 : row.c_chunks_1.val < 2 ^ 16)
    (h_c2 : row.c_chunks_2.val < 2 ^ 16) (h_c3 : row.c_chunks_3.val < 2 ^ 16)
    (h_bool_0 : row.cout_0 * (1 + -row.cout_0) = 0)
    (h_carry_0 :
      row.a_0 + row.b_0
        + -(row.cout_0 * 4294967296 + row.c_chunks_1 * 65536 + row.c_chunks_0)
      = 0)
    (h_bool_1 : row.cout_1 * (1 + -row.cout_1) = 0)
    (h_carry_1 :
      row.a_1 + row.b_1 + row.cout_0
        + -(row.cout_1 * 4294967296 + row.c_chunks_3 * 65536 + row.c_chunks_2)
      = 0) :
    Spec row := by
  have hlo := carry_chain_lo_nat h_bool_0 h_carry_0 h_a0 h_b0 h_c0 h_c1
  have h_cout0_le : row.cout_0.val ≤ 1 := by
    rcases bool_val_cases h_bool_0 with h | h <;> omega
  have hhi := carry_chain_hi_nat h_bool_1 h_cout0_le h_carry_1
    h_a1 h_b1 h_c2 h_c3
  have h_cout1_le : row.cout_1.val ≤ 1 := by
    rcases bool_val_cases h_bool_1 with h | h <;> omega
  simp only [Spec, cPacked, packed32]
  omega

/-- BinaryAdd row soundness: the four constraints + range/carry
    assumptions imply the Spec. (Thin wrapper over `soundness_of_ranges`
    unpacking the bundled `Assumptions`; the carry-pin conjuncts are
    unused.) -/
theorem soundness (row : BinaryAddRow FGL)
    (h_assumptions : Assumptions row)
    (h_bool_0 : row.cout_0 * (1 + -row.cout_0) = 0)
    (h_carry_0 :
      row.a_0 + row.b_0
        + -(row.cout_0 * 4294967296 + row.c_chunks_1 * 65536 + row.c_chunks_0)
      = 0)
    (h_bool_1 : row.cout_1 * (1 + -row.cout_1) = 0)
    (h_carry_1 :
      row.a_1 + row.b_1 + row.cout_0
        + -(row.cout_1 * 4294967296 + row.c_chunks_3 * 65536 + row.c_chunks_2)
      = 0) :
    Spec row := by
  obtain ⟨h_a0, h_a1, h_b0, h_b1, h_c0, h_c1, h_c2, h_c3, _, _⟩ := h_assumptions
  exact soundness_of_ranges row h_a0 h_a1 h_b0 h_b1 h_c0 h_c1 h_c2 h_c3
    h_bool_0 h_carry_0 h_bool_1 h_carry_1

end ZiskFv.AirsClean.BinaryAdd
