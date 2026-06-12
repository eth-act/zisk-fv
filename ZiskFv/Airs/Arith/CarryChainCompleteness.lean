import Mathlib

import ZiskFv.Field.Goldilocks

/-!
# Arith carry-chain completeness helpers

These helpers build honest 16-bit chunk rows and field-solved carries for the
Clean Arith completeness proofs.  They do not assert range facts about the
carry witnesses; the base component only constrains them through the eight
carry-chain equations.
-/

namespace ZiskFv.Airs.ArithCarryChainCompleteness

open Goldilocks

/-- The 16-bit limb at index `k`, little-endian. -/
def chunk16 (x k : ℕ) : ℕ :=
  x / 65536 ^ k % 65536

lemma chunk16_lt (x k : ℕ) : chunk16 x k < 65536 := by
  unfold chunk16
  exact Nat.mod_lt _ (by norm_num)

lemma nat_decomp4 (x : ℕ) (h : x < 65536 ^ 4) :
    x = chunk16 x 0 + chunk16 x 1 * 65536 + chunk16 x 2 * 65536 ^ 2 +
      chunk16 x 3 * 65536 ^ 3 := by
  unfold chunk16 at *
  omega

lemma nat_decomp8 (x : ℕ) (h : x < 65536 ^ 8) :
    x = chunk16 x 0 + chunk16 x 1 * 65536 + chunk16 x 2 * 65536 ^ 2 +
      chunk16 x 3 * 65536 ^ 3 + chunk16 x 4 * 65536 ^ 4 +
      chunk16 x 5 * 65536 ^ 5 + chunk16 x 6 * 65536 ^ 6 +
      chunk16 x 7 * 65536 ^ 7 := by
  unfold chunk16 at *
  omega

lemma fgl_decomp4 (x : ℕ) (h : x < 65536 ^ 4) :
    (x : FGL) = chunk16 x 0 + chunk16 x 1 * 65536 +
      chunk16 x 2 * (65536 ^ 2 : FGL) + chunk16 x 3 * (65536 ^ 3 : FGL) := by
  have hcast := congrArg (fun n : ℕ => (n : FGL)) (nat_decomp4 x h)
  norm_num at hcast ⊢
  simpa using hcast

lemma fgl_decomp8 (x : ℕ) (h : x < 65536 ^ 8) :
    (x : FGL) = chunk16 x 0 + chunk16 x 1 * 65536 +
      chunk16 x 2 * (65536 ^ 2 : FGL) + chunk16 x 3 * (65536 ^ 3 : FGL) +
      chunk16 x 4 * (65536 ^ 4 : FGL) + chunk16 x 5 * (65536 ^ 5 : FGL) +
      chunk16 x 6 * (65536 ^ 6 : FGL) + chunk16 x 7 * (65536 ^ 7 : FGL) := by
  have hcast := congrArg (fun n : ℕ => (n : FGL)) (nat_decomp8 x h)
  norm_num at hcast ⊢
  simpa using hcast

lemma fgl_65536_ne_zero : (65536 : FGL) ≠ 0 := by
  decide

variable {F : Type} [Field F]

/-- Field-solved carry after equation 0. -/
def cc0 (B e0 : F) : F :=
  e0 / B

/-- Field-solved carry after equation 1. -/
def cc1 (B e0 e1 : F) : F :=
  (e0 + e1 * B) / B ^ 2

/-- Field-solved carry after equation 2. -/
def cc2 (B e0 e1 e2 : F) : F :=
  (e0 + e1 * B + e2 * B ^ 2) / B ^ 3

/-- Field-solved carry after equation 3. -/
def cc3 (B e0 e1 e2 e3 : F) : F :=
  (e0 + e1 * B + e2 * B ^ 2 + e3 * B ^ 3) / B ^ 4

/-- Field-solved carry after equation 4. -/
def cc4 (B e0 e1 e2 e3 e4 : F) : F :=
  (e0 + e1 * B + e2 * B ^ 2 + e3 * B ^ 3 + e4 * B ^ 4) / B ^ 5

/-- Field-solved carry after equation 5. -/
def cc5 (B e0 e1 e2 e3 e4 e5 : F) : F :=
  (e0 + e1 * B + e2 * B ^ 2 + e3 * B ^ 3 + e4 * B ^ 4 + e5 * B ^ 5) /
    B ^ 6

/-- Field-solved carry after equation 6. -/
def cc6 (B e0 e1 e2 e3 e4 e5 e6 : F) : F :=
  (e0 + e1 * B + e2 * B ^ 2 + e3 * B ^ 3 + e4 * B ^ 4 + e5 * B ^ 5 +
    e6 * B ^ 6) / B ^ 7

lemma chain_eq_0 {B e0 : F} (hB : B ≠ 0) :
    e0 - cc0 B e0 * B = 0 := by
  unfold cc0
  field_simp [hB]
  ring

lemma chain_eq_1 {B e0 e1 : F} (hB : B ≠ 0) :
    e1 + cc0 B e0 - cc1 B e0 e1 * B = 0 := by
  unfold cc0 cc1
  field_simp [hB]
  ring

lemma chain_eq_2 {B e0 e1 e2 : F} (hB : B ≠ 0) :
    e2 + cc1 B e0 e1 - cc2 B e0 e1 e2 * B = 0 := by
  unfold cc1 cc2
  field_simp [hB]
  ring

lemma chain_eq_3 {B e0 e1 e2 e3 : F} (hB : B ≠ 0) :
    e3 + cc2 B e0 e1 e2 - cc3 B e0 e1 e2 e3 * B = 0 := by
  unfold cc2 cc3
  field_simp [hB]
  ring

lemma chain_eq_4 {B e0 e1 e2 e3 e4 : F} (hB : B ≠ 0) :
    e4 + cc3 B e0 e1 e2 e3 - cc4 B e0 e1 e2 e3 e4 * B = 0 := by
  unfold cc3 cc4
  field_simp [hB]
  ring

lemma chain_eq_5 {B e0 e1 e2 e3 e4 e5 : F} (hB : B ≠ 0) :
    e5 + cc4 B e0 e1 e2 e3 e4 - cc5 B e0 e1 e2 e3 e4 e5 * B = 0 := by
  unfold cc4 cc5
  field_simp [hB]
  ring

lemma chain_eq_6 {B e0 e1 e2 e3 e4 e5 e6 : F} (hB : B ≠ 0) :
    e6 + cc5 B e0 e1 e2 e3 e4 e5 - cc6 B e0 e1 e2 e3 e4 e5 e6 * B = 0 := by
  unfold cc5 cc6
  field_simp [hB]
  ring

lemma chain_last {B e0 e1 e2 e3 e4 e5 e6 e7 : F} (hB : B ≠ 0)
    (h : e0 + e1 * B + e2 * B ^ 2 + e3 * B ^ 3 + e4 * B ^ 4 +
      e5 * B ^ 5 + e6 * B ^ 6 + e7 * B ^ 7 = 0) :
    e7 + cc6 B e0 e1 e2 e3 e4 e5 e6 = 0 := by
  unfold cc6
  field_simp [hB]
  linear_combination h

end ZiskFv.Airs.ArithCarryChainCompleteness
