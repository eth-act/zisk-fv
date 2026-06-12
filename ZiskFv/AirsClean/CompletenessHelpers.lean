import ZiskFv.Field.Goldilocks

/-!
# Clean completeness helper lemmas

Small constructive helpers shared by honest-row completeness proofs.

## Trust note

No axioms. These are plain data constructors and elementary lemmas used by
builder-existential `ProverAssumptions`.
-/

namespace ZiskFv.AirsClean

open Goldilocks

/-- Encode a Boolean selector as a Goldilocks field element. -/
def boolF (b : Bool) : FGL := if b then 1 else 0

@[simp]
lemma boolF_false : boolF false = 0 := rfl

@[simp]
lemma boolF_true : boolF true = 1 := rfl

@[simp]
lemma boolF_booleanity (b : Bool) : boolF b * (1 - boolF b) = 0 := by
  cases b <;> simp [boolF]

@[simp]
lemma boolF_booleanity_add (b : Bool) : boolF b * (1 + -boolF b) = 0 := by
  simpa [sub_eq_add_neg] using boolF_booleanity b

/-- A small natural below a Goldilocks-bounded range remains small after casting to `FGL`. -/
lemma fgl_natCast_val_lt_of_lt {n bound : ℕ} (h_bound : bound ≤ GL_prime)
    (h_n : n < bound) : ((n : FGL).val < bound) := by
  rw [Fin.val_natCast]
  omega

end ZiskFv.AirsClean
