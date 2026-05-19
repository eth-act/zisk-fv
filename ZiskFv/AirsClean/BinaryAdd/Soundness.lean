import ZiskFv.AirsClean.BinaryAdd.Constraints
import Mathlib.Tactic.LinearCombination

/-!
# BinaryAdd Soundness helpers (Clean form)

Helper lemmas used by the per-row carry-chain soundness proofs.
Specialised from the spike branch's
`ZiskFvClean/BinaryAdd/Soundness.lean` (generic `[Fact (p > 2^65)]`)
to Goldilocks (`FGL = Fin GL_prime`).

## Adaptation status — partial

The spike's proof relies on `ZMod.val_add_of_lt` / `ZMod.val_mul` /
`ZMod.val_natCast`. For `FGL = Fin GL_prime`, the `.val` projection
is `Fin.val`, which is defeq to `ZMod.val` (since `ZMod n = Fin n`
for `n ≠ 0`) but the pattern-matching in `rw` lemmas doesn't always
unify cleanly.

This file lands the FGL adaptation that *does* work:

* `GL_lower_bound : 2 ^ 34 < GL_prime`
* `Fact_GL_one_lt`
* `bool_val_cases` (via direct `subst`)
* `val_of_nat` (via `Fin.val_natCast` + `Nat.mod_eq_of_lt`)
* `val_congr` (via `Fin.val`)

The full carry-chain `Nat`-level reductions need a few more
elaboration hints to bridge `Fin.val` to `ZMod.val_*` lemmas, and
are deferred to the next stacked PR in the series. They DO NOT block
the Phase 4 wrapper pattern (already validated in
`ZiskFv/Vm/Probe_ADD.lean`).

## Trust note

No axioms. Pure scaffolding.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks

/-- All carry-chain sub-sums in BinaryAdd are bounded by `2 * 2^32 +
    2^16 < 2^34 ≪ GL_prime`. -/
lemma GL_lower_bound : 2 ^ 34 < GL_prime := by decide

/-- Convenience: `1 < GL_prime` (needed for some `ZMod.val_one`-style lemmas). -/
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

/-- Lift an FGL equation to the Nat level via `Fin.val`. -/
lemma val_congr {x y : FGL} (h : x = y) : x.val = y.val :=
  congr_arg Fin.val h

/-! ## Carry-chain Nat-level equations (deferred)

The carry-chain Nat-level reductions (porting ~250 LoC from the
spike) need additional elaboration hints beyond `(n := GL_prime)`:
specifically, the `Fin n → ZMod n` rewrite chain hits `↑(a * ↑c)`
pattern-mismatch when `ZMod.val_mul`'s LHS is `(?a * ?b).val`.

The fix is one of:
* Use `Fin.val_mul` / `Fin.val_add` variants if Mathlib has them
* Insert a `change ZMod.val ...` step to coerce the goal
* Provide a local `Fin → ZMod` cast lemma

Deferred to a follow-up PR in this stack — once unblocked, the
spike's proof transfers verbatim with `(n := GL_prime)` annotations.

The probe `ZiskFv/Vm/Probe_ADD.lean` already validates Phase 4's
wrapper pattern WITHOUT this proof (it routes through the existing
`equiv_ADD` and the channel-balance bridge), so this gap doesn't
block the rest of the stack. -/

end ZiskFv.AirsClean.BinaryAdd
