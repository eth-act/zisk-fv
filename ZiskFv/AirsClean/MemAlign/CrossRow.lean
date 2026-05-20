import ZiskFv.AirsClean.MemAlign.Bridge

/-!
# MemAlign cross-row adjacency predicate

The 9 cross-row F-typed constraints of ZisK's MemAlign AIR:

* `delta_addr_definition` — `delta_addr` is the gated forward-
  difference of `addr` between row `r - 1` and row `r`. PIL maps to
  `constraint_29_every_row` in `build/extraction/Extraction/MemAlign.lean`.
* `down_to_up_continuity_N` (N = 0..7) — when `sel_down_to_up = 1`
  and `sel_N = 1`, the previous row's `reg_N` matches the current
  row's. PIL maps to `constraint_{1,3,5,7,9,11,13,15}_every_row`
  (the odd-numbered siblings of the forward-rotated continuity
  constraints, which use the unsupported positive `rowOffset = +1`
  and are accordingly skipped at extraction).

This is a standalone predicate — no Soundness proof is needed; the
9-conjunct equality is supplied by downstream callers as a single
hypothesis matching `Valid_MemAlign`'s cross-row constraint fields.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The 9 cross-row F-typed constraints at row `r`, referencing the
    previous row `r - 1`. -/
def cross_row_at (v : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL) (r : ℕ) : Prop :=
  v.delta_addr r - (v.addr r - v.addr (r - 1)) * (1 - v.reset r) = 0
  ∧ (v.reg_0 (r - 1) - v.reg_0 r) * v.sel_0 r * v.sel_down_to_up r = 0
  ∧ (v.reg_1 (r - 1) - v.reg_1 r) * v.sel_1 r * v.sel_down_to_up r = 0
  ∧ (v.reg_2 (r - 1) - v.reg_2 r) * v.sel_2 r * v.sel_down_to_up r = 0
  ∧ (v.reg_3 (r - 1) - v.reg_3 r) * v.sel_3 r * v.sel_down_to_up r = 0
  ∧ (v.reg_4 (r - 1) - v.reg_4 r) * v.sel_4 r * v.sel_down_to_up r = 0
  ∧ (v.reg_5 (r - 1) - v.reg_5 r) * v.sel_5 r * v.sel_down_to_up r = 0
  ∧ (v.reg_6 (r - 1) - v.reg_6 r) * v.sel_6 r * v.sel_down_to_up r = 0
  ∧ (v.reg_7 (r - 1) - v.reg_7 r) * v.sel_7 r * v.sel_down_to_up r = 0

end ZiskFv.AirsClean.MemAlign
