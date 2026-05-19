import ZiskFv.AirsClean.Mem.Soundness
import ZiskFv.Airs.Mem

/-!
# `Valid_Mem` ↔ `MemRow` compatibility bridge

Connects the v1 `Valid_Mem` record (parameterized over `[Circuit F ExtF C]`)
to the Clean Component's `MemRow`. The Bridge supplies:

* `rowAt v r` — projection `Valid_Mem → MemRow FGL` at row `r`
* `constraints_at v r` — the 9 F-typed Mem constraints at row `r`,
  expressed against the v1 record's named accessors
* `spec_of_valid v r h_assumptions h_constraints : Spec (rowAt v r)`
  — routes through the Component's `soundness` theorem

This is the v1 ↔ v2 compatibility shim. Phase D will remove the
`[Circuit F ExtF C]` parameterization; until then, consumers can
continue to take `m : Valid_Mem` and derive the Component Spec via
this bridge.

## Trust note

No new axioms. The Bridge is pure projection + soundness invocation.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL) (r : ℕ) : MemRow FGL where
  addr := v.addr r
  step := v.step r
  sel := v.sel r
  addr_changes := v.addr_changes r
  step_dual := v.step_dual r
  sel_dual := v.sel_dual r
  value_0 := v.value_0 r
  value_1 := v.value_1 r
  wr := v.wr r
  previous_step := v.previous_step r
  increment_0 := v.increment_0 r
  increment_1 := v.increment_1 r
  read_same_addr := v.read_same_addr r

/-- The 9 F-typed Mem row constraints at row `r`, expressed against a
    `Valid_Mem`. -/
def constraints_at (v : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL) (r : ℕ) : Prop :=
  v.sel_dual r * (1 - v.sel_dual r) = 0
  ∧ (1 - v.sel r) * v.sel_dual r = 0
  ∧ v.sel r * (1 - v.sel r) = 0
  ∧ v.addr_changes r * (1 - v.addr_changes r) = 0
  ∧ v.wr r * (1 - v.wr r) = 0
  ∧ v.wr r * (1 - v.sel r) = 0
  ∧ v.read_same_addr r - (1 - v.addr_changes r) * (1 - v.wr r) = 0
  ∧ (v.addr_changes r * (1 - v.wr r)) * v.value_0 r = 0
  ∧ (v.addr_changes r * (1 - v.wr r)) * v.value_1 r = 0

/-- **Bridge theorem.** Given a row of a `Valid_Mem` satisfying the
    9 Clean Component constraints and the boolean range assumptions,
    the Mem per-row Spec holds. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9

end ZiskFv.AirsClean.Mem
