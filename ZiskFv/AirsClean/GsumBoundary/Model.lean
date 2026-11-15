import Extraction.LookupWiring

/-!
# Typed source-local finalizer model

The equation is the source's guarded final-row invariant, not a theorem that
numeric `gsum` realizes Clean channel balance. AIR and AIR-group cells are
independent. This module imports no generated per-AIR simp declarations, so
local source boundaries can reuse it without importing the leaf weld packet.
-/

namespace ZiskFv.AirsClean.GsumBoundary

open Extraction.LookupWiring

/-- The final-row invariant, including the source's selector guard. -/
def Closed {F : Type} [Field F] (selector contribution running direct : F) : Prop :=
  selector * (contribution - running - direct) = 0

/-- Constructibility of the local boundary, not logUp soundness. -/
theorem closed_constructible {F : Type} [Field F] (selector running direct : F) :
    Closed selector (running + direct) running direct := by
  simp [Closed]

/-- An enabled selector fixes the contribution to running sum plus direct terms. -/
theorem closed_at_final_row {F : Type} [Field F] (contribution running direct : F) :
    Closed 1 contribution running direct ↔ contribution = running + direct := by
  simp only [Closed, one_mul, sub_sub, sub_eq_zero]

/-- Independent typed source cells. AIR values and AIR-group values are
 different functions; offsets are signed relative to the current physical row. -/
structure Source (F : Type) where
  witness : Nat → Nat → Int → F
  fixed : Nat → Int → F
  airValue : Nat → F
  airGroupValue : Nat → F

/-- Closed interpretation for finalizer syntax only. Unsupported constructors
and literals return `none`, never an invented field value. -/
def Source.eval {F : Type} [Field F] (source : Source F) : Expr → Option F
  | .constant "0" => some 0
  | .witness stage column offset => some (source.witness stage column offset)
  | .fixed column offset => some (source.fixed column offset)
  | .airValue index => some (source.airValue index)
  | .airGroupValue index => some (source.airGroupValue index)
  | .add lhs rhs => do return (← source.eval lhs) + (← source.eval rhs)
  | .sub lhs rhs => do return (← source.eval lhs) - (← source.eval rhs)
  | .mul lhs rhs => do return (← source.eval lhs) * (← source.eval rhs)
  | _ => none

def Source.Holds {F : Type} [Field F] (source : Source F) (constraint : Expr) : Prop :=
  source.eval constraint = some 0

theorem typedSource_rejects_unsupported {F : Type} [Field F] (source : Source F) :
    source.eval (.challenge 2 0) = none ∧
    source.eval (.opaque "unsupported" "payload") = none := by
  exact ⟨rfl, rfl⟩

end ZiskFv.AirsClean.GsumBoundary
