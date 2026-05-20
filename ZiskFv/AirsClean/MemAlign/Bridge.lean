import ZiskFv.AirsClean.MemAlign.Soundness
import ZiskFv.Airs.MemAlign

/-!
# `Valid_MemAlign` ↔ `MemAlignRow` compatibility bridge

The Bridge routes v1 `Valid_MemAlign` consumers through the Clean
Component's per-row Spec (16 clauses). Cross-row continuity clauses
(`down_to_up_continuity_N`, `delta_addr_definition`) live in a
separate `cross_row_at` predicate (`CrossRow.lean`) that downstream
consumers invoke once the per-row Spec is established.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL) (r : ℕ) :
    MemAlignRow FGL where
  addr := v.addr r
  offset := v.offset r
  width := v.width r
  wr := v.wr r
  pc := v.pc r
  reset := v.reset r
  sel_up_to_down := v.sel_up_to_down r
  sel_down_to_up := v.sel_down_to_up r
  reg_0 := v.reg_0 r
  reg_1 := v.reg_1 r
  reg_2 := v.reg_2 r
  reg_3 := v.reg_3 r
  reg_4 := v.reg_4 r
  reg_5 := v.reg_5 r
  reg_6 := v.reg_6 r
  reg_7 := v.reg_7 r
  sel_0 := v.sel_0 r
  sel_1 := v.sel_1 r
  step := v.step r
  sel_2 := v.sel_2 r
  sel_3 := v.sel_3 r
  sel_4 := v.sel_4 r
  sel_5 := v.sel_5 r
  sel_6 := v.sel_6 r
  sel_7 := v.sel_7 r
  sel_prove := v.sel_prove r
  preL1 := v.preL1 r
  delta_addr := v.delta_addr r
  value_0 := v.value_0 r
  value_1 := v.value_1 r

/-- The 16 per-row F-typed constraints at row `r`, expressed against
    a `Valid_MemAlign`. -/
def constraints_at (v : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL) (r : ℕ) : Prop :=
  v.wr r * (1 - v.wr r) = 0
  ∧ v.reset r * (1 - v.reset r) = 0
  ∧ v.sel_up_to_down r * (1 - v.sel_up_to_down r) = 0
  ∧ v.sel_down_to_up r * (1 - v.sel_down_to_up r) = 0
  ∧ v.sel_0 r * (1 - v.sel_0 r) = 0
  ∧ v.sel_1 r * (1 - v.sel_1 r) = 0
  ∧ v.sel_2 r * (1 - v.sel_2 r) = 0
  ∧ v.sel_3 r * (1 - v.sel_3 r) = 0
  ∧ v.sel_4 r * (1 - v.sel_4 r) = 0
  ∧ v.sel_5 r * (1 - v.sel_5 r) = 0
  ∧ v.sel_6 r * (1 - v.sel_6 r) = 0
  ∧ v.sel_7 r * (1 - v.sel_7 r) = 0
  ∧ v.preL1 r * v.pc r = 0
  ∧ v.sel_prove r * (v.sel_up_to_down r + v.sel_down_to_up r) = 0
  ∧ v.value_0 r -
      (v.sel_prove r *
        (v.sel_0 r * (v.reg_0 r + v.reg_1 r * 256 + v.reg_2 r * 65536 + v.reg_3 r * 16777216)
         + v.sel_1 r * (v.reg_1 r + v.reg_2 r * 256 + v.reg_3 r * 65536 + v.reg_4 r * 16777216)
         + v.sel_2 r * (v.reg_2 r + v.reg_3 r * 256 + v.reg_4 r * 65536 + v.reg_5 r * 16777216)
         + v.sel_3 r * (v.reg_3 r + v.reg_4 r * 256 + v.reg_5 r * 65536 + v.reg_6 r * 16777216)
         + v.sel_4 r * (v.reg_4 r + v.reg_5 r * 256 + v.reg_6 r * 65536 + v.reg_7 r * 16777216)
         + v.sel_5 r * (v.reg_5 r + v.reg_6 r * 256 + v.reg_7 r * 65536 + v.reg_0 r * 16777216)
         + v.sel_6 r * (v.reg_6 r + v.reg_7 r * 256 + v.reg_0 r * 65536 + v.reg_1 r * 16777216)
         + v.sel_7 r * (v.reg_7 r + v.reg_0 r * 256 + v.reg_1 r * 65536 + v.reg_2 r * 16777216))
       + (v.sel_up_to_down r + v.sel_down_to_up r)
         * (v.reg_0 r + v.reg_1 r * 256 + v.reg_2 r * 65536 + v.reg_3 r * 16777216)) = 0
  ∧ v.value_1 r -
      (v.sel_prove r *
        (v.sel_0 r * (v.reg_4 r + v.reg_5 r * 256 + v.reg_6 r * 65536 + v.reg_7 r * 16777216)
         + v.sel_1 r * (v.reg_5 r + v.reg_6 r * 256 + v.reg_7 r * 65536 + v.reg_0 r * 16777216)
         + v.sel_2 r * (v.reg_6 r + v.reg_7 r * 256 + v.reg_0 r * 65536 + v.reg_1 r * 16777216)
         + v.sel_3 r * (v.reg_7 r + v.reg_0 r * 256 + v.reg_1 r * 65536 + v.reg_2 r * 16777216)
         + v.sel_4 r * (v.reg_0 r + v.reg_1 r * 256 + v.reg_2 r * 65536 + v.reg_3 r * 16777216)
         + v.sel_5 r * (v.reg_1 r + v.reg_2 r * 256 + v.reg_3 r * 65536 + v.reg_4 r * 16777216)
         + v.sel_6 r * (v.reg_2 r + v.reg_3 r * 256 + v.reg_4 r * 65536 + v.reg_5 r * 16777216)
         + v.sel_7 r * (v.reg_3 r + v.reg_4 r * 256 + v.reg_5 r * 65536 + v.reg_6 r * 16777216))
       + (v.sel_up_to_down r + v.sel_down_to_up r)
         * (v.reg_4 r + v.reg_5 r * 256 + v.reg_6 r * 65536 + v.reg_7 r * 16777216)) = 0

theorem spec_of_valid
    (v : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
    h_constraints
  exact soundness (rowAt v r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

end ZiskFv.AirsClean.MemAlign
