import ZiskFv.Compliance.AddFaithfulPaddedWitness
import ZiskFv.Compliance.RegisterBoundaryAnchor

/-!
# The boundary landing point is reached on a concrete accepted trace

`boundarySuppliedAt_reload_message` and its two projections are all conditional on
`BoundarySuppliedAt`. This file discharges that hypothesis on `addFaithfulAcceptedTrace` — the
two-row `add x1,x1,x1` trace that also serves as `root_soundness`'s non-vacuity witness — so the
anchor results are known to have content rather than being true for want of an instance.

The `a` slot of row `0` is a register read (`add x1,x1,x1` sets `a_src_reg`), which is all
`exists_boundarySuppliedSite` needs.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.Main (componentWithRomMemAndOpBus)
open ZiskFv.Compliance.AddFaithfulPaddedWitness
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep)

/-- Row `0` of the faithful trace reads `x1` through the `a` slot. -/
theorem addFaithfulMainTable_a_selector_zero
    (h : (0 : ℕ) < addFaithfulMainTable.table.length) :
    RegSlot.a.selector
        (eval (addFaithfulMainTable.environment (addFaithfulMainTable.table.get ⟨0, h⟩))
          (componentWithRomMemAndOpBus 2 addFaithfulProgram).rowInputVar) = 1 := by
  rw [show addFaithfulMainTable.environment (addFaithfulMainTable.table.get ⟨0, h⟩)
      = addFaithfulMainTable.environmentAt ⟨0, by simp⟩ from rfl,
    addFaithfulMainTable_evalAt_zero]
  rfl

/-- **`BoundarySuppliedAt` is inhabited.** Some site of the faithful accepted trace has its
    register read answered by the `RegisterBoundary`, so `boundarySuppliedAt_reload_message` and
    `boundarySuppliedAt_reload_values` say something about a real trace. -/
theorem exists_boundarySuppliedAt_addFaithful :
    ∃ p : RegWalkStep, BoundarySuppliedAt addFaithfulAcceptedTrace p := by
  have h_len : (0 : ℕ) < addFaithfulMainTable.table.length := by simp
  exact exists_boundarySuppliedSite addFaithfulAcceptedTrace
    (table := addFaithfulMainTable)
    (addFaithfulAcceptedTrace_mainTable_eq ▸ addFaithfulAcceptedTrace.mainTable_mem)
    rfl
    (List.get_mem _ _)
    RegSlot.a
    (addFaithfulMainTable_a_selector_zero h_len)

end ZiskFv.Compliance
