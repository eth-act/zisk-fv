import ZiskFv.Compliance.TraceLevelExport

/-!
# Root soundness

The headline soundness statement of the project, factored out of the
trace-level export development for visibility.  It sits parallel to
`ZiskFv.Compliance` and re-exports the single endpoint theorem.
-/

namespace ZiskFv.Compliance

/-- **Root soundness — trace-level export (#61).**

    From an accepted full-ensemble trace, a program binding, a per-row
    classification of all 63 RV64IM archetypes, and a per-row defect-exclusion
    hypothesis (`h_known_bugs`), every row satisfies the canonical channel-balance
    conclusion (`= state_effect_via_channels …`). The per-row `OpEnvelope` is
    constructed from the trace inside each `stepStrong_<op>` — nothing is
    caller-supplied beyond the trace itself. -/
theorem root_soundness
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (rowData : ∀ i : Fin trace.numInstructions, StrongRowConstructionData trace binding i)
    (h_known_bugs : ∀ i : Fin trace.numInstructions, StepNoKnownDefect trace binding i (rowData i)) :
    ∀ i : Fin trace.numInstructions, StepComplianceStrong trace binding i (rowData i) :=
  fun i => stepComplianceStrong_of_rowData trace binding i (rowData i) (h_known_bugs i)

end ZiskFv.Compliance
