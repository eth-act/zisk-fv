import ZiskFv.Compliance.TraceLevelExport

/-!
# Root soundness

The headline soundness statement of the project, factored out of the
trace-level export development for visibility. It sits parallel to
`ZiskFv.Compliance` and re-exports the single endpoint theorem.
-/

namespace ZiskFv.Compliance

/-- ** The top-level global soundness theorem: given a satisfying assignment of circuits
    that does not involve any explicitly enumerated bugs, the zisk machine state transition
    agrees with the Sail machine state transition.

    An AcceptedZiskTrace is a set of constraints, and a witness that satisfies those constraints and the
    channel balancing constraint enfoced in the proving system through a lookup argument.

    A SailTrace is a choice of which table in the witness is the Main execution table, together
    with the sequence of Sail machine states the program steps through and the facts that pin that
    table into the witness : that it really occurs in it, that it really is the Main component, and
    that it has one row per instruction.

    rowData is the assumption that, for each instruction, ZisK's inputs match the Sail model's
    inputs — same opcode, same operand and PC values.

    From an accepted full-ensemble trace, a program binding, a per-row
    classification of all 63 RV64IM archetypes, and a per-row defect-exclusion
    hypothesis (`h_known_bugs`), every row satisfies the canonical channel-balance
    conclusion (`= state_effect_via_channels …`). The per-row `OpEnvelope` is
    constructed from the trace inside each `stepStrong_<op>` — nothing is
    caller-supplied beyond the trace itself. -/
theorem root_soundness
    (ziskTrace : AcceptedZiskTrace)
    (sailTrace : SailTrace ziskTrace)
    (rowData : ∀ i : Fin ziskTrace.numInstructions, StrongRowConstructionData ziskTrace sailTrace i)
    (h_known_bugs : ∀ i : Fin ziskTrace.numInstructions, StepNoKnownDefect ziskTrace sailTrace i (rowData i)) :
    ∀ i : Fin ziskTrace.numInstructions, StepFaithful ziskTrace sailTrace i (rowData i) :=
  fun i => stepFaithful_of_evidence ziskTrace sailTrace i (rowData i) (h_known_bugs i)

end ZiskFv.Compliance
