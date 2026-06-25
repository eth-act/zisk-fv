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

    For each instruction i the per-step hypotheses split three ways:
    `ziskStep` is what the ZisK machine did (its decoded op + operand/dest
    indices + committed bus row); `rowDecodes` is the circuit-checkable fact that
    the row is a well-formed instance of that op; and `inputsAgree` is the
    cross-world fact that ZisK's inputs equal the Sail model's register / PC /
    memory state. `h_known_bugs` excludes the enumerated forge defects.

    Every row then satisfies the canonical channel-balance conclusion
    (`= state_effect_via_channels …`). The per-row `OpEnvelope` is constructed
    from the trace inside each `stepStrong_<op>` — nothing is caller-supplied
    beyond the trace itself. -/
theorem root_soundness
    (numInstructions : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (rowDecodes : ∀ i : Fin numInstructions, RowDecode ziskTrace sailTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (h_known_bugs : ∀ i : Fin numInstructions,
      StepNoKnownDefect ziskTrace sailTrace i (ziskStep i) (rowDecodes i) (inputsAgree i)) :
    ∀ i : Fin numInstructions, StepFaithful ziskTrace sailTrace i (ziskStep i) :=
  fun i =>
    stepFaithful_of_evidence ziskTrace sailTrace i (ziskStep i) (rowDecodes i) (inputsAgree i) (h_known_bugs i)

end ZiskFv.Compliance
