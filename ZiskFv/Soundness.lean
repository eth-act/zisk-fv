import ZiskFv.Compliance.TraceLevelExport
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode

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
    indices + committed bus row); `programDecodes` is the circuit-checkable fact
    that the row is a well-formed instance of that op, stated about the
    COMMITTED program `trace.program` (the ROM the circuit already checks): the
    witness-row decode columns are no longer assumed, they are DERIVED from the
    program-level decode facts via the in-circuit ROM lookup
    (`rowDecode_of_programDecode`, block 1); and `inputsAgree` is the cross-world
    fact that ZisK's inputs equal the Sail model's register / PC / memory state.
    `hAvoidKnownBugs` excludes the enumerated forge defects.

    `bootSeed` is the single named **cross-row memory seed** premise: the segment's
    initial memory state at segment entry, together with the one consistent
    per-row memory-evolution chain (`RowTraceCoherence` over the whole consumed
    memory-bus row sequence).  Every load's and store's memory-coherence fact is
    *derived* from this one seed (`memEvidence_of_bootSeed`), rather than each of
    the ten memory ops carrying its own copy.  It is a named external-trust premise
    (the same class as channel-balance), documented in
    `trust/trusted-base.md` — it is genuinely irreducible at the single-segment
    level (a segment does not contain its own starting state; it is carried in from
    the previous segment / boot), and driving it to zero is #115 / #119.  It is a
    *memory* seed: the coherence chain constrains only memory; PC / registers are
    pinned only incidentally through the initial-state snapshot (per-step next-PC is
    discharged separately by the `AcceptedZiskTrace` PC-handshake certificate).

    Every row then satisfies the canonical channel-balance conclusion
    (`= state_effect_via_channels …`). The per-row `OpEnvelope` is constructed
    from the trace inside each `stepStrong_<op>` — nothing is caller-supplied
    beyond the trace itself. -/
theorem root_soundness
    (numInstructions : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (programDecodes : ∀ i : Fin numInstructions, ProgramDecode ziskTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions, StepSound ziskTrace sailTrace i (ziskStep i) :=
  fun i =>
    stepSound_of_evidence ziskTrace sailTrace i (ziskStep i)
      (rowDecode_of_programDecode ziskTrace i (programDecodes i)) (inputsAgree i)
      (memEvidence_of_bootSeed bootSeed i) (hAvoidKnownBugs i)

end ZiskFv.Compliance
