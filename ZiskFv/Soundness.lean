import ZiskFv.Compliance.TraceLevelExport
import ZiskFv.Compliance.TraceLevelExport.RawRowDecode

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
    memory state. `hAvoidKnownBugs` excludes the enumerated forge defects.

    Every row then satisfies the canonical channel-balance conclusion
    (`= state_effect_via_channels …`). The per-row `OpEnvelope` is constructed
    from the trace inside each `stepStrong_<op>` — nothing is caller-supplied
    beyond the trace itself. -/
theorem root_soundness
    (numInstructions : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (rowDecodes : ∀ i : Fin numInstructions, RowDecode ziskTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace sailTrace i (ziskStep i) (inputsAgree i)) :
    ∀ i : Fin numInstructions, StepSound ziskTrace sailTrace i (ziskStep i) :=
  fun i =>
    stepSound_of_evidence ziskTrace sailTrace i (ziskStep i) (rowDecodes i) (inputsAgree i) (hAvoidKnownBugs i)

/-- ** The load-bearing soundness endpoint: the decode is grounded in the raw
    RISC-V program.

    Identical to `root_soundness` except the caller-asserted `rowDecodes` family
    is replaced by two genuinely thinner, soundness-critical inputs:
    * `rawProgram : Fin numInstructions → BitVec 32` — the raw RISC-V instruction
      words (a verifier-attached certificate, the binary the trace claims to run);
    * `hbind : ProgramBinding ziskTrace rawProgram` — the single op-agnostic
      certificate that the committed ROM holds exactly the serialized real-lowering
      of each raw word (run once per word, no per-op trust);
    * `rawRowDecodes : ∀ i, RawRowDecode …` — per row, the op-shaped raw-word fact
      plus the SAME non-ROM operand witnesses block 1 already carried.

    `rowDecodes_of_rawProgram` DERIVES the full block-1 `rowDecodes` family from
    these through the real Aeneas decode→lower→serialize pipeline, so the
    Main-ROM decode columns (op / flags / jmp_offset / ind_width) are no longer
    assumed — they are now load-bearing on `rawProgram`.  The body is exactly
    `root_soundness` with that derived `rowDecodes`; `root_soundness` and
    `AcceptedZiskTrace` are untouched. -/
theorem root_soundness_rawProgram
    (numInstructions : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (rawProgram : Fin numInstructions → BitVec 32)
    (hbind : RawProgramBinding.ProgramBinding ziskTrace rawProgram)
    (rawRowDecodes : ∀ i : Fin numInstructions, RawRowDecode ziskTrace i rawProgram (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace sailTrace i (ziskStep i) (inputsAgree i)) :
    ∀ i : Fin numInstructions, StepSound ziskTrace sailTrace i (ziskStep i) :=
  root_soundness numInstructions ziskTrace sailTrace ziskStep
    (rowDecodes_of_rawProgram ziskTrace ziskStep rawProgram hbind rawRowDecodes)
    inputsAgree hAvoidKnownBugs

end ZiskFv.Compliance
