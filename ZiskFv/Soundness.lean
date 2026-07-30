import ZiskFv.Compliance.TraceLevelExport
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode
import ZiskFv.Compliance.TraceLevelExport.RawProgramDecode

/-!
# Root soundness

The headline soundness statement of the project, factored out of the trace-level
export development for visibility. It sits parallel to `ZiskFv.Compliance`.

`root_soundness` is the single audit entrypoint: the entire compliance statement
is reachable from it. `stepSound_of_programDecodes` is the interior layer it
calls, kept as a separate declaration because the six concrete trace
instantiations target it directly.
-/

namespace ZiskFv.Compliance

/-- Soundness for every executed step, indexed by the COMMITTED-program decode
    family: given a satisfying assignment of circuits that does not involve any
    explicitly enumerated bugs, the zisk machine state transition agrees with the
    Sail machine state transition.

    This is the interior layer of the audit tree, not the entrypoint. The public
    endpoint is `root_soundness` below, which CONSTRUCTS `programDecodes` from raw
    RV64IM words through the production lowerer instead of taking it as a premise.

    An AcceptedZiskTrace is a set of constraints, and a witness that satisfies those constraints and the
    channel balancing constraint enfoced in the proving system through a lookup argument.

    A SailTrace is the sequence of Sail machine states for the executed steps. The Main execution
    table is derived from the witness and has a row for every executed step; its physical row count
    and the committed ROM length may both be larger than that executed-step count.

    For each executed step i the per-step hypotheses split three ways:
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
theorem stepSound_of_programDecodes
    (numInstructions : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (programDecodes : ∀ i : Fin numInstructions, ProgramDecode ziskTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i (programDecodes i)) :=
  fun i =>
    stepSound_of_evidence ziskTrace sailTrace i (ziskStep i)
      (rowDecode_of_programDecode ziskTrace i (programDecodes i)) (inputsAgree i)
      (memEvidence_of_bootSeed bootSeed i) (hAvoidKnownBugs i)

/-- **The root soundness theorem — the entrypoint for an audit of this project's
    soundness claim.** The entire compliance statement is reachable from here:
    every premise below is either discharged inside this theorem or is a named
    trust premise documented in `trust/trusted-base.md`.

    Given an accepted ZisK trace, the raw RV64IM program image, and an exact
    binding of that image to the committed ROM, every executed step's ZisK state
    transition agrees with the Sail/RISC-V transition.

    The per-instruction decode family consumed by `stepSound_of_programDecodes` is
    CONSTRUCTED here (`programDecode_of_rawProgramDecode`, 63 arms) by running the
    Aeneas-extracted production lowerer on the raw word, rather than being supplied
    by the caller. `programBinding` states that the committed ROM holds exactly the
    serialized lowering of `rawProgram` — gap-free, in program order, with two-row
    (unaligned JALR) expansions occupying adjacent physical slots.

    Residual boundaries, all named in `trust/trusted-base.md`: the layout maps
    `start` / `addr` are caller-supplied (their meaning is that architectural word
    `k` sits at the location assigned to `k`, not that the map came from a
    particular linker image); grounding the same word in Sail's `ext_decode` is
    #172; and identifying `rawProgram` with the intended compiled binary is the
    external compile/commitment boundary.

    NON-VACUITY (#320): `programBinding` and `rawProgramDecodes` do not yet have
    in-tree witnesses. The six concrete instantiations (`addSpin`, `addAddiSpin`,
    `divSpin`, `jalrSpin`, `sdLdSpin`, degenerate) discharge the premises this
    theorem SHARES with `stepSound_of_programDecodes` — `ziskTrace`, `ziskStep`,
    `inputsAgree`, `bootSeed`, `hAvoidKnownBugs` — but they satisfy `ProgramDecode`
    directly and so provide no evidence for those two. -/
theorem root_soundness
    (numInstructions rawLength : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (start : Fin rawLength → Fin ziskTrace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (programBinding : RawProgramBinding.ProgramRowsBinding
      ziskTrace start addr rawProgram)
    (rawProgramDecodes : ∀ i : Fin numInstructions,
      RawProgramDecode ziskTrace i (ziskStep i) start addr rawProgram)
    (inputsAgree : ∀ i : Fin numInstructions,
      InputsAgree ziskTrace sailTrace i (ziskStep i))
    (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i
          (programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
            start addr rawProgram programBinding (rawProgramDecodes i))) :=
  stepSound_of_programDecodes numInstructions ziskTrace sailTrace ziskStep
    (fun i => programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
      start addr rawProgram programBinding (rawProgramDecodes i))
    inputsAgree bootSeed hAvoidKnownBugs

end ZiskFv.Compliance
