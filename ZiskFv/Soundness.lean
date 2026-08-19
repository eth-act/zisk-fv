import ZiskFv.Compliance.TraceLevelExport
import ZiskFv.Compliance.TraceLevelExport.ChainedSailTrace
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode
import ZiskFv.Compliance.TraceLevelExport.RawProgramDecode
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import ZiskFv.Compliance.TraceLevelExport.RegisterCoverageBridge

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
    fact that ZisK's inputs equal the Sail model's register / memory state.
    `hAvoidKnownBugs` excludes the enumerated forge defects.

    `pcChain` and `rowsAligned` carry the **PC arm**.  The PC half of `inputsAgree`
    used to be a per-row assumption: all 63 `Inputs_<op>` structures carried an
    `h_pc_bridge` field asserting that the Main `pc` column at that row equals the
    Sail PC.  Those are gone.  `inputsAgree` now takes `InputsAgreeCore`
    (`Inputs_<op>` minus that field), and per-row PC agreement is *derived* by the
    strong induction in `stepSound_of_programDecodes` below:

      * `pcChain.boot` — the Sail PC agrees with the Main `pc` column at step `0`.
        This is the ONLY premise here relating a committed ZisK column to a Sail
        register.
      * `pcChain.retire` — the Sail state at `j + 1` takes its `PC` from what step
        `j` retired into `nextPC`.  Mentions no `mainOfTable`, `nextPcMux` or `pc`
        column: it relates two Sail states through Sail's own step function.
      * `rowsAligned` — at every step with a successor, the step's execution-bus
        producer entry is its own Main row's successor `pc`.  Mentions no Sail
        state.  Only a two-row unaligned JALR lowering can violate it; see
        `ZISK-MODEL-GAP-JALR-EXPANSION-STEP-ROW-INDEX` in `trust/defects.md`.

    Row `0` is `boot`; every later row comes from the PREVIOUS row's own `StepSound`
    via `pcBridge_succ_of_stepSound`, which reads the retired `nextPC` off the
    channel effect (`nextPC_of_busEffect_ok`) and identifies it with `pc (j + 1)`
    using `rowsAligned`.

    **Be precise about the claim.**  `sailRetireChain_of_inputsAgree` proves the
    converse — the old per-row bundle plus `rowsAligned` yields `retire` — so over an
    `AcceptedZiskTrace` the two premise sets are inter-derivable.  This is a
    *restructuring*, NOT a reduction in logical strength, and it is the same bargain
    `BootSegmentMemorySeed` struck for memory.  What changes: the cross-machine
    content collapses to `boot` alone, the other two premises are each one-sided, and
    `rowsAligned` — which the old `succ` silently did without — is now visible.

    `retire` is irreducible at *this* layer because `sailTrace` is an arbitrary
    `Fin n → SailState` (`Compliance/SailTrace.lean`) with no chaining, so *something*
    must say the Sail states form an execution.  It is **not** irreducible at the root:
    `root_soundness` below takes an initial state instead of a trace, generates the
    trace with `chainedSailTrace`, and obtains `retire` from
    `chainedSailTrace_retireChain` — a theorem, not a premise (#343).  This layer keeps
    the trace parametric because the five multi-step accepted-trace witnesses target it
    directly with hand-built traces.

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
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgreeCore ziskTrace sailTrace i (ziskStep i))
    (pcChain : SegmentPcChain ziskTrace sailTrace ziskStep)
    (rowsAligned : StepRowsAligned ziskTrace ziskStep
      (fun i => rowDecode_of_programDecode ziskTrace i (programDecodes i)))
    (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i (programDecodes i)) := by
  -- Per-row PC agreement, by strong induction on the step index. Row `0` is `pcChain.boot`; each
  -- later row comes from the previous row's own `StepSound` via `pcBridge_succ_of_stepSound`. This
  -- is the #330 Phase 7 restructure: the per-`i` map became an induction so that `succ` could stop
  -- being a premise.
  have key : ∀ (k : ℕ) (hk : k < numInstructions),
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable).pc k).val
        = ((sailTrace ⟨k, hk⟩).regs.get? Register.PC).elim 0 BitVec.toNat := by
    intro k
    induction k with
    | zero => intro hk; exact pcChain.boot hk
    | succ j ih =>
        intro hk
        have hj : j < numInstructions := Nat.lt_of_succ_lt hk
        exact pcBridge_succ_of_stepSound pcChain.toSailRetireChain rowsAligned j hk
          (stepSound_of_evidence ziskTrace sailTrace ⟨j, hj⟩ (ziskStep ⟨j, hj⟩)
            (rowDecode_of_programDecode ziskTrace ⟨j, hj⟩ (programDecodes ⟨j, hj⟩))
            (inputsAgree_of_pcBridge ⟨j, hj⟩ (ih hj) (ziskStep ⟨j, hj⟩) (inputsAgree ⟨j, hj⟩))
            (memEvidence_of_bootSeed bootSeed ⟨j, hj⟩) (hAvoidKnownBugs ⟨j, hj⟩))
  intro i
  exact stepSound_of_evidence ziskTrace sailTrace i (ziskStep i)
    (rowDecode_of_programDecode ziskTrace i (programDecodes i))
    (inputsAgree_of_pcBridge i (key i.val i.isLt) (ziskStep i) (inputsAgree i))
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

    THE SAIL SIDE IS GENERATED, NOT SUPPLIED (#343). This theorem does not take a
    `SailTrace`. It takes the initial Sail state `init` and builds the trace itself
    with `chainedSailTrace`, which runs `execute_instruction` at each step and then
    performs Sail's retire (copy `nextPC` into `PC`). Three consequences, and the
    third is a cost:

      * The `retire` OBLIGATION left the statement; the binder did not. `pcChain :
        SegmentPcChain …` was *replaced* by `pcBoot`, which carries only the `boot`
        equation — the binder count is unchanged (16, per
        `trust/generated/baseline-strong-export-binders.txt`). What is gone is
        `SegmentPcChain`'s `retire` field, supplied below by the hypothesis-free
        theorem `chainedSailTrace_retireChain`. `sailRetireChain_of_inputsAgree`'s
        converse no longer applies, because there is nothing left to derive.
      * A caller can no longer choose the Sail states. Supplying `init` and then
        `inputsAgree` at `chainedSailTrace ziskStep init` means agreeing with the
        states Sail actually reaches, which is the guardrail #343 asks for: the trace
        has to be *harder* to inhabit, not merely repackaged. Note that no checked-in
        witness yet pays that cost — both instantiations run at `numInstructions ≤ 1`,
        where `chainedSailStates … 0` is `init` by `rfl`, so neither reaches a chain
        step. See `trust/trusted-base.md`.
      * This statement is an INSTANCE of the old one, at
        `sailTrace := chainedSailTrace ziskStep init`. So the edit both drops an
        obligation and specializes the conclusion: a caller who wants `StepSound` at a
        trace of their own choosing can no longer get it here. That is the intended
        direction, but it is a specialization, not a free strengthening.

    `stepSound_of_programDecodes` keeps taking a `SailTrace` and a full
    `SegmentPcChain`, because the five multi-step accepted-trace witnesses target it
    directly with hand-built traces.

    NON-VACUITY (#320): witnessed. `addFaithfulPaddedRawRootSoundness`
    (`Compliance/AddFaithfulPaddedRootSoundness.lean`) instantiates this theorem on a
    one-instruction execution with the proved `addFaithfulProgramRowsBinding` and real
    `addFaithfulRawProgramDecodes`, so the conclusion it obtains is not vacuous.
    `memoryRawRootSoundness` supplies a second real `ProgramRowsBinding`, on an
    empty execution. The other instantiations (`addSpin`, `addAddiSpin`, `divSpin`,
    `jalrSpin`, `sdLdSpin`) discharge the premises this theorem SHARES with
    `stepSound_of_programDecodes` — `ziskTrace`, `ziskStep`, `inputsAgree`, `rowsAligned`,
    `bootSeed`, `hAvoidKnownBugs` — but satisfy `ProgramDecode` directly, so they
    provide no evidence for `programBinding` / `rawProgramDecodes`. -/
theorem root_soundness
    (numInstructions rawLength : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (start : Fin rawLength → Fin ziskTrace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (programBinding : RawProgramBinding.ProgramRowsBinding
      ziskTrace start addr rawProgram)
    (rawProgramDecodes : ∀ i : Fin numInstructions,
      RawProgramDecode ziskTrace i (ziskStep i) start addr rawProgram)
    (inputsAgree : ∀ i : Fin numInstructions,
      InputsAgreeCore ziskTrace (chainedSailTrace ziskStep init) i (ziskStep i))
    (pcBoot : ∀ (_ : 0 < numInstructions),
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable).pc 0).val
        = (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (rowsAligned : StepRowsAligned ziskTrace ziskStep
      (fun i => rowDecode_of_programDecode ziskTrace i
        (programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
          start addr rawProgram programBinding (rawProgramDecodes i))))
    (bootSeed : BootSegmentMemorySeed ziskTrace (chainedSailTrace ziskStep init) ziskStep)
    (regBoot : ∀ k : Fin 32, k ≠ 0 →
      init.regs.get? (reg_of_fin k)
        = some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace (chainedSailTrace ziskStep init) i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i
          (programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
            start addr rawProgram programBinding (rawProgramDecodes i))) := by
  let rowDecodes := fun i => rowDecode_of_programDecode ziskTrace i
    (programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
      start addr rawProgram programBinding (rawProgramDecodes i))
  have regKey : ∀ (k : ℕ) (hk : k < numInstructions),
      RegAgree ziskStep rowDecodes init k := by
    intro k
    induction k with
    | zero => intro _; exact regAgree_zero ziskStep rowDecodes init regBoot
    | succ j ih =>
        intro hk
        have hj : j < numInstructions := Nat.lt_of_succ_lt hk
        exact regAgree_succ ziskStep rowDecodes init j hj
          (stepSound_of_programDecodes numInstructions ziskTrace
            (chainedSailTrace ziskStep init) ziskStep
            (fun i => programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
              start addr rawProgram programBinding (rawProgramDecodes i))
            inputsAgree
            { toSailRetireChain := chainedSailTrace_retireChain ziskStep init
              boot := pcBoot }
            rowsAligned bootSeed hAvoidKnownBugs ⟨j, hj⟩)
          (ih hj)
  intro i
  exact stepSound_of_programDecodes numInstructions ziskTrace
    (chainedSailTrace ziskStep init) ziskStep
    (fun i => programDecode_of_rawProgramDecode ziskTrace i (ziskStep i)
      start addr rawProgram programBinding (rawProgramDecodes i))
    inputsAgree
    { toSailRetireChain := chainedSailTrace_retireChain ziskStep init
      boot := pcBoot }
    rowsAligned bootSeed hAvoidKnownBugs i

end ZiskFv.Compliance
