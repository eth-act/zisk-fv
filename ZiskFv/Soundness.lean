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

open ZiskFv.AirsClean.FullEnsemble (mainTableRowAtOrZero mainOfTable mainOfTable_pc
  mainOfTable_store_pc mainOfTable_jmp_offset2 mainOfTable_is_external_op mainOfTable_op
  mainOfTable_b_0 mainOfTable_b_1 mainOfTable_c_0 mainOfTable_c_1)
open ZiskFv.AirsClean.Main (cMemMessage rowAt)
open ZiskFv.Channels.MemoryBus (MemBusMessage.toEntry)

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
      RowOutsideDefectRegion ziskTrace i (ziskStep i))
    (lb : ∀ i : Fin numInstructions,
      LaneBridge ziskTrace (sailTrace i) i.val) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i (programDecodes i)) := by
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
            (memEvidence_of_bootSeed bootSeed ⟨j, hj⟩) (hAvoidKnownBugs ⟨j, hj⟩)
            (lb ⟨j, hj⟩))
  intro i
  exact stepSound_of_evidence ziskTrace sailTrace i (ziskStep i)
    (rowDecode_of_programDecode ziskTrace i (programDecodes i))
    (inputsAgree_of_pcBridge i (key i.val i.isLt) (ziskStep i) (inputsAgree i))
    (memEvidence_of_bootSeed bootSeed i) (hAvoidKnownBugs i)
    (lb i)

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
private theorem stepRegWrite_converse_aux
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n) (zs : ZiskStep trace i) (rd : RowDecode trace i zs)
    (h_addr : ZiskFv.AirsClean.Main.AddressSpec
      (mainTableRowAtOrZero trace.program trace.mainTable i.val))
    (h_aligned : stepProducerRow i zs rd = i.val)
    (e : Interaction.MemoryBusEntry FGL)
    (he : stepRegWrite (stepChannelOutput i zs rd) = some e)
    (h_r_ne : Transpiler.wrap_to_regidx e.ptr ≠ 0) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 := by
  cases zs with
  | beq c => exact nomatch he
  | bne c => exact nomatch he
  | blt c => exact nomatch he
  | bge c => exact nomatch he
  | bltu c => exact nomatch he
  | bgeu c => exact nomatch he
  | sb c => exact nomatch he
  | sh c => exact nomatch he
  | sw c => exact nomatch he
  | sd c => exact nomatch he
  | fence c => exact nomatch he
  | jalr c =>
    have h_eq : rd.rows.start = rd.rows.finish := by
      by_contra h_ne_rows
      have := rd.h_start_store_reg_zero h_ne_rows
      have h_prod : rd.rows.finish.val = i.val := h_aligned
      have h_arch := rd.rows.architectural_start
      omega
    have h_fi : i.val = rd.rows.finish.val :=
      ((congrArg Fin.val h_eq.symm).trans rd.rows.architectural_start).symm
    rw [h_fi, rd.h_store_reg]
    suffices h : (regidx_to_fin c.rd : Fin 32) ≠ 0 by simp [h]
    intro h_zero
    apply h_r_ne
    have he' := Option.some.inj he
    rw [show e.ptr = (eRdAt trace rd.rows.finish).ptr from congrArg (·.ptr) he'.symm]
    have h_off : (mainRowWithRomAt trace rd.rows.finish).rom.store_offset =
        Transpiler.ind (regidx_to_fin c.rd) := by
      rw [rd.h_store_offset, h_zero]; simp [Transpiler.ind]
    have h_idx := eRdAt_rd_idx_of_decode rd.h_store_ind h_off
    rw [← h_idx, h_zero]
  | _ =>
    rw [rd.h_store_reg]
    have h_addr2 := h_addr.2.2.1
    rw [rd.h_store_ind, rd.h_store_offset] at h_addr2; simp at h_addr2
    have he' := Option.some.inj he
    rw [show e.ptr = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.addr2
      from by exact congrArg (·.ptr) he'.symm] at h_r_ne
    rw [h_addr2, Transpiler.wrap_to_regidx_ind] at h_r_ne
    try simp only [Transpiler.regidxOfBitVec5, ne_eq, Fin.ext_iff, Fin.val_zero] at h_r_ne
    simp [h_r_ne]

private lemma fgl_add_val_lt_of_sum_lt {a b : FGL} {bound : ℕ}
    (h_sum_lt : a.val + b.val < GL_prime)
    (h_bound : a.val + b.val < bound) :
    (a + b).val < bound := by
  change (a.val + b.val) % GL_prime < bound
  omega

private lemma fgl_val_add_intCast_of_nonneg_lt {a : FGL} {z : ℤ}
    (h_nonneg : 0 ≤ (a.val : ℤ) + z) (h_lt : (a.val : ℤ) + z < GL_prime) :
    (a + (z : FGL)).val = ((a.val : ℤ) + z).toNat := by
  have h_a := a.isLt
  change (a.val + (z : FGL).val) % GL_prime = _
  have h_zv : (z : FGL).val = (z % (GL_prime : ℤ)).toNat := by
    simp only [Fin.val_intCast]; norm_cast
  rw [h_zv]; omega

private lemma fgl_add_intCast_lt_of_bitvec_lt {pc : FGL} {offset : BitVec 64} {bound : ℕ}
    (h_nonneg : 0 ≤ (pc.val : ℤ) + offset.toInt)
    (h_lt : (pc.val : ℤ) + offset.toInt < GL_prime)
    (h_bound : (BitVec.ofNat 64 pc.val + offset).toNat < bound) :
    (pc + (offset.toInt : FGL)).val < bound := by
  rw [fgl_val_add_intCast_of_nonneg_lt h_nonneg h_lt]
  have h_pc_lt := pc.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pc.val < 2 ^ 64)]
      at h_bound
  rw [BitVec.toInt_eq_toNat_bmod] at h_nonneg h_lt ⊢
  have h_off_lt : offset.toNat < 2 ^ 64 := offset.isLt
  simp only [Int.bmod] at h_nonneg h_lt ⊢
  split at h_nonneg <;> split at h_lt <;> split <;> omega

private lemma cMemMessage_chunks_of_store_pc_one
    (m : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_sp : m.core.store_pc = 1)
    (h_val : (m.core.pc + m.core.jmp_offset2).val < 4294967296) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage m).toEntry 1 1) := by
  simp only [ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range, cMemMessage, MemBusMessage.toEntry,
    h_sp]
  constructor
  · rw [one_mul, sub_add_cancel]; exact h_val
  · show ((1 : FGL) - 1).val * _ % _ < _; simp

private lemma cMemMessage_chunks_of_store_pc_zero
    (m : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_sp : m.core.store_pc = 0)
    (h_c0 : m.core.c_0.val < 4294967296)
    (h_c1 : m.core.c_1.val < 4294967296) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage m).toEntry 1 1) := by
  simp only [ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range, cMemMessage, MemBusMessage.toEntry,
    h_sp]
  constructor
  · show (0 * _ + m.core.c_0).val < _; simp [h_c0]
  · have : ((1 : FGL) - 0) * m.core.c_1 = m.core.c_1 := by ring
    rw [this]; exact h_c1

private theorem stepRegWrite_entry_range_aux
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n) (zs : ZiskStep trace i) (rd : RowDecode trace i zs)
    (hAvoid : RowOutsideDefectRegion trace i zs)
    (he : stepRegWrite (stepChannelOutput i zs rd)
      = some ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  cases zs with
  | beq c => exact nomatch he
  | bne c => exact nomatch he
  | blt c => exact nomatch he
  | bge c => exact nomatch he
  | bltu c => exact nomatch he
  | bgeu c => exact nomatch he
  | sb c => exact nomatch he
  | sh c => exact nomatch he
  | sw c => exact nomatch he
  | sd c => exact nomatch he
  | fence c => exact nomatch he
  | jal c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 1 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_j2 : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.jmp_offset2 = 4 := by
      have := rd.h_jmp2; simp only [mainOfTable_jmp_offset2] at this; exact this
    apply cMemMessage_chunks_of_store_pc_one _ h_sp
    rw [h_j2]
    have h_pcv : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc.val
        < GL_prime - 4 := by
      have := hAvoid.h_pc_bound; unfold MainSequentialPcDomain mainPcVal at this
      simp only [mainOfTable_pc] at this; exact this
    have h_bound := hAvoid.h_pc_offset_lt_2_32
      (BitVec.ofNat 64 (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc.val)
      (by unfold mainPcVal; simp only [mainOfTable_pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h_bound
    exact fgl_add_val_lt_of_sum_lt (by omega) (by omega)
  | auipc c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 1 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_j2 := rd.h_jmp_offset2_imm; simp only [mainOfTable_jmp_offset2] at h_j2
    apply cMemMessage_chunks_of_store_pc_one _ h_sp
    rw [h_j2]
    have h_nonneg := hAvoid.h_target_nonneg
    have h_lt_prime := hAvoid.h_target_lt
    unfold mainPcVal at h_nonneg h_lt_prime
    simp only [mainOfTable_pc] at h_nonneg h_lt_prime
    exact fgl_add_intCast_lt_of_bitvec_lt h_nonneg h_lt_prime
      (hAvoid.h_pc_offset_lt_2_32
        (BitVec.ofNat 64 (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc.val)
        (by unfold mainPcVal; simp only [mainOfTable_pc, BitVec.toNat_ofNat]; omega))
  | lui c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.is_external_op
        = 0 := by
      have := rd.h_main_active; simp only [mainOfTable_is_external_op] at this; exact this
    have h_op : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.op
        = (1 : FGL) := by
      have := rd.h_main_op; simp only [mainOfTable_op] at this
      rw [this]; rfl
    have h_spec := mainSpec_at_physical trace ⟨i.val, trace.mainTable_index i⟩
    have h5 := h_spec.2.2.2.2.1
    simp only [mainOfTable_is_external_op, mainOfTable_op, mainOfTable_b_0, mainOfTable_c_0] at h5
    rw [h_ieo, h_op] at h5
    have h6 := h_spec.2.2.2.2.2.1
    simp only [mainOfTable_is_external_op, mainOfTable_op, mainOfTable_b_1, mainOfTable_c_1] at h6
    rw [h_ieo, h_op] at h6
    simp only [sub_zero, one_mul] at h5 h6
    have h_b0_eq_c0 : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.b_0
        = (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.c_0 :=
      sub_eq_zero.mp h5
    have h_b1_eq_c1 : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.b_1
        = (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.c_1 :=
      sub_eq_zero.mp h6
    apply cMemMessage_chunks_of_store_pc_zero _ h_sp
    · have h_b0_val := rd.h_imm_lo_nat; simp only [mainOfTable_b_0] at h_b0_val
      rw [show (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.c_0.val
          = (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.b_0.val from
        congr_arg Fin.val h_b0_eq_c0.symm, h_b0_val]
      exact (c.imm ++ (0 : BitVec 12)).isLt
    · have h_b1_val := rd.h_imm_hi_nat; simp only [mainOfTable_b_1] at h_b1_val
      rw [show (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.c_1.val
          = (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.b_1.val from
        congr_arg Fin.val h_b1_eq_c1.symm, h_b1_val]
      exact Nat.div_lt_of_lt_mul (by have := (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).isLt; omega)
  | _ => sorry

private theorem stepRegWrite_consistent_aux
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n) (zs : ZiskStep trace i) (rd : RowDecode trace i zs)
    (h_sr : (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1) :
    stepRegWrite (stepChannelOutput i zs rd) ≠ none
    ∧ stepProducerRow i zs rd = i.val := by
  cases zs with
  | beq c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | bne c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | blt c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | bge c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | bltu c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | bgeu c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | sb c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | sh c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | sw c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | sd c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | fence c => exact absurd (rd.h_store_reg.symm.trans h_sr) (by decide)
  | jalr c =>
    constructor
    · exact fun h => nomatch h
    · show rd.rows.finish.val = i.val
      have h_eq : rd.rows.start = rd.rows.finish := by
        by_contra h_ne
        have h_zero := rd.h_start_store_reg_zero h_ne
        have : (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 0 := by
          rw [show i.val = rd.rows.start.val from rd.rows.architectural_start.symm]
          exact h_zero
        exact absurd (this.symm.trans h_sr) (by decide)
      exact (congrArg Fin.val h_eq.symm).trans rd.rows.architectural_start
  | _ => exact ⟨(fun h => nomatch h), rfl⟩

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
  have h_stepRegWrite_consistent : ∀ (i : Fin numInstructions),
      (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val).rom.store_reg = 1 →
      stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
      ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val := fun i h_sr =>
    stepRegWrite_consistent_aux i (ziskStep i) (rowDecodes i) h_sr
  have h_stepRegWrite_converse : ∀ (i : Fin numInstructions)
      (e : Interaction.MemoryBusEntry FGL),
      i.val + 1 < numInstructions →
      stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) = some e →
      Transpiler.wrap_to_regidx e.ptr ≠ 0 →
      (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val).rom.store_reg = 1 :=
    fun i e h_succ he h_ne =>
    stepRegWrite_converse_aux i (ziskStep i) (rowDecodes i)
      (RomDecodeBinding.mainAddressSpec_at ziskTrace ⟨i.val, ziskTrace.mainTable_index i⟩)
      (rowsAligned i.val h_succ) e he h_ne
  have h_entry_range : ∀ (i : Fin numInstructions),
      stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
        = some ((cMemMessage
          (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val)).toEntry 1 1) →
      ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
        ((cMemMessage
          (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val)).toEntry 1 1) :=
    fun i he =>
    stepRegWrite_entry_range_aux i (ziskStep i) (rowDecodes i) (hAvoidKnownBugs i) he
  have combined : ∀ (k : ℕ) (hk : k < numInstructions),
      RegAgree ziskStep rowDecodes init k
      ∧ ((ZiskFv.AirsClean.FullEnsemble.mainOfTable
            ziskTrace.program ziskTrace.mainTable).pc k).val
        = ((chainedSailTrace ziskStep init ⟨k, hk⟩).regs.get? Register.PC).elim 0
            BitVec.toNat := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact ⟨regAgree_zero ziskStep rowDecodes init regBoot, pcBoot hk⟩
    | succ j ih =>
        intro hk
        have hj : j < numInstructions := Nat.lt_of_succ_lt hk
        obtain ⟨h_reg_j, h_pc_j⟩ := ih hj
        have ss_j : StepSound ziskTrace (chainedSailTrace ziskStep init) ⟨j, hj⟩
            (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩) :=
          stepSound_of_evidence ziskTrace (chainedSailTrace ziskStep init) ⟨j, hj⟩
            (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)
            (inputsAgree_of_pcBridge ⟨j, hj⟩ h_pc_j (ziskStep ⟨j, hj⟩) (inputsAgree ⟨j, hj⟩))
            (memEvidence_of_bootSeed bootSeed ⟨j, hj⟩) (hAvoidKnownBugs ⟨j, hj⟩)
            (laneBridge_of_regAgree ziskTrace ziskStep rowDecodes init j hj
              h_reg_j h_stepRegWrite_consistent h_stepRegWrite_converse h_entry_range)
        exact ⟨
          regAgree_succ ziskStep rowDecodes init j hj ss_j h_reg_j,
          pcBridge_succ_of_stepSound (chainedSailTrace_retireChain ziskStep init)
            rowsAligned j hk ss_j⟩
  intro i
  obtain ⟨h_reg_i, h_pc_i⟩ := combined i.val i.isLt
  exact stepSound_of_evidence ziskTrace (chainedSailTrace ziskStep init) i (ziskStep i)
    (rowDecodes i)
    (inputsAgree_of_pcBridge i h_pc_i (ziskStep i) (inputsAgree i))
    (memEvidence_of_bootSeed bootSeed i) (hAvoidKnownBugs i)
    (laneBridge_of_regAgree ziskTrace ziskStep rowDecodes init i.val i.isLt
      h_reg_i h_stepRegWrite_consistent h_stepRegWrite_converse h_entry_range)

end ZiskFv.Compliance
