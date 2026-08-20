import ZiskFv.Compliance.TraceLevelExport
import ZiskFv.Compliance.TraceLevelExport.ChainedSailTrace
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode
import ZiskFv.Compliance.TraceLevelExport.RawProgramDecode
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import ZiskFv.Compliance.TraceLevelExport.RegisterCoverageBridge
import ZiskFv.AirsClean.ArithTableProjections

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
  mainOfTable_store_pc mainOfTable_jmp_offset2 mainOfTable_jmp_offset1 mainOfTable_is_external_op
  mainOfTable_op mainOfTable_b_0 mainOfTable_b_1 mainOfTable_c_0 mainOfTable_c_1
  mainOfTable_set_pc mainOfTable_flag mainOfTable_segment_l1)
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

private lemma matches_entry_c_eq
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {i : ℕ} {msg : ZiskFv.Channels.OperationBus.OpBusMessage FGL}
    (h : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m i)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry msg 1)) :
    m.c_0 i = msg.c_lo ∧ m.c_1 i = msg.c_hi := by
  simp only [ZiskFv.Airs.OperationBus.matches_entry,
    ZiskFv.Airs.OperationBus.opBus_row_Main,
    ZiskFv.Channels.OperationBus.OpBusMessage.toEntry] at h
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

private lemma fgl_two_chunks_val_lt (a b : FGL)
    (ha : a.val < 65536) (hb : b.val < 65536) :
    (a * 65536 + b : FGL).val < 4294967296 := by
  have hav : (65536 : FGL).val = 65536 := by native_decide
  have h1 : a.val * (65536 : FGL).val % GL_prime = a.val * 65536 :=
    Nat.mod_eq_of_lt (by rw [hav]; omega)
  have h2 : (a.val * 65536 + b.val) % GL_prime = a.val * 65536 + b.val :=
    Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_mul, h1, h2]
  omega

private lemma fgl_two_chunks_val_lt_comm (a b : FGL)
    (ha : a.val < 65536) (hb : b.val < 65536) :
    (b + a * 65536 : FGL).val < 4294967296 := by
  rw [add_comm]; exact fgl_two_chunks_val_lt a b ha hb

private lemma fgl_two_bytes_val_lt (a b : FGL)
    (ha : a.val < 256) (hb : b.val < 256) :
    (a + 256 * b : FGL).val < 65536 := by
  have h256v : (256 : FGL).val = 256 := by native_decide
  have h1 : (256 : FGL).val * b.val % GL_prime = 256 * b.val :=
    Nat.mod_eq_of_lt (by rw [h256v]; omega)
  have h2 : (a.val + 256 * b.val) % GL_prime = a.val + 256 * b.val :=
    Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_mul, h256v, h1, h2]
  omega

private lemma fgl_four_bytes_val_lt (a b c d : FGL)
    (ha : a.val < 256) (hb : b.val < 256) (hc : c.val < 256) (hd : d.val < 256) :
    (a + 256 * b + 65536 * c + 16777216 * d : FGL).val < 4294967296 := by
  have h_eq : (a + 256 * b + 65536 * c + 16777216 * d : FGL)
      = (c + 256 * d) * 65536 + (a + 256 * b) := by ring
  rw [h_eq]
  exact fgl_two_chunks_val_lt _ _ (fgl_two_bytes_val_lt c d hc hd)
    (fgl_two_bytes_val_lt a b ha hb)

private lemma fgl_four_bytes_carry_val_lt (a b c d carry : FGL)
    (ha : a.val < 256) (hb : b.val < 256) (hc : c.val < 256) (hd : d.val < 256)
    (hcarry : carry = 0) :
    (a + 256 * b + 65536 * c + 16777216 * d + carry : FGL).val < 4294967296 := by
  rw [hcarry, add_zero]
  exact fgl_four_bytes_val_lt a b c d ha hb hc hd

private lemma binary_static_opBus_c_hi_lt
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row) :
    (ZiskFv.AirsClean.Binary.opBusMessage row).c_hi.val < 4294967296 := by
  show (ZiskFv.AirsClean.Binary.cHiValue row).val < _
  unfold ZiskFv.AirsClean.Binary.cHiValue
  have hr4 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.1
  have hr5 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.2.1
  have hr6 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.2.2.1
  have hr7 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.2.2.2
  simp only [ZiskFv.Airs.Tables.BinaryTable.range_conditions,
    ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
    ZiskFv.AirsClean.Binary.lookupMessage4Row,
    ZiskFv.AirsClean.Binary.lookupMessage5Row,
    ZiskFv.AirsClean.Binary.lookupMessage6Row,
    ZiskFv.AirsClean.Binary.lookupMessage7Row] at hr4 hr5 hr6 hr7
  exact fgl_four_bytes_val_lt _ _ _ _ hr4.2.2.1 hr5.2.2.1 hr6.2.2.1 hr7.2.2.1

private lemma binary_static_opBus_c_lo_lt
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_carry : row.chain.carry_7 = 0) :
    (ZiskFv.AirsClean.Binary.opBusMessage row).c_lo.val < 4294967296 := by
  show (ZiskFv.AirsClean.Binary.cLoValue row).val < _
  unfold ZiskFv.AirsClean.Binary.cLoValue
  have hr0 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.1
  have hr1 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.1
  have hr2 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.1
  have hr3 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.1
  simp only [ZiskFv.Airs.Tables.BinaryTable.range_conditions,
    ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
    ZiskFv.AirsClean.Binary.lookupMessage0Row,
    ZiskFv.AirsClean.Binary.lookupMessage1Row,
    ZiskFv.AirsClean.Binary.lookupMessage2Row,
    ZiskFv.AirsClean.Binary.lookupMessage3Row] at hr0 hr1 hr2 hr3
  exact fgl_four_bytes_carry_val_lt _ _ _ _ _ hr0.2.2.1 hr1.2.2.1 hr2.2.2.1 hr3.2.2.1 h_carry

private lemma mode_pins_of_emit_op_eq_16_of_static_spec
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (16 : FGL)) :
    row.mode.mode32 = 0
      ∧ row.chain.b_op.val = 16
      ∧ row.chain.b_op_or_sext.val = 16 := by
  have h_bop_ne : row.chain.b_op.val ≠ 0 := by
    have := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_zero h_static.1
    simpa [ZiskFv.AirsClean.Binary.lookupMessage0Row] using this
  have h_mode_bool : row.mode.mode32 * (1 - row.mode.mode32) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_mode32,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.1
  have h16v : (16 : FGL).val = 16 := by native_decide
  rcases (mul_eq_zero.mp h_mode_bool) with h_mode_zero | h_mode_sub
  · have h_bop_val : row.chain.b_op.val = 16 := by
      have hv := congrArg Fin.val h_emit
      simp only [Fin.val_add, Fin.val_mul] at hv
      rw [h_mode_zero] at hv
      simp only [Fin.val_zero, Nat.mul_zero,
        Nat.mod_eq_of_lt (by omega : 0 < GL_prime),
        Nat.add_zero,
        Nat.mod_eq_of_lt (show row.chain.b_op.val < GL_prime from row.chain.b_op.isLt),
        h16v] at hv
      exact hv
    have h_bop_or :=
      ZiskFv.EquivCore.Bridge.Binary.b_op_or_sext_val_eq_of_mode32_zero
        (ZiskFv.AirsClean.Binary.validOfRow row) 0 16
        h_core (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_mode_zero)
        (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_val)
    exact ⟨h_mode_zero, h_bop_val,
      by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_or⟩
  · exfalso
    have h_mode_one : row.mode.mode32 = 1 := (sub_eq_zero.mp h_mode_sub).symm
    have h_bad : row.chain.b_op.val = 0 := by
      have hv := congrArg Fin.val h_emit
      simp only [Fin.val_add, Fin.val_mul] at hv
      rw [h_mode_one] at hv
      simp only [Fin.val_one, Nat.mul_one, h16v,
        Nat.mod_eq_of_lt (by omega : 16 < GL_prime)] at hv
      have hsmall : row.chain.b_op.val + 16 < GL_prime := by omega
      rw [Nat.mod_eq_of_lt hsmall] at hv
      omega
    exact h_bop_ne h_bad

private lemma binary_static_add_sub_entry_range
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_wf : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_op_lt : op_val < 16)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL))
    (h_op_add_or_sub :
      op_val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD ∨
      op_val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB) :
    row.chain.carry_7 = 0 := by
  have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
    row h_spec_facts op_val h_op_lt h_core h_emit
  have h_out := ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
    row h_wf op_val h_core h_pins.1 h_pins.2.1
  have h_carry_bool : (ZiskFv.AirsClean.Binary.validOfRow row).carry_7 0 *
      (1 - (ZiskFv.AirsClean.Binary.validOfRow row).carry_7 0) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_carry_7, ZiskFv.AirsClean.Binary.validOfRow]
      using h_core.2.1
  rcases h_op_add_or_sub with h | h
  · have := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_ADD_of_static_chain
      _ 0 (h ▸ h_out) h_core h_carry_bool
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using this
  · have := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_SUB_of_static_chain
      _ 0 (h ▸ h_out) h_core h_carry_bool
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using this

private lemma binary_static_compare_c_lo_lt
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_wf : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_op_lt : op_val < 16)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL))
    (h_c_zero_of_chain : ∀ {a b c cin flags pos : FGL},
      ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val a b c cin flags pos → c = 0) :
    (ZiskFv.AirsClean.Binary.opBusMessage row).c_lo.val < 4294967296 := by
  have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
    row h_spec_facts op_val h_op_lt h_core h_emit
  have h_out := ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
    row h_wf op_val h_core h_pins.1 h_pins.2.1
  have hc0 : row.cBytes.free_in_c_0 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_0
  have hc1 : row.cBytes.free_in_c_1 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_1
  have hc2 : row.cBytes.free_in_c_2 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_2
  have hc3 : row.cBytes.free_in_c_3 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_3
  have h_carry_bool : row.chain.carry_7 * (1 - row.chain.carry_7) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_carry_7,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.2.1
  show (ZiskFv.AirsClean.Binary.cLoValue row).val < _
  unfold ZiskFv.AirsClean.Binary.cLoValue
  rw [hc0, hc1, hc2, hc3]
  rcases mul_eq_zero.mp h_carry_bool with h | h
  · rw [h]; norm_num
  · have h1 := (sub_eq_zero.mp h).symm; rw [h1]; norm_num

private lemma binary_static_w_mode_carry_7_zero
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_wf : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL))
    (h_op_w : op_val = 26 ∨ op_val = 27) :
    row.chain.carry_7 = 0 := by
  have h_mode_bool : row.mode.mode32 * (1 - row.mode.mode32) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_mode32,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.1
  have h_mode_one : row.mode.mode32 = 1 := by
    rcases mul_eq_zero.mp h_mode_bool with h | h
    · exfalso
      have h_ne := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_W_add_sub h_spec_facts.1
      simp only [ZiskFv.AirsClean.Binary.lookupMessage0Row] at h_ne
      have h_bop : row.chain.b_op = (op_val : FGL) := by
        have := h_emit; rw [h, mul_zero, add_zero] at this; exact this
      have h_bop_v := congrArg Fin.val h_bop
      simp only [Fin.val_natCast] at h_bop_v
      rcases h_op_w with rfl | rfl
      · exact h_ne.1 (by rw [show 26 % GL_prime = 26 from by omega] at h_bop_v; exact h_bop_v)
      · exact h_ne.2 (by rw [show 27 % GL_prime = 27 from by omega] at h_bop_v; exact h_bop_v)
    · exact (sub_eq_zero.mp h).symm
  have h_bop_val : row.chain.b_op.val = op_val - 16 := by
    have hv := congrArg Fin.val h_emit
    simp only [Fin.val_add, Fin.val_mul] at hv
    rw [h_mode_one] at hv
    have h16v : (16 : FGL).val = 16 := by native_decide
    simp only [Fin.val_one, Nat.mul_one, h16v,
      Nat.mod_eq_of_lt (by omega : 16 < GL_prime)] at hv
    have h_lt : row.chain.b_op.val < GL_prime := row.chain.b_op.isLt
    rcases h_op_w with rfl | rfl
    · simp only [Fin.val_natCast,
        Nat.mod_eq_of_lt (by omega : 26 < GL_prime)] at hv; omega
    · simp only [Fin.val_natCast,
        Nat.mod_eq_of_lt (by omega : 27 < GL_prime)] at hv; omega
  have h_bop_add_or_sub :
      row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD ∨
      row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB := by
    rcases h_op_w with rfl | rfl
    · left; rw [h_bop_val]; rfl
    · right; rw [h_bop_val]; rfl
  exact (ZiskFv.EquivCore.Bridge.Binary.w_mode_sext_choice_and_carry_7_zero_of_static_row
    row h_spec_facts h_wf h_core h_mode_one h_bop_add_or_sub).2

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

private lemma entry_range_of_provider_match
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {msg : ZiskFv.Channels.OperationBus.OpBusMessage FGL}
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry msg 1))
    (h_clo : msg.c_lo.val < 4294967296)
    (h_chi : msg.c_hi.val < 4294967296) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have ⟨hc0_eq, hc1_eq⟩ := matches_entry_c_eq h_match
  simp only [mainOfTable_c_0] at hc0_eq
  simp only [mainOfTable_c_1] at hc1_eq
  exact cMemMessage_chunks_of_store_pc_zero _ h_sp
    (hc0_eq ▸ h_clo) (hc1_eq ▸ h_chi)

private lemma binary_static_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (h_pr : providerRow ∈ providerTable.table)
    (h_component : providerTable.component =
      ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_spec : providerTable.Spec)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_carry :
      (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (providerTable.environment providerRow)).chain.carry_7 = 0) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have h_row_spec : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts
      (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (providerTable.environment providerRow)) := by
    have := h_spec providerRow h_pr
    rw [h_component, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at this
    exact this.2
  exact entry_range_of_provider_match i h_sp h_match
    (binary_static_opBus_c_lo_lt _ h_row_spec h_carry)
    (binary_static_opBus_c_hi_lt _ h_row_spec)

private lemma binaryAdd_opBus_c_lo_lt (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (h : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row) :
    (ZiskFv.AirsClean.BinaryAdd.opBusMessage row).c_lo.val < 4294967296 := by
  show (row.c_chunks_1 * 65536 + row.c_chunks_0 : FGL).val < _
  exact fgl_two_chunks_val_lt _ _ (by have := h.2.2.2.2.2.1; omega) (by have := h.2.2.2.2.1; omega)

private lemma binaryAdd_opBus_c_hi_lt (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (h : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row) :
    (ZiskFv.AirsClean.BinaryAdd.opBusMessage row).c_hi.val < 4294967296 := by
  show (row.c_chunks_3 * 65536 + row.c_chunks_2 : FGL).val < _
  exact fgl_two_chunks_val_lt _ _ (by have := h.2.2.2.2.2.2.2; omega) (by have := h.2.2.2.2.2.2.1; omega)

private lemma binaryAdd_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (h_pr : providerRow ∈ providerTable.table)
    (h_component : providerTable.component = ZiskFv.AirsClean.BinaryAdd.component)
    (h_spec : providerTable.Spec)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage
          (ZiskFv.AirsClean.BinaryAdd.component.rowInput
            (providerTable.environment providerRow))) 1)) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have h_facts : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts
      (ZiskFv.AirsClean.BinaryAdd.component.rowInput
        (providerTable.environment providerRow)) := by
    simpa [h_component, ZiskFv.AirsClean.BinaryAdd.component_spec] using
      h_spec providerRow h_pr
  exact entry_range_of_provider_match i h_sp h_match
    (binaryAdd_opBus_c_lo_lt _ h_facts)
    (binaryAdd_opBus_c_hi_lt _ h_facts)

private lemma arithMul_opBus_c_lo_lt
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec row)
    (h_div_block : ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec row) :
    (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage row).c_lo.val < 4294967296 := by
  have h_chunks := h_full.2.2.2.1
  have h_div_mode := h_div_block.1
  have h_mm_bool := h_div_mode.2.1
  have h_md_bool := h_div_mode.1
  have h_mm_md := h_div_mode.2.2.1
  show ((1 - row.flags.main_mul - row.flags.main_div) * (row.chunks.d_0 + row.chunks.d_1 * 65536)
    + row.flags.main_mul * (row.chunks.c_0 + row.chunks.c_1 * 65536)
    + row.flags.main_div * (row.chunks.a_0 + row.chunks.a_1 * 65536)).val < _
  rcases mul_eq_zero.mp h_mm_bool with hmm | hmm
  · rcases mul_eq_zero.mp h_md_bool with hmd | hmd
    · have h1 : (1 : FGL) - 0 - 0 = 1 := by ring
      simp only [hmm, hmd, zero_mul, add_zero, h1, one_mul]
      exact fgl_two_chunks_val_lt_comm row.chunks.d_1 row.chunks.d_0
        h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have hmd1 := sub_eq_zero.mp hmd
      have h1 : (1 : FGL) - 0 - 1 = 0 := by ring
      simp only [hmm, hmd1, zero_mul, add_zero, zero_add, h1, one_mul]
      exact fgl_two_chunks_val_lt_comm row.chunks.a_1 row.chunks.a_0
        h_chunks.2.1 h_chunks.1
  · have hmm1 := sub_eq_zero.mp hmm
    have hmd0 : row.flags.main_div = 0 := by
      have h := hmm1 ▸ h_mm_md; rwa [one_mul] at h
    have h1 : (1 : FGL) - 1 - 0 = 0 := by ring
    simp only [hmm1, hmd0, h1, zero_mul, zero_add, one_mul, mul_zero, add_zero]
    exact fgl_two_chunks_val_lt_comm row.chunks.c_1 row.chunks.c_0
      h_chunks.2.2.2.2.2.2.2.2.2.1 h_chunks.2.2.2.2.2.2.2.2.1

private lemma arithMul_opBus_c_hi_lt
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec row)
    (h_div_block : ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec row) :
    (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage row).c_hi.val < 4294967296 := by
  have h_chunks := h_full.2.2.2.1
  have h_table := h_full.2.1
  have h_c46 := h_full.2.2.1
  have h_div_mode := h_div_block.1
  have h_mm_bool := h_div_mode.2.1
  have h_md_bool := h_div_mode.1
  have h_mm_md := h_div_mode.2.2.1
  show row.flags.bus_res1.val < _
  have hbus : row.flags.bus_res1 = row.flags.sext * 4294967295
      + (1 - row.flags.m32) * (
          (1 - row.flags.main_mul - row.flags.main_div) * (row.chunks.d_2 + row.chunks.d_3 * 65536)
          + row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536)
          + row.flags.main_div * (row.chunks.a_2 + row.chunks.a_3 * 65536)) :=
    sub_eq_zero.mp h_c46
  rw [hbus]
  rcases ZiskFv.AirsClean.ArithTableProjections.m32_boolean row h_table with hm32 | hm32
  · have hsext := ZiskFv.AirsClean.ArithTableProjections.sext_zero_of_m32_zero row h_table hm32
    simp only [hm32, hsext, zero_mul, zero_add, sub_zero, one_mul]
    rcases mul_eq_zero.mp h_mm_bool with hmm | hmm
    · rcases mul_eq_zero.mp h_md_bool with hmd | hmd
      · have h1 : (1 : FGL) - 0 - 0 = 1 := by ring
        simp only [hmm, hmd, h1, one_mul, zero_mul, add_zero]
        exact fgl_two_chunks_val_lt_comm row.chunks.d_3 row.chunks.d_2
          h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · have hmd1 := sub_eq_zero.mp hmd
        have h1 : (1 : FGL) - 0 - 1 = 0 := by ring
        simp only [hmm, hmd1, zero_mul, add_zero, zero_add, h1, one_mul]
        exact fgl_two_chunks_val_lt_comm row.chunks.a_3 row.chunks.a_2
          h_chunks.2.2.2.1 h_chunks.2.2.1
    · have hmm1 := sub_eq_zero.mp hmm
      have hmd0 : row.flags.main_div = 0 := by
        have h := hmm1 ▸ h_mm_md; rwa [one_mul] at h
      have h1 : (1 : FGL) - 1 - 0 = 0 := by ring
      simp only [hmm1, hmd0, h1, zero_mul, zero_add, one_mul, mul_zero, add_zero]
      exact fgl_two_chunks_val_lt_comm row.chunks.c_3 row.chunks.c_2
        h_chunks.2.2.2.2.2.2.2.2.2.2.2.1 h_chunks.2.2.2.2.2.2.2.2.2.2.1
  · simp only [hm32, sub_self, zero_mul, add_zero]
    rcases ZiskFv.AirsClean.ArithTableProjections.sext_boolean row h_table with hs | hs
    · simp only [hs, zero_mul]; decide
    · simp only [hs, one_mul]
      show (4294967295 : FGL).val < 4294967296
      native_decide

private lemma arithMul_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (hpr : providerRow ∈ providerTable.table)
    (hcomp : providerTable.component =
      ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent)
    (hspec : providerTable.Spec)
    (hmatch : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
            (providerTable.environment providerRow))) 1)) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have h_row := (hspec providerRow hpr)
  rw [hcomp, ZiskFv.AirsClean.ArithMul.componentComplete_spec] at h_row
  exact entry_range_of_provider_match i h_sp hmatch
    (arithMul_opBus_c_lo_lt _ h_row.1 h_row.2)
    (arithMul_opBus_c_hi_lt _ h_row.1 h_row.2)

private theorem stepRegWrite_entry_range_aux
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n) (zs : ZiskStep trace i) (rd : RowDecode trace i zs)
    (hAvoid : RowOutsideDefectRegion trace i zs)
    (he : stepRegWrite (stepChannelOutput i zs rd)
      = some ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1))
    (h_ptr : Transpiler.wrap_to_regidx ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1).ptr ≠ 0) :
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
  | jalr c =>
    -- stepRegWrite [eRdAt rd.rows.finish] = some (eRdAt rd.rows.finish)
    have h_inj : (cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable
        rd.rows.finish.val)).toEntry 1 1
      = (cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1 := by
      have : stepRegWrite (stepChannelOutput i (.jalr c) rd) =
        some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable
          rd.rows.finish.val)).toEntry 1 1) := by
        show stepRegWrite ⟨_, [eRdAt trace rd.rows.finish]⟩ = _
        simp [stepRegWrite, eRdAt, mainRowWithRomAt, MemBusMessage.toEntry]
      rw [this] at he; exact Option.some.inj he
    rw [← h_inj]
    -- Case split on store_pc (= boolF (rd ≠ 0))
    have h_sp := rd.h_store_pc
    simp only [mainOfTable_store_pc] at h_sp
    by_cases h_rd : (regidx_to_fin c.rd).val ≠ 0
    · -- rd ≠ 0: store_pc = 1
      have h_sp_rw : (mainTableRowAtOrZero trace.program trace.mainTable
          rd.rows.finish.val).core.store_pc = 1 := by
        rw [h_sp]; simp [ZiskFv.AirsClean.boolF, h_rd]
      rcases rd.h_jmp2 with ⟨h_align, h_j2⟩ | ⟨h_2row, h_j2⟩
      · -- aligned (1-row): rows.finish.val = i.val
        have h_fi_eq : rd.rows.finish.val = i.val :=
          (congr_arg Fin.val h_align).symm.trans rd.rows.architectural_start
        simp only [h_fi_eq] at h_sp_rw h_j2 ⊢
        apply cMemMessage_chunks_of_store_pc_one _ h_sp_rw
        simp only [mainOfTable_jmp_offset2] at h_j2; rw [h_j2]
        have h_pcv := hAvoid.h_pc_bound
        unfold MainSequentialPcDomain mainPcVal at h_pcv
        simp only [mainOfTable_pc] at h_pcv
        have h_bound := hAvoid.h_pc_offset_lt_2_32
          (BitVec.ofNat 64 (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc.val)
          (by unfold mainPcVal; simp only [mainOfTable_pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h_bound
        exact fgl_add_val_lt_of_sum_lt (by omega) (by omega)
      · -- unaligned (2-row): rows.finish = i+1, jmp2 = 3
        apply cMemMessage_chunks_of_store_pc_one _ h_sp_rw
        simp only [mainOfTable_jmp_offset2] at h_j2; rw [h_j2]
        -- Derive pc(finish) = pc(i) + 1 from Main transition
        have h_as : rd.rows.start.val = i.val := rd.rows.architectural_start
        have h_fi_eq : rd.rows.finish.val = i.val + 1 := by omega
        -- Get lowering properties for the start row
        rcases rd.rows.lowering with ⟨h_eq, _⟩ | ⟨_, _, _, _, _, h_flag, h_setpc, h_j2s, _⟩
        · exact absurd (congr_arg Fin.val h_eq) (by omega)
        · -- Main transition: pc(i+1) = nextPcMux(i)
          have h_idx_succ : i.val + 1 < trace.mainTable.table.length :=
            by have := rd.rows.finish_has_successor; omega
          have h_seg := trace.mainTable_fixed.segment_l1_succ i.val h_idx_succ
          have h_trans := trace.mainTransition_to_next_pc i.val h_idx_succ h_seg
          -- Specialize: set_pc=0, flag=0, jmp2=1 at start (= i)
          simp only [ZiskFv.Airs.Main.pc_handshake_with_next_pc, mainOfTable_pc,
            mainOfTable_set_pc, mainOfTable_c_0, mainOfTable_jmp_offset1,
            mainOfTable_jmp_offset2, mainOfTable_flag] at h_trans
          rw [h_as] at h_setpc h_flag h_j2s
          simp only [mainOfTable_set_pc, mainOfTable_flag, mainOfTable_jmp_offset2] at h_setpc h_flag h_j2s
          rw [h_setpc, h_flag, h_j2s] at h_trans
          simp at h_trans
          have h_pc_finish : (mainTableRowAtOrZero trace.program trace.mainTable
              rd.rows.finish.val).core.pc
            = (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc + 1 := by
            rw [h_fi_eq]; exact h_trans
          rw [h_pc_finish]
          -- pc(i) + 1 + 3 = pc(i) + 4
          have h_pcv := hAvoid.h_pc_bound
          unfold MainSequentialPcDomain mainPcVal at h_pcv
          simp only [mainOfTable_pc] at h_pcv
          have h_bound := hAvoid.h_pc_offset_lt_2_32
            (BitVec.ofNat 64 (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc.val)
            (by unfold mainPcVal; simp only [mainOfTable_pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega)
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h_bound
          have h_sum : ((mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc
              + 1 + 3 : FGL) = (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.pc
              + 4 := by ring
          rw [h_sum]
          exact fgl_add_val_lt_of_sum_lt (by omega) (by omega)
    · -- rd = 0: addr2 = 0 via AddressSpec, contradicting h_ptr
      push_neg at h_rd
      rcases rd.h_jmp2 with ⟨h_align, _⟩ | ⟨h_2row, _⟩
      · -- aligned: rows.finish = i, derive addr2 = 0 at row i
        have h_fi_eq : rd.rows.finish.val = i.val :=
          (congr_arg Fin.val h_align).symm.trans rd.rows.architectural_start
        have h_addr_spec := RomDecodeBinding.mainAddressSpec_at trace
          ⟨i.val, trace.mainTable_index i⟩
        have h_addr2 : (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.addr2
            = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_offset
            + (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind
              * (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.a_0 :=
          h_addr_spec.2.2.1
        have h_si : (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind
            = 0 := by
          have := rd.h_store_ind; rw [mainRowWithRomAt, h_fi_eq] at this; exact this
        have h_so : (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_offset
            = 0 := by
          have := rd.h_store_offset
          rw [mainRowWithRomAt, h_fi_eq, if_pos h_rd] at this; exact this
        exfalso; apply h_ptr
        show Transpiler.wrap_to_regidx
          (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.addr2 = 0
        rw [h_addr2, h_si, h_so]
        simp [Transpiler.wrap_to_regidx]
      · -- unaligned: timestamps at i and i+1 differ, so h_inj is False
        exfalso
        have h_as := rd.rows.architectural_start
        have h_fi_eq : rd.rows.finish.val = i.val + 1 := by omega
        have h_ms_i := mainRowAt_main_step trace.mainTable_component (trace.mainTable_index i)
        have h_ms_f : (mainTableRowAtOrZero trace.program trace.mainTable
              rd.rows.finish.val).rom.main_step
            = (rd.rows.finish.val : FGL) :=
          mainRowAt_main_step trace.mainTable_component
            (by have := rd.rows.finish_has_successor; omega)
        have h_ts : (3 : FGL) + (rd.rows.finish.val : FGL) * 4
            = 3 + (i.val : FGL) * 4 := by
          have := congrArg Interaction.MemoryBusEntry.timestamp h_inj
          simp only [MemBusMessage.toEntry, cMemMessage, h_ms_f, h_ms_i] at this
          exact this
        rw [h_fi_eq] at h_ts
        have h_cancel : (↑(i.val + 1) : FGL) = (↑i.val : FGL) :=
          mul_right_cancel₀ (show (4 : FGL) ≠ 0 from by decide) (add_left_cancel h_ts)
        rw [Nat.cast_succ] at h_cancel
        have : (1 : FGL) = 0 := by
          have := sub_eq_zero.mpr h_cancel; ring_nf at this; exact this
        exact one_ne_zero this
  | and c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 14 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_AND_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_AND = 14 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | or c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inl h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 15 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_OR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_OR = 15 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | xor c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inr h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := mode_pins_of_emit_op_eq_16_of_static_spec
      _ h_spec_facts h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_XOR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_XOR = 16 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | andi c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 14 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_AND_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_AND = 14 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | ori c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inl h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 15 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_OR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_OR = 15 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | xori c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inr h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := mode_pins_of_emit_op_eq_16_of_static_spec
      _ h_spec_facts h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_XOR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_XOR = 16 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | sub c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_sub_provided trace i h_ieo h_op
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_add_sub_entry_range _ h_spec_facts h_core h_wf
      11 (by norm_num) h_op_eq.symm (Or.inr rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | add c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD := by
      have := rd.h_main_op; exact this
    obtain ⟨_, h_disj⟩ := main_request_add_provided trace i h_ieo h_op
    rcases h_disj with ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ |
        ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩
    · have h_row := (hspec pr hpr)
      rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
      have h_spec_facts := h_row.2
      have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
      have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
      have h_op_eq := hmatch.2.1
      simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
        ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
        ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
      rw [h_op] at h_op_eq
      have h_carry := binary_static_add_sub_entry_range _ h_spec_facts h_core h_wf
        10 (by norm_num) h_op_eq.symm (Or.inl rfl)
      exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
    · exact binaryAdd_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | addi c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD := by
      have := rd.h_main_op; exact this
    obtain ⟨_, h_disj⟩ := main_request_add_provided trace i h_ieo h_op
    rcases h_disj with ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ |
        ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩
    · have h_row := (hspec pr hpr)
      rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
      have h_spec_facts := h_row.2
      have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
      have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
      have h_op_eq := hmatch.2.1
      simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
        ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
        ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
      rw [h_op] at h_op_eq
      have h_carry := binary_static_add_sub_entry_range _ h_spec_facts h_core h_wf
        10 (by norm_num) h_op_eq.symm (Or.inl rfl)
      exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
    · exact binaryAdd_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | slt c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 7 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LT h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | sltu c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inr h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 6 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LTU h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | slti c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 7 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LT h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | sltiu c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inr h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 6 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LTU h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | addw c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_w_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_w_mode_carry_7_zero _ h_spec_facts h_core h_wf
      26 h_op_eq.symm (Or.inl rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | subw c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_w_provided trace i h_ieo (Or.inr h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_w_mode_carry_7_zero _ h_spec_facts h_core h_wf
      27 h_op_eq.symm (Or.inr rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | addiw c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_w_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.opBusMessage] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_w_mode_carry_7_zero _ h_spec_facts h_core h_wf
      26 h_op_eq.symm (Or.inl rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | mulw c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | mulhu c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulhu_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | mulh c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulh_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | mulhsu c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulhsu_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | div c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_div_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | divu c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_divu_provided trace i h_ieo (Or.inl h_op)
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | divuw c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_divuw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | remu c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_remu_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | remuw c =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_remuw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | _ =>
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    apply cMemMessage_chunks_of_store_pc_zero _ h_sp
    · sorry
    · sorry

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
      Transpiler.wrap_to_regidx ((cMemMessage
          (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val)).toEntry 1 1).ptr ≠ 0 →
      ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
        ((cMemMessage
          (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val)).toEntry 1 1) :=
    fun i he h_ptr =>
    stepRegWrite_entry_range_aux i (ziskStep i) (rowDecodes i) (hAvoidKnownBugs i) he h_ptr
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
