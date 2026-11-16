import ZiskFv.Compliance.TraceLevelExport.CanonicalSyntaxBoundary
import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterPlatformProjection
import ZiskFv.Compliance.TraceLevelExport.MappedMemoryInvariant

/-!
# Same-trace source-head induction facts

The caller remains `AcceptedZiskTrace n`. Every instruction below is at
`checked.index i`; a terminal producer may lie outside `Fin n`, but remains in
Main. In particular no total family of auxiliary architectural steps is used.

This module does not assert the proposed Root. It derives the physical writer
classification, register/PC boot, and actual architectural memory/PC successor
facts needed by a joint induction. The unresolved load obligation is read
soundness at the source replay prefix, not merely mutable-table presence.
The three original narrow-store preserved-byte leaves remain unchanged.
-/

namespace ZiskFv.Compliance.CanonicalSyntaxBoundary.SourceHeadRegisterPcPlatform

open Goldilocks
open CanonicalExecutionRows RawProgramBinding SerializedExecutionRows
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation (RegSlot)
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Channels.MemoryBus

variable {n rawLength : Nat} {trace : AcceptedZiskTrace n}
variable {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
variable {rawProgram : Fin rawLength → BitVec 32}
variable (checked : CheckedSyntax trace start addr rawProgram)

@[simp] theorem index_val (i : Fin checked.count) :
    (checked.index i).val = sourceStart checked.lowering i := rfl

theorem owner_spec (row : Fin n) :
    sourceStart checked.lowering (checked.owner row) ≤ row.val ∧
      row.val < sourceStart checked.lowering (checked.owner row) +
        (checked.lowering (checked.owner row)).width :=
  physicalOwner_spec checked.lowering
    ⟨row.val, Nat.lt_of_lt_of_le row.isLt checked.covered⟩

theorem endpoint_zero_of_empty (empty : checked.count = 0) : checked.endpoint = 0 := by
  unfold CheckedSyntax.endpoint sourceEnd rowPrefix
  apply Finset.sum_eq_zero
  intro i _
  have inside := i.isLt
  omega

/-- Empty syntax really has an empty physical domain. No boot fact is unguarded. -/
theorem empty_domain (empty : checked.count = 0) : n = 0 := by
  have endpoint := endpoint_zero_of_empty checked empty
  have covered := checked.covered
  change n ≤ checked.endpoint at covered
  omega

/-- The original head bound need not bound the final physical cut. -/
theorem endpoint_le_n_succ : checked.endpoint ≤ n + 1 := by
  by_cases empty : checked.count = 0
  · rw [endpoint_zero_of_empty checked empty]
    omega
  · let last : Fin checked.count := ⟨checked.count - 1, by omega⟩
    have cut := prefix_succ (sourceWidth checked.lowering) last
    have final : last.val + 1 = checked.count := by dsimp [last]; omega
    rw [final] at cut
    change checked.endpoint = sourceStart checked.lowering last +
      (checked.lowering last).width at cut
    have inside := checked.headWithin last
    rcases (checked.lowering last).count with one | two
    · change (checked.lowering last).width = 1 at one
      omega
    · change (checked.lowering last).width = 2 at two
      omega

theorem span_room (i : Fin checked.count) :
    (checked.index i).val + (checked.lowering i).width ≤ trace.mainTable.table.length := by
  have cut := prefix_succ (sourceWidth checked.lowering) i
  have bounded := prefix_mono (sourceWidth checked.lowering) (Nat.succ_le_of_lt i.isLt)
  have room := checked.room
  change rowPrefix (sourceWidth checked.lowering) (i.val + 1) =
    sourceStart checked.lowering i + (checked.lowering i).width at cut
  change rowPrefix (sourceWidth checked.lowering) (i.val + 1) ≤
    sourceEnd checked.lowering at bounded
  rw [index_val]
  omega

variable (binding : ProgramRowsBinding trace start addr rawProgram)

include binding

/-- Real raw decode fixes the producer, also for nonfinal two-row JALR. -/
theorem producer_stop (i : Fin checked.count) :
    stepProducerRow (checked.index i) (checked.steps i) (checked.decoded binding i) + 1 =
      sourceStart checked.lowering i + (checked.lowering i).width := by
  have width := source_width_at_selected_pc trace (checked.index i) (checked.steps i)
    start addr rawProgram binding (checked.rawDecodes i)
    (checked.selected i) (checked.lowering i) (checked.atPc i)
  have placed := ExecutionSpanLegacy.producer_eq_index_or_succ
    (checked.index i) (checked.steps i) (checked.decoded binding i)
  change (checked.lowering i).width =
    stepProducerRow (checked.index i) (checked.steps i) (checked.decoded binding i) + 1 -
      (checked.index i).val at width
  rw [index_val] at width placed
  omega

/-- An actual selected first C request of an expanded source word is inactive. -/
theorem expanded_first_no_write (i : Fin checked.count)
    (two : (checked.lowering i).width = 2) :
    actualCRegisterWriteAt trace
      ⟨(checked.index i).val, trace.mainTable_index (checked.index i)⟩ = none := by
  obtain ⟨rd, rs1⟩ := expanded_source_register_bounds (checked.lowering i) two
  apply actualCRegisterWriteAt_of_mult_zero
  exact expanded_main_first_cMemInteraction_mult_zero trace start addr rawProgram binding
    (checked.selected i) (checked.lowering i) two rd rs1 _ (checked.atPc i)

omit binding in
private theorem no_write_store_reg_zero {q : Nat} {t : AcceptedZiskTrace q}
    (i : Fin q) (step : ZiskStep t i) (decoded : RowDecode t i step)
    (none : stepRegWrite (stepChannelOutput i step decoded) = Option.none) :
    (mainTableRowAtOrZero t.program t.mainTable
      (stepProducerRow i step decoded)).rom.store_reg = 0 := by
  cases step <;> first | exact decoded.h_store_reg | exact nomatch none

/-- The computed interval owner, not an arbitrary equality hypothesis, is the
real architectural producer of every selected physical C write below n. -/
theorem actual_write_owner (row : Fin n) (entry : Interaction.MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace
      ⟨row.val, trace.mainTable_index row⟩ = some entry) :
    stepProducerRow (checked.index (checked.owner row)) (checked.steps (checked.owner row))
        (checked.decoded binding (checked.owner row)) = row.val ∧
      stepRegWrite (stepChannelOutput (checked.index (checked.owner row))
        (checked.steps (checked.owner row)) (checked.decoded binding (checked.owner row))) =
          some entry := by
  let i := checked.owner row
  have owner := owner_spec checked row
  have stop := producer_stop checked binding i
  have terminal : stepProducerRow (checked.index i) (checked.steps i)
      (checked.decoded binding i) = row.val := by
    rcases (checked.lowering i).count with one | two
    · change (checked.lowering i).width = 1 at one
      change sourceStart checked.lowering i ≤ row.val ∧
        row.val < sourceStart checked.lowering i + (checked.lowering i).width at owner
      omega
    · change (checked.lowering i).width = 2 at two
      by_cases first : row.val = (checked.index i).val
      · have sameRow : row = checked.index i := Fin.ext first
        have inactive := expanded_first_no_write checked binding i two
        rw [sameRow, inactive] at written
        cases written
      · change sourceStart checked.lowering i ≤ row.val ∧
          row.val < sourceStart checked.lowering i + (checked.lowering i).width at owner
        rw [index_val] at first
        omega
  obtain ⟨registerOp, entryEq⟩ := actualCRegisterWriteAt_some_memop3 trace _ written
  have register := (cMemMessage_reg_selectors_of_memop3 trace
    ⟨row.val, trace.mainTable_index row⟩ registerOp).1
  rcases stepRegWrite_eq_none_or_cMemMessage (checked.index i) (checked.steps i)
      (checked.decoded binding i) with none | someWrite
  · have inactive := no_write_store_reg_zero (checked.index i) (checked.steps i)
      (checked.decoded binding i) none
    rw [terminal, register] at inactive
    exact False.elim (one_ne_zero inactive)
  · refine ⟨terminal, ?_⟩
    rw [terminal] at someWrite
    exact someWrite.trans (congrArg Option.some entryEq.symm)

omit binding in
/-- A preceding physical writer has a strictly preceding architectural owner. -/
theorem owner_before_head (cut : Fin checked.count) (row : Fin n)
    (before : row.val < (checked.index cut).val) :
    (checked.owner row).val < cut.val := by
  by_contra notBefore
  have monotone := prefix_mono (sourceWidth checked.lowering) (Nat.le_of_not_gt notBefore)
  have owner := (owner_spec checked row).1
  change sourceStart checked.lowering cut ≤
    sourceStart checked.lowering (checked.owner row) at monotone
  rw [index_val] at before
  omega

/-- Raw-walk read coverage specialized to the SAME checked source heads. The
supplier is a genuine earlier architectural producer; auxiliaries are not steps. -/
theorem register_read_origin (cut : Fin checked.count)
    (slot : RegSlot) (operand : slot = .a ∨ slot = .b)
    (active : slot.selector
      (mainTableRowAtOrZero trace.program trace.mainTable (checked.index cut).val) = 1)
    (r : Fin 32)
    (pointer : Transpiler.wrap_to_regidx (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (checked.index cut).val)).ptr = r) :
    ((slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable (checked.index cut).val)).value_0 = 0 ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable (checked.index cut).val)).value_1 = 0) ∨
    ∃ (row : Fin n) (entry : Interaction.MemoryBusEntry FGL),
      (checked.owner row).val < cut.val ∧
      stepProducerRow (checked.index (checked.owner row)) (checked.steps (checked.owner row))
        (checked.decoded binding (checked.owner row)) = row.val ∧
      stepRegWrite (stepChannelOutput (checked.index (checked.owner row))
        (checked.steps (checked.owner row)) (checked.decoded binding (checked.owner row))) =
          some entry ∧
      Transpiler.wrap_to_regidx entry.ptr = r ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable (checked.index cut).val)).value_0 =
          entry.value_0 ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable (checked.index cut).val)).value_1 =
          entry.value_1 := by
  rcases physicalRegisterRead_lastWrite trace (checked.index cut) slot operand active r pointer with
    ⟨lo, hi, _⟩ | ⟨row, entry, before, written, target, _, lo, hi⟩
  · exact Or.inl ⟨lo, hi⟩
  · obtain ⟨producer, realWrite⟩ := actual_write_owner checked binding row entry written
    exact Or.inr ⟨row, entry, owner_before_head checked cut row before,
      producer, realWrite, target, lo, hi⟩

variable {init : State}
variable (premises : NewPremises trace init start addr rawProgram checked)

include premises

/-- All non-load physical writer ranges follow from the retained current Core
and defect facts. The load alternative is explicit, not discharged by xreg packing. -/
theorem writer_range_or_load (row : Fin n) (entry : Interaction.MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace
      ⟨row.val, trace.mainTable_index row⟩ = some entry)
    (nonzero : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range entry ∨
      ZiskStepLoadMemoryRows trace (checked.index (checked.owner row))
        (checked.steps (checked.owner row)) := by
  by_cases load : ZiskStepLoadMemoryRows trace (checked.index (checked.owner row))
      (checked.steps (checked.owner row))
  · exact Or.inr load
  · have realWrite := (actual_write_owner checked binding row entry written).2
    exact Or.inl (PhysicalRegisterWriteRanges.real_stepRegWrite_entry_range
      (checked.index (checked.owner row)) (checked.steps (checked.owner row))
      (checked.decoded binding (checked.owner row)) (premises.inputsAgree (checked.owner row))
      (premises.avoid (checked.owner row)) (fun h => False.elim (load h)) realWrite nonzero)

omit binding premises in
private theorem initial_state (i : Fin checked.count) (first : i.val = 0) :
    checked.ownerTrace init (checked.index i) = init := by
  rw [CheckedSyntax.state_at_index]
  simp only [first, CheckedSyntax.states]

omit binding premises in
private theorem initial_index (i : Fin checked.count) (first : i.val = 0) :
    (checked.index i).val = 0 := by
  simp [index_val, sourceStart, first]

private theorem initial_read_lanes (i : Fin checked.count) (first : i.val = 0)
    (slot : RegSlot) (operand : slot = .a ∨ slot = .b)
    (active : slot.selector
      (mainTableRowAtOrZero trace.program trace.mainTable (checked.index i).val) = 1)
    (r : Fin 32) (nonzero : r ≠ 0)
    (pointer : Transpiler.wrap_to_regidx (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (checked.index i).val)).ptr = r) :
    (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (checked.index i).val)).value_0 =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (checked.ownerTrace init (checked.index i))).xreg r) ∧
    (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (checked.index i).val)).value_1 =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (checked.ownerTrace init (checked.index i))).xreg r) := by
  have xreg : (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 init).xreg r = 0 := by
    apply ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    have cell := premises.regBoot r nonzero
    fin_cases r <;> simp_all [read_xreg, Sail.readReg, PreSail.readReg, reg_of_fin]
  rcases register_read_origin checked binding i slot operand active r pointer with
    ⟨lo, hi⟩ | ⟨row, entry, earlier, _⟩
  · rw [initial_state checked i first, xreg]
    exact ⟨lo.trans (by simp [ZiskFv.Trusted.lane_lo]),
      hi.trans (by simp [ZiskFv.Trusted.lane_hi])⟩
  · omega

/-- Genuine joint boot consumer, with no semantic/read/register agreement oracle.
The result is exactly the two non-memory inputs of `stepSound_of_evidence`.
It is not a StepSound theorem: the load/RMW memory residual is still required. -/
theorem initial_register_pc_platform (i : Fin checked.count) (first : i.val = 0) :
    ∃ _inputs : InputsAgree trace (checked.ownerTrace init) (checked.index i) (checked.steps i),
      LaneBridge trace (checked.ownerTrace init (checked.index i)) (checked.index i).val := by
  have pc : ((mainOfTable trace.program trace.mainTable).pc (checked.index i).val).val =
      ((checked.ownerTrace init (checked.index i)).regs.get? Register.PC).elim 0 BitVec.toNat := by
    rw [initial_index checked i first, initial_state checked i first]
    exact premises.pcBoot (Nat.zero_lt_of_lt i.isLt)
  have lanes := initial_read_lanes checked binding premises i first
  refine ⟨inputsAgree_of_pcBridge (checked.index i) pc (checked.steps i)
    (premises.inputsAgree i), ?_⟩
  exact {
    a_lo := fun r nz active pointer => (lanes .a (Or.inl rfl) active r nz pointer).1
    a_hi := fun r nz active pointer => (lanes .a (Or.inl rfl) active r nz pointer).2
    b_lo := fun r nz active pointer => (lanes .b (Or.inr rfl) active r nz pointer).1
    b_hi := fun r nz active pointer => (lanes .b (Or.inr rfl) active r nz pointer).2 }

omit binding premises in
/-- The recursively generated architectural successor is the actual retire;
this internal induction projection never executes an auxiliary instruction. -/
theorem states_retire (i : Fin checked.count) (result : ExecutionResult) (post : State)
    (executed : execute_instruction (sailInstructionOf (checked.index i) (checked.steps i))
      (checked.ownerTrace init (checked.index i)) = .ok result post) :
    checked.states init (i.val + 1) (Nat.succ_le_of_lt i.isLt) = retirePC post := by
  rw [CheckedSyntax.state_at_index] at executed
  change retirePC (sailStepPost (sailInstructionOf (checked.index i) (checked.steps i))
    (checked.states init i.val (Nat.le_of_lt i.isLt))) = _
  rw [sailStepPost, executed]

omit premises in
/-- The exact register preservation component of a successful real source
step. Only its actual destination xreg and nextPC can be written by the channel;
retire additionally changes PC. No CSR/platform equality is assumed. -/
theorem successor_platform_register (i : Fin checked.count) (r : Register)
    (notPc : r ≠ Register.PC) (notNextPc : r ≠ Register.nextPC)
    (notXreg : ∀ k : Fin 32, r ≠ reg_of_fin k)
    (sound : StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
      (checked.decoded binding i)) :
    (checked.states init (i.val + 1) (Nat.succ_le_of_lt i.isLt)).regs.get? r =
      (checked.states init i.val (Nat.le_of_lt i.isLt)).regs.get? r := by
  obtain ⟨result, post, bus⟩ := stepChannelOutput_busEffect_ok
    (checked.index i) (checked.steps i) (checked.decoded binding i)
    (checked.ownerTrace init (checked.index i))
  have executed : execute_instruction
      (sailInstructionOf (checked.index i) (checked.steps i))
      (checked.ownerTrace init (checked.index i)) = .ok result post :=
    ((stepSound_iff (checked.index i) (checked.steps i) (checked.decoded binding i)).mp sound).trans bus
  obtain ⟨nextPc, registers⟩ := post_regs_eq_of_stepChannelOutput
    (checked.index i) (checked.steps i) (checked.decoded binding i)
    (checked.ownerTrace init (checked.index i)) post result bus
  rw [states_retire checked i result post executed, retirePC_regs_of_ne post r notPc,
    registers, Std.ExtDHashMap.get?_insert,
    dif_neg (by simp only [beq_iff_eq]; exact Ne.symm notNextPc)]
  cases written : stepRegWrite
      (stepChannelOutput (checked.index i) (checked.steps i) (checked.decoded binding i)) with
  | none =>
    exact congrArg (fun state : State => state.regs.get? r) (checked.state_at_index init i)
  | some entry =>
    dsimp only
    by_cases zero : Transpiler.wrap_to_regidx entry.ptr = 0
    · rw [if_pos zero]
      exact congrArg (fun state : State => state.regs.get? r) (checked.state_at_index init i)
    · rw [if_neg zero, Std.ExtDHashMap.get?_insert,
        dif_neg (by simp only [beq_iff_eq]; exact Ne.symm (notXreg _))]
      exact congrArg (fun state : State => state.regs.get? r) (checked.state_at_index init i)

omit premises in
/-- CSR/platform preservation is an internal prefix projection: each successor
uses only the recursively established soundness of that real source word.
The zero prefix and final architectural endpoint require no extra instruction. -/
theorem platform_register_prefix_of_previous_sounds (j : Nat) (bound : j ≤ checked.count)
    (sounds : ∀ i : Fin checked.count, i.val < j →
      StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
        (checked.decoded binding i))
    (r : Register) (notPc : r ≠ Register.PC) (notNextPc : r ≠ Register.nextPC)
    (notXreg : ∀ k : Fin 32, r ≠ reg_of_fin k) :
    (checked.states init j bound).regs.get? r = init.regs.get? r := by
  revert bound sounds
  induction j with
  | zero =>
    intro bound sounds
    rfl
  | succ j ih =>
    intro bound sounds
    let i : Fin checked.count := ⟨j, by omega⟩
    have preserved := successor_platform_register checked binding i r notPc notNextPc notXreg
      (sounds i (by simp only [i, Fin.val_mk]; omega))
    exact preserved.trans (ih (by omega) (fun k hk => sounds k (by omega)))

omit binding premises in
private theorem readReg_ok_iff_lookup (state : State) (r : Register) (value : RegisterType r) :
    Sail.readReg r state = EStateM.Result.ok value state ↔ state.regs.get? r = some value := by
  cases cell : state.regs.get? r <;> simp [Sail.readReg, PreSail.readReg, cell]

omit premises in
/-- The actual initial RISC-V profile is preserved in full, with the SAME
mstatus/PMA/misa/mseccfg values and all original numeric/attribute conditions.
This equivalence introduces no platform oracle or new boot assumption. -/
theorem risc_v_profile_prefix_iff (j : Nat) (bound : j ≤ checked.count)
    (sounds : ∀ i : Fin checked.count, i.val < j →
      StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
        (checked.decoded binding i))
    (mstatus : RegisterType Register.mstatus) (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa) (mseccfg : RegisterType Register.mseccfg) :
    RISC_V_assumptions (checked.states init j bound) mstatus pmaRegion misa mseccfg ↔
      RISC_V_assumptions init mstatus pmaRegion misa mseccfg := by
  have privilege := platform_register_prefix_of_previous_sounds checked binding j bound sounds
    Register.cur_privilege (by decide) (by decide)
    (fun k => Ne.symm (reg_of_fin_neq_cur_privilege (r := k)))
  have status := platform_register_prefix_of_previous_sounds checked binding j bound sounds
    Register.mstatus (by decide) (by decide)
    (fun k => Ne.symm (reg_of_fin_neq_mstatus (r := k)))
  have regions := platform_register_prefix_of_previous_sounds checked binding j bound sounds
    Register.pma_regions (by decide) (by decide)
    (fun k => Ne.symm (reg_of_fin_neq_pma_regions (r := k)))
  have tohost := platform_register_prefix_of_previous_sounds checked binding j bound sounds
    Register.htif_tohost_base (by decide) (by decide)
    (fun k => Ne.symm (reg_of_fin_neq_htif_tohost_base (r := k)))
  have misaCell := platform_register_prefix_of_previous_sounds checked binding j bound sounds
    Register.misa (by decide) (by decide) (by intro k; fin_cases k <;> simp [reg_of_fin])
  have mseccfgCell := platform_register_prefix_of_previous_sounds checked binding j bound sounds
    Register.mseccfg (by decide) (by decide) (by intro k; fin_cases k <;> simp [reg_of_fin])
  simp only [RISC_V_assumptions]
  rw [readReg_ok_iff_lookup (checked.states init j bound) Register.cur_privilege Privilege.Machine,
    readReg_ok_iff_lookup init Register.cur_privilege Privilege.Machine,
    readReg_ok_iff_lookup (checked.states init j bound) Register.mstatus mstatus,
    readReg_ok_iff_lookup init Register.mstatus mstatus,
    readReg_ok_iff_lookup (checked.states init j bound) Register.pma_regions [pmaRegion],
    readReg_ok_iff_lookup init Register.pma_regions [pmaRegion],
    readReg_ok_iff_lookup (checked.states init j bound) Register.htif_tohost_base none,
    readReg_ok_iff_lookup init Register.htif_tohost_base none,
    readReg_ok_iff_lookup (checked.states init j bound) Register.mseccfg mseccfg,
    readReg_ok_iff_lookup init Register.mseccfg mseccfg,
    privilege, status, regions, tohost, misaCell, mseccfgCell]

omit premises in
/-- At any real source head the full platform profile is exactly the initial
one, conditional only on the internal strictly preceding source sounds. -/
theorem source_head_risc_v_profile_iff (i : Fin checked.count)
    (sounds : ∀ k : Fin checked.count, k.val < i.val →
      StepSound trace (checked.ownerTrace init) (checked.index k) (checked.steps k)
        (checked.decoded binding k))
    (mstatus : RegisterType Register.mstatus) (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa) (mseccfg : RegisterType Register.mseccfg) :
    RISC_V_assumptions (checked.ownerTrace init (checked.index i)) mstatus pmaRegion misa mseccfg ↔
      RISC_V_assumptions init mstatus pmaRegion misa mseccfg := by
  rw [CheckedSyntax.state_at_index]
  exact risc_v_profile_prefix_iff checked binding i.val (Nat.le_of_lt i.isLt) sounds
    mstatus pmaRegion misa mseccfg

omit premises in
/-- PC at the complete successor cut, including the last old n+1 endpoint.
Only the recursively established current soundness is consumed here. -/
theorem successor_pc (i : Fin checked.count)
    (sound : StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
      (checked.decoded binding i)) :
    (checked.states init (i.val + 1) (Nat.succ_le_of_lt i.isLt)).regs.get? Register.PC =
      some (register_type_pc_equiv ▸ BitVec.ofNat 64
        ((mainOfTable trace.program trace.mainTable).pc
          (sourceStart checked.lowering i + (checked.lowering i).width)).val) := by
  obtain ⟨result, post, executed, pc⟩ := stepSound_producer_nextPC
    (checked.index i) (checked.steps i) (checked.decoded binding i) sound
  rw [states_retire checked i result post executed, retirePC_pc, pc,
    producer_stop checked binding i]

omit premises in
/-- The genuine current source instruction advances mutable memory once.
This establishes a prefix invariant after soundness, not read soundness before it. -/
theorem successor_memory (i : Fin checked.count)
    (sound : StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
      (checked.decoded binding i)) :
    (checked.states init (i.val + 1) (Nat.succ_le_of_lt i.isLt)).mem =
      replayMemoryAfterBusRows (checked.states init i.val (Nat.le_of_lt i.isLt)).mem
        (memoryRowsOfStep trace (checked.index i) (checked.steps i)) := by
  obtain ⟨result, post, bus⟩ := stepChannelOutput_busEffect_ok
    (checked.index i) (checked.steps i) (checked.decoded binding i)
    (checked.ownerTrace init (checked.index i))
  have executed : execute_instruction
      (sailInstructionOf (checked.index i) (checked.steps i))
      (checked.ownerTrace init (checked.index i)) = .ok result post :=
    ((stepSound_iff (checked.index i) (checked.steps i) (checked.decoded binding i)).mp sound).trans bus
  rw [states_retire checked i result post executed, retirePC_mem]
  have memory := post_mem_eq_replay_of_stepChannelOutput (checked.index i) (checked.steps i)
    (checked.decoded binding i) (checked.ownerTrace init (checked.index i)) post result bus
  rw [channel_replay_eq_memoryRowsOfStep, CheckedSyntax.state_at_index] at memory
  exact memory

omit premises in
/-- Consecutive architectural heads compose across either actual source width.
No PC agreement is asserted at an internal JALR row. -/
theorem next_head_pc (i j : Fin checked.count) (next : j.val = i.val + 1)
    (sound : StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
      (checked.decoded binding i)) :
    (checked.ownerTrace init (checked.index j)).regs.get? Register.PC =
      some (register_type_pc_equiv ▸ BitVec.ofNat 64
        ((mainOfTable trace.program trace.mainTable).pc (checked.index j).val).val) := by
  rw [CheckedSyntax.state_at_index]
  have pc := successor_pc checked binding i sound
  rw [← source_successor checked.lowering i j next] at pc
  simpa only [next, index_val] using pc

omit premises in
/-- The memory component of the joint induction hypothesis, proved by recursion
from strictly previous real source sounds. This includes the empty prefix and
the complete final state without requiring a step at the endpoint. -/
theorem memory_prefix_of_previous_sounds (j : Nat) (bound : j ≤ checked.count)
    (sounds : ∀ i : Fin checked.count, i.val < j →
      StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
        (checked.decoded binding i)) :
    (checked.states init j bound).mem =
      replayMemoryAfterBusRows init.mem
        (((List.finRange checked.count).take j).flatMap
          (fun i => memoryRowsOfStep trace (checked.index i) (checked.steps i))) := by
  revert bound sounds
  induction j with
  | zero =>
    intro bound sounds
    rfl
  | succ j ih =>
    intro bound sounds
    let i : Fin checked.count := ⟨j, by omega⟩
    have previous := ih (by omega) (fun k hk => sounds k (by omega))
    calc
      (checked.states init (j + 1) bound).mem =
          replayMemoryAfterBusRows
            (checked.states init j (by omega)).mem
            (memoryRowsOfStep trace (checked.index i) (checked.steps i)) :=
        successor_memory checked binding i
          (sounds i (by simp only [i, Fin.val_mk]; omega))
      _ = replayMemoryAfterBusRows
          (replayMemoryAfterBusRows init.mem
            (((List.finRange checked.count).take j).flatMap
              (fun k => memoryRowsOfStep trace (checked.index k) (checked.steps k))))
          (memoryRowsOfStep trace (checked.index i) (checked.steps i)) := by
        rw [previous]
      _ = replayMemoryAfterBusRows init.mem
          (((List.finRange checked.count).take (j + 1)).flatMap
            (fun k => memoryRowsOfStep trace (checked.index k) (checked.steps k))) := by
        rw [finitePrefix_succ i, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          replayMemoryAfterBusRows_append]

omit binding premises in
/-- Exact minimal load residual: the coherence existential is equivalent to the
eight actual read bytes, not to presence or mappedness of those addresses. -/
theorem load_coherence_iff_read (state : State) (entry : Interaction.MemoryBusEntry FGL)
    (memory : entry.as = 2) (pull : entry.multiplicity = -1) :
    LoadMemoryTimelineCoherenceEvidence state entry ↔
      ReadEventReplayAgreement state.mem (eventOfEntry entry) := by
  constructor
  · rintro ⟨initial, rows, facts, stateAt, prior, later, split, seed, atState, coherent⟩
    have bytes :=
      ZiskFv.ZiskCircuit.MemTimeline.Spike.stateBytesAtPrefix_of_rowTraceCoherence
        (entry := entry) facts stateAt prior seed coherent
    rw [atState] at bytes
    have read := facts.prefixReadSound prior entry later split memory pull
    have byte0 := bytes 0 (by decide)
    simp only [Nat.add_zero] at byte0
    unfold ReadEventReplayAgreement at read ⊢
    rw [byte0, bytes 1 (by decide), bytes 2 (by decide), bytes 3 (by decide),
      bytes 4 (by decide), bytes 5 (by decide), bytes 6 (by decide), bytes 7 (by decide)]
    exact read
  · intro read
    have sound : MemoryBusRowsPrefixReadSound state.mem [entry] := by
      intro prior row later split _ _
      cases prior with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        rw [← split.1]
        exact read
      | cons a rest =>
        have lengths := congrArg List.length split
        simp only [List.length_cons, List.length_append, List.length_nil] at lengths
        omega
    exact loadEvidence_of_loadMemReplay (initialState := state)
      (priorRows := []) (laterRows := [])
      { initialMemory := state.mem
        prefixReadSound := sound
        initialAgreement := fun _ => rfl }
      rfl rfl

omit binding premises in
private theorem store_coherence_of_preserved (state : State)
    (entry : Interaction.MemoryBusEntry FGL) (width : Nat)
    (notRead : entry.multiplicity ≠ -1)
    (preserved : StoreRmwPreservedBytesAtPrefix state.mem entry width) :
    StoreRmwMemoryCoherenceEvidence state entry width := by
  have sound : MemoryBusRowsPrefixReadSound state.mem [entry] := by
    intro prior row later split _ pull
    cases prior with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      rw [← split.1] at pull
      exact False.elim (notRead pull)
    | cons a rest =>
      have lengths := congrArg List.length split
      simp only [List.length_cons, List.length_append, List.length_nil] at lengths
      omega
  exact storeEvidence_of_loadMemReplay (initialState := state)
    (priorRows := []) (laterRows := [])
    { initialMemory := state.mem
      prefixReadSound := sound
      initialAgreement := fun _ => rfl }
    rfl rfl preserved

omit binding in
/-- Every non-load memory residual is derived. The singleton here contains the
actual store entry: it is read-sound because it is a write, not an invented
accepted replay. The three retained preserved-byte leaves supply its only RMW
content. The seven genuine load cases remain explicit in the conclusion. -/
theorem memory_evidence_or_load (i : Fin checked.count) :
    MemoryOpEvidenceFor trace (checked.ownerTrace init) (checked.index i) (checked.steps i) ∨
      ZiskStepLoadMemoryRows trace (checked.index i) (checked.steps i) := by
  have storeNotRead :
      (busSt trace (checked.index i) (Pilot.execRowOf trace (checked.index i))).e2.multiplicity ≠ -1 := by
    change (1 : FGL) ≠ -1
    decide
  cases same : checked.steps i <;>
    simp only [MemoryOpEvidenceFor, ZiskStepLoadMemoryRows]
  all_goals first
  | exact Or.inl True.intro
  | exact Or.inr True.intro
  | exact Or.inl (store_coherence_of_preserved _ _ _ storeNotRead
      (premises.sbPreserved i _ same))
  | exact Or.inl (store_coherence_of_preserved _ _ _ storeNotRead
      (premises.shPreserved i _ same))
  | exact Or.inl (store_coherence_of_preserved _ _ _ storeNotRead
      (premises.swPreserved i _ same))

omit premises binding in
/-- Source-grounded obstruction, expressed as an equivalence rather than a new
Root binder: each load needs the actual eight-byte read equation at its state. -/
theorem load_memory_obligation_iff (i : Fin checked.count)
    (load : ZiskStepLoadMemoryRows trace (checked.index i) (checked.steps i)) :
    MemoryOpEvidenceFor trace (checked.ownerTrace init) (checked.index i) (checked.steps i) ↔
      ReadEventReplayAgreement (checked.ownerTrace init (checked.index i)).mem
        (eventOfEntry (busLd trace (checked.index i) (Pilot.execRowOf trace (checked.index i))).e1) := by
  cases same : checked.steps i <;>
    simp only [same, MemoryOpEvidenceFor, ZiskStepLoadMemoryRows] at load ⊢
  all_goals first
  | contradiction
  | exact load_coherence_iff_read _ _ rfl rfl

/-!
The remaining implication is deliberately not a declaration with a new hypothesis
bundle. For each load head i, NewPremises and sounds STRICTLY before i must imply
`ReadEventReplayAgreement (checked.ownerTrace init (checked.index i)).mem
  (eventOfEntry (busLd trace (checked.index i)
    (Pilot.execRowOf trace (checked.index i))).e1)`.
`load_memory_obligation_iff` proves this is exactly the current memory residual.

`successor_memory` gives the state/replay-prefix equation from earlier sounds.
`BootMemoryAt` identifies its initial memory when the source is nonempty.
Accepted provider membership and chunk ranges still need replay-safe ordered
correspondence (or a direct read-at-prefix theorem), including MemAlign
alternatives, for the SAME accepted witness and physical source cut. The existing
load Core has successful byte lookup EXISTENCE (`h_input_bytes`), not equality
with the actual emitted B bytes. The old BootSegmentMemorySeed carried the
order/read burden. No non-entailment countermodel is claimed here; this is the
exact unproved implication, not an assumed-step proof of closure.
-/

end ZiskFv.Compliance.CanonicalSyntaxBoundary.SourceHeadRegisterPcPlatform
