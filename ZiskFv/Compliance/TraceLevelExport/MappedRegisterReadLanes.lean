import ZiskFv.Compliance.TraceLevelExport.SourcePhysicalRegisterWrites

/-!
# Actual source-cut register read lanes

The current read comes from the accepted raw walk's exact last physical C
writer, then its genuine source provider bounds recover the two FGL32 lanes.
Earlier real StepSounds give the mapped Sail register-cell agreement. Auxiliary
rows remain physical requests, never invented architectural steps.

The platform data below are the unchanged original boot-seed fields and
MemoryOpPlacement predicate, restricted to real source starts. In particular no
per-load presence, range, successful-read, or selector oracle is added.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.Compliance.Instantiation (RegSlot)

private theorem memPresent_of_real_load_placement
    {n : Nat} {trace : AcceptedZiskTrace n}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : Nat → List (Interaction.MemoryBusEntry FGL)}
    (memPresent_of_executionRows_nonempty :
      (List.range n).flatMap rowsOf ≠ [] → MutableMemPresent trace.witness)
    (i : Fin n) (step : ZiskStep trace i)
    (placement : MemoryOpPlacement trace rowsOf memInit i step)
    (load : ZiskStepLoadMemoryRows trace i step) : MutableMemPresent trace.witness := by
  apply memPresent_of_executionRows_nonempty
  intro empty
  have rows := rowsOf_eq_memoryRowsOfStep_of_placement i step placement
  have member : (memoryRowsOfStep trace i step).head! ∈ (List.range n).flatMap rowsOf := by
    apply List.mem_flatMap.mpr
    refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
    rw [rows]
    cases step <;> simp [ZiskStepLoadMemoryRows, memoryRowsOfStep] at load ⊢
  rw [empty] at member
  simp at member

private theorem sail_xreg_of_actual_cell
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r : Fin 32) (nonzero : r ≠ 0) (value : BitVec 64)
    (cell : state.regs.get? (reg_of_fin r) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) value)) :
    (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r = value := by
  apply ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
  fin_cases r <;> simp_all [read_xreg, Sail.readReg, PreSail.readReg, reg_of_fin]

section Source

variable {m rawLength : Nat}
variable (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
variable (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
variable (trace : AcceptedZiskTrace (sourceEnd L))
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (steps : ∀ i, ZiskStep trace (physicalStart L i))
variable (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
  start addr rawProgram)

variable (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
  (physicalStart L i).val = addr (selected i))
variable (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
variable (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
  some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
variable (cut : Fin m)
variable (sounds : ∀ i : Fin m, i.val < cut.val →
  StepSound trace (mappedSailTrace L steps init) (physicalStart L i) (steps i)
    (rowDecode_of_programDecode trace (physicalStart L i)
      (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
        start addr rawProgram binding (rawDecodes i))))
variable (inputs : ∀ i : Fin m, i.val < cut.val →
  InputsAgreeCore trace (mappedSailTrace L steps init) (physicalStart L i) (steps i))
variable (outside : ∀ i : Fin m, i.val < cut.val →
  RowOutsideDefectRegion trace (physicalStart L i) (steps i))

include binding rawDecodes atPc regBoot sounds inputs outside

private theorem source_register_read_lanes
    (memoryPresent : ∀ i : Fin m, i.val < cut.val →
      ZiskStepLoadMemoryRows trace (physicalStart L i) (steps i) →
        MutableMemPresent trace.witness)
    (slot : RegSlot) (operand : slot = .a ∨ slot = .b)
    (active : slot.selector
      (mainTableRowAtOrZero trace.program trace.mainTable (physicalStart L cut).val) = 1)
    (r : Fin 32) (nonzero : r ≠ 0)
    (pointer : Transpiler.wrap_to_regidx (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (physicalStart L cut).val)).ptr = r) :
    (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (physicalStart L cut).val)).value_0 =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (mappedSailTrace L steps init (physicalStart L cut))).xreg r) ∧
    (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable (physicalStart L cut).val)).value_1 =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (mappedSailTrace L steps init (physicalStart L cut))).xreg r) := by
  have cells := mappedRegAgree_actualPhysical_prefix rawProgram selected L trace
    start addr binding steps rawDecodes atPc init regBoot cut.val (Nat.le_of_lt cut.isLt) sounds
  have actualCell := cells r nonzero
  have sailValue :
      (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (mappedSailTrace L steps init (physicalStart L cut))).xreg r =
        actualPhysicalRegFile trace (physicalStart L cut).val
          (Nat.le_of_lt (physicalStart L cut).isLt) r := by
    apply sail_xreg_of_actual_cell _ r nonzero
    rw [state_at_start]
    exact actualCell
  rcases physicalRegisterRead_lastWrite trace (physicalStart L cut) slot operand active r pointer with
    ⟨lo, hi, zero⟩ | ⟨writer, entry, before, written, target, fileEq, lo, hi⟩
  · rw [sailValue, zero]
    constructor
    · simpa [ZiskFv.Trusted.lane_lo] using lo
    · simpa [ZiskFv.Trusted.lane_hi] using hi
  · have ranges := source_actualCRegisterWriteAt_entry_range rawProgram selected L trace
      start addr binding steps rawDecodes atPc (mappedSailTrace L steps init) cut
      inputs outside memoryPresent writer before entry written (by rw [target]; exact nonzero)
    rw [sailValue, fileEq]
    exact ⟨lo.trans (lane_lo_entryRegValue entry ranges).symm,
      hi.trans (lane_hi_entryRegValue entry ranges).symm⟩

/-- The four concrete A/B lo/hi fields at a source-derived physical start.
Every platform premise is an unchanged original seed field/predicate, not a new
read/coverage/range assumption. Only REAL source starts have placements or
StepSounds; no architectural label is assigned to an auxiliary physical row. -/
theorem laneBridge_at_source_start
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : Nat → List (Interaction.MemoryBusEntry FGL))
    (memPresent_of_executionRows_nonempty :
      (List.range (sourceEnd L)).flatMap rowsOf ≠ [] → MutableMemPresent trace.witness)
    (placements : ∀ i : Fin m, i.val < cut.val →
      MemoryOpPlacement trace rowsOf memInit (physicalStart L i) (steps i)) :
    LaneBridge trace (mappedSailTrace L steps init (physicalStart L cut))
      (physicalStart L cut).val := by
  have present : ∀ i : Fin m, i.val < cut.val →
      ZiskStepLoadMemoryRows trace (physicalStart L i) (steps i) →
        MutableMemPresent trace.witness :=
    fun i before load => memPresent_of_real_load_placement
      memPresent_of_executionRows_nonempty (physicalStart L i) (steps i)
      (placements i before) load
  have lanes := source_register_read_lanes rawProgram selected L trace start addr
    binding steps rawDecodes atPc init regBoot cut sounds inputs outside present
  exact
    { a_lo := fun r nonzero active pointer => (lanes .a (Or.inl rfl) active r nonzero pointer).1
      a_hi := fun r nonzero active pointer => (lanes .a (Or.inl rfl) active r nonzero pointer).2
      b_lo := fun r nonzero active pointer => (lanes .b (Or.inr rfl) active r nonzero pointer).1
      b_hi := fun r nonzero active pointer => (lanes .b (Or.inr rfl) active r nonzero pointer).2 }

end Source
end ZiskFv.Compliance.SerializedExecutionRows
