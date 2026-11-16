import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterPlatformProjection
import ZiskFv.Compliance.TraceLevelExport.OldCanonicalExecution

/-! Old supported executions retain their original platform memory primitives.
Only real source starts carry steps; final two-row expansions and the empty
execution are handled by the finite ordered source spine. -/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

private theorem memoryRowsOfStep_transport {q : Nat} {trace : AcceptedZiskTrace q}
    {i j : Fin q} (same : i = j) (step : ZiskStep trace i) :
    memoryRowsOfStep trace j (same ▸ step) = memoryRowsOfStep trace i step := by
  cases same
  rfl

private theorem memoryOpPlacement_transport {q : Nat} {trace : AcceptedZiskTrace q}
    {i j : Fin q} (same : i = j) (step : ZiskStep trace i)
    (rows : Nat → List (Interaction.MemoryBusEntry FGL))
    (memInit : Std.ExtHashMap Nat (BitVec 8)) :
    MemoryOpPlacement trace rows memInit j (same ▸ step) ↔
      MemoryOpPlacement trace rows memInit i step := by
  cases same
  rfl

/-- Recounting and reindexing a real source step does not change its bus rows. -/
theorem oldCanonicalMemoryRows {n : Nat} {words : Fin n → BitVec 32}
    (trace : AcceptedZiskTrace n) (L : ∀ i, SuccessfulRowLowering (words i))
    (room : sourceEnd L ≤ trace.mainTable.table.length)
    (starts : ∀ i, sourceStart L i = i.val)
    (steps : ∀ i : Fin n, ZiskStep trace i) (i : Fin n) :
    memoryRowsOfStep (recountWithinMain trace (sourceEnd L) room)
      (physicalStart L i) (oldCanonicalSteps trace L room starts steps i) =
      memoryRowsOfStep trace i (steps i) := by
  change memoryRowsOfStep _ _ ((oldCanonicalIndexEq L starts i) ▸
    recountStep trace room (architecturalCount_le_sourceEnd L) i (steps i)) = _
  rw [memoryRowsOfStep_transport]
  cases steps i <;> rfl

/-- Literal placement transports through equality of the real row and its
ordered prefix. In particular the original narrow-store RMW fact is unchanged. -/
theorem oldCanonicalMemoryPlacement {n : Nat} {words : Fin n → BitVec 32}
    (trace : AcceptedZiskTrace n) (L : ∀ i, SuccessfulRowLowering (words i))
    (room : sourceEnd L ≤ trace.mainTable.table.length)
    (starts : ∀ i, sourceStart L i = i.val)
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (oldRows newRows : Nat → List (Interaction.MemoryBusEntry FGL))
    (i : Fin n) (row : newRows i.val = oldRows i.val)
    (priorRows : (List.range i.val).flatMap newRows = (List.range i.val).flatMap oldRows)
    (placement : MemoryOpPlacement trace oldRows memInit i (steps i)) :
    MemoryOpPlacement (recountWithinMain trace (sourceEnd L) room)
      newRows memInit (physicalStart L i)
      (oldCanonicalSteps trace L room starts steps i) := by
  change MemoryOpPlacement _ _ _ _ ((oldCanonicalIndexEq L starts i) ▸
    recountStep trace room (architecturalCount_le_sourceEnd L) i (steps i))
  rw [memoryOpPlacement_transport]
  cases hstep : steps i <;>
    simpa only [hstep, recountStep, MemoryOpPlacement, recountIndex_val, row, priorRows] using placement

private theorem legacy_fin_prefix {α : Type} {n : Nat}
    (rows : Nat → List α) (j : Nat) (bound : j ≤ n) :
    ((List.finRange n).take j).flatMap (fun i => rows i.val) =
      (List.range j).flatMap rows := by
  have all : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [← List.flatMap_map, List.map_take, all]
  simp [List.take_range, Nat.min_eq_left bound]

/-- The original supported-domain seed supplies actual computed physical
platform leaves, without a total physical step family or an auxiliary seed. -/
theorem legacy_actualPhysicalMemory_platform
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (sail : SailTrace n) (steps : ∀ i : Fin n, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (aligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i))))
    (seed : BootSegmentMemorySeed trace sail steps) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        ∃ room : sourceEnd L ≤ trace.mainTable.table.length,
          ∃ starts : ∀ i, sourceStart L i = i.val,
            let physical := recountWithinMain trace (sourceEnd L) room
            let rows := actualPhysicalMemoryRowsOf physical seed.rowsOf
            rows = sourcePhysicalRowsOf L seed.rowsOf ∧
            ((List.range (sourceEnd L)).flatMap rows =
              (List.range n).flatMap seed.rowsOf) ∧
            (∀ i : Fin n, (List.range (physicalStart L i).val).flatMap rows =
              (List.range i.val).flatMap seed.rowsOf) ∧
            (∀ present : MutableMemPresent trace.witness,
              Nonempty (BootSegmentReadSoundInputs physical seed.memInit rows present)) ∧
            (((List.range (sourceEnd L)).flatMap rows ≠ []) →
              MutableMemPresent physical.witness) ∧
            (∀ i : Fin n, MemoryOpPlacement physical rows seed.memInit
              (physicalStart L i) (oldCanonicalSteps trace L room starts steps i)) := by
  obtain ⟨selected, L, widths, starts, ends⟩ :=
    RawDecodeRowLowering.old_raw_source_widths_and_placement trace steps start addr rawProgram
      binding rawDecodes aligned
  let decoded := fun i => rowDecode_of_programDecode trace i
    (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
      binding (rawDecodes i))
  have room : sourceEnd L ≤ trace.mainTable.table.length := by
    by_cases nonempty : 0 < n
    · let last : Fin n := ⟨n - 1, by omega⟩
      rw [ends last (by dsimp [last]; omega)]
      exact Nat.le_of_lt (ExecutionSpanLegacy.producer_has_successor last
        (steps last) (decoded last))
    · have empty : n = 0 := by omega
      subst n
      simp [sourceEnd, rowPrefix]
  let physical := recountWithinMain trace (sourceEnd L) room
  let canonical := oldCanonicalSteps trace L room starts steps
  have atPc : ∀ i, (mainOfTable physical.program physical.mainTable).pc
      (physicalStart L i).val = addr (selected i) := by
    intro i
    simpa only [physicalStart_val, starts i] using (widths i).1.symm
  have canonicalRows : ∀ i, memoryRowsOfStep physical (physicalStart L i) (canonical i) =
      seed.rowsOf i.val := by
    intro i
    rw [oldCanonicalMemoryRows trace L room starts steps]
    exact (rowsOf_eq_memoryRowsOfStep_of_placement i (steps i) (seed.placement i)).symm
  have slots : actualMainMutablePhysicalSlots physical =
      sourcePhysicalSlots L (fun i => seed.rowsOf i.val) := by
    rw [actual_main_mutable_slots_eq_sourcePhysicalSlots rawProgram selected L physical
      start addr binding canonical
      (oldCanonicalRawDecoded trace L room starts steps start addr rawProgram rawDecodes) atPc]
    congr 1
    funext i
    exact canonicalRows i
  have rowsEq : actualPhysicalMemoryRowsOf physical seed.rowsOf =
      sourcePhysicalRowsOf L seed.rowsOf := by
    unfold actualPhysicalMemoryRowsOf sourcePhysicalRowsOf
    rw [slots]
  have priorRows : ∀ i : Fin n,
      (List.range (physicalStart L i).val).flatMap
          (actualPhysicalMemoryRowsOf physical seed.rowsOf) =
        (List.range i.val).flatMap seed.rowsOf := by
    intro i
    rw [rowsEq]
    exact (sourcePhysicalRowsOf_prefix L seed.rowsOf i.val
      (Nat.le_of_lt i.isLt)).trans
      (legacy_fin_prefix seed.rowsOf i.val (Nat.le_of_lt i.isLt))
  have atStart : ∀ i : Fin n,
      actualPhysicalMemoryRowsOf physical seed.rowsOf i.val = seed.rowsOf i.val := by
    intro i
    rw [rowsEq]
    have inside : sourceStart L i < (sourcePhysicalSlots L
        (fun j => seed.rowsOf j.val)).length := by
      rw [sourcePhysicalSlots_length]
      exact sourceStart_lt_sourceEnd L i
    have slot := sourcePhysicalSlots_get_at_offset L
      (fun j => seed.rowsOf j.val) i 0
      (SuccessfulRowLowering.width_pos (L i))
    have placement := seed.placement i
    have width := (widths i).2
    conv_lhs => rw [← starts i]
    simp only [sourcePhysicalRowsOf, dif_pos inside]
    rcases (L i).count with one | two
    · simpa [sourceSpanSlots, SuccessfulRowLowering.width, one] using slot
    · have different : stepProducerRow i (steps i) (decoded i) ≠ i.val := by
        intro equal
        have wide : legacyWidth steps decoded i = 2 := width.symm.trans two
        unfold legacyWidth at wide
        rw [equal] at wide
        omega
      have nil : seed.rowsOf i.val = [] :=
        (rowsOf_eq_memoryRowsOfStep_of_placement i (steps i) placement).trans
          (memoryRowsOfStep_eq_nil_of_producer_ne_start i (steps i) (decoded i) different)
      simpa [sourceSpanSlots, SuccessfulRowLowering.width, two, nil] using slot
  refine ⟨selected, L, room, starts, rowsEq, ?_, priorRows, ?_, ?_, ?_⟩
  · rw [rowsEq]
    exact sourcePhysicalRowsOf_flatten L seed.rowsOf
  · intro present
    rw [rowsEq]
    exact ⟨recountReadSoundInputs trace L room seed.memInit seed.rowsOf present
      (seed.readSoundInputs present)⟩
  · rw [rowsEq, sourcePhysicalRowsOf_flatten]
    exact seed.memPresent_of_executionRows_nonempty
  · intro i
    apply oldCanonicalMemoryPlacement trace L room starts steps seed.memInit seed.rowsOf
      (actualPhysicalMemoryRowsOf physical seed.rowsOf) i (atStart i)
    · simpa only [physicalStart_val, starts i] using priorRows i
    · exact seed.placement i

end ZiskFv.Compliance.SerializedExecutionRows
