import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterReads
import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterWriteRanges

/-!
# Every selected physical C-register writer is a real source producer

Source interval ownership, the actual successful width, and the genuinely
inactive expanded first C request derive physical write coverage. There is no
architectural step at an auxiliary physical row and no caller coverage/range
promise. The same source-selected real step supplies its existing provider and
defect facts for the actual producer's canonical32 chunks.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows RawProgramBinding
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.Channels.MemoryBus

private theorem no_step_write_store_reg_zero {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (step : ZiskStep trace i) (decoded : RowDecode trace i step)
    (none : stepRegWrite (stepChannelOutput i step decoded) = Option.none) :
    (mainTableRowAtOrZero trace.program trace.mainTable
      (stepProducerRow i step decoded)).rom.store_reg = 0 := by
  cases step <;> first | exact decoded.h_store_reg | exact nomatch none

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

local notation "D" => (fun i => rowDecode_of_programDecode trace (physicalStart L i)
  (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
    start addr rawProgram binding (rawDecodes i)))

variable (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
  (physicalStart L i).val = addr (selected i))

include binding rawDecodes atPc

/-- The selected physical request is exactly the architectural write of its
actual source owner, at the real terminal index. -/
theorem source_actualCRegisterWriteAt_is_real_step
    (row : Fin (sourceEnd L)) (entry : Interaction.MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace
      ⟨row.val, trace.mainTable_index row⟩ = some entry) :
    ∃ i : Fin m, stepProducerRow (physicalStart L i) (steps i) (D i) = row.val ∧
      stepRegWrite (stepChannelOutput (physicalStart L i) (steps i) (D i)) = some entry := by
  let i := physicalOwner L row
  have owner : sourceStart L i ≤ row.val ∧ row.val < sourceStart L i + (L i).width :=
    physicalOwner_spec L row
  have stop : stepProducerRow (physicalStart L i) (steps i) (D i) + 1 =
      sourceStart L i + (L i).width :=
    mapped_producer_successor_eq_source_stop rawProgram selected L trace
      start addr binding steps rawDecodes atPc i
  have widths : (L i).width = 1 ∨ (L i).width = 2 := (L i).count
  have terminal : stepProducerRow (physicalStart L i) (steps i) (D i) = row.val := by
    dsimp only at owner stop ⊢
    rcases widths with one | two
    · rw [one] at owner stop
      omega
    · by_cases first : row.val = (physicalStart L i).val
      · have inactive := source_first_actualCRegisterWriteAt_none rawProgram selected L trace
          start addr binding atPc i two
        have sameRow : row = physicalStart L i := Fin.ext first
        rw [sameRow, inactive] at written
        cases written
      · simp only [physicalStart_val] at first stop
        rw [two] at owner stop
        omega
  obtain ⟨registerOp, entryEq⟩ := actualCRegisterWriteAt_some_memop3 trace _ written
  have register := (cMemMessage_reg_selectors_of_memop3 trace
    ⟨row.val, trace.mainTable_index row⟩ registerOp).1
  rcases stepRegWrite_eq_none_or_cMemMessage (physicalStart L i) (steps i) (D i) with
    none | someWrite
  · have inactive := no_step_write_store_reg_zero (physicalStart L i) (steps i) (D i) none
    rw [terminal, register] at inactive
    exact False.elim (one_ne_zero inactive)
  · refine ⟨i, terminal, ?_⟩
    rw [terminal] at someWrite
    exact someWrite.trans (congrArg Option.some entryEq.symm)

/-- Every physical write strictly before the current source cut has an earlier
REAL source owner. Retained per-real-step inputs, precise defect facts, and
actual load-memory support yield the source producer's chunk ranges. -/
theorem source_actualCRegisterWriteAt_entry_range
    (sailTrace : SailTrace (sourceEnd L)) (cut : Fin m)
    (inputs : ∀ i : Fin m, i.val < cut.val →
      InputsAgreeCore trace sailTrace (physicalStart L i) (steps i))
    (outside : ∀ i : Fin m, i.val < cut.val →
      RowOutsideDefectRegion trace (physicalStart L i) (steps i))
    (memoryPresent : ∀ i : Fin m, i.val < cut.val →
      ZiskStepLoadMemoryRows trace (physicalStart L i) (steps i) →
        MutableMemPresent trace.witness)
    (row : Fin (sourceEnd L)) (before : row.val < (physicalStart L cut).val)
    (entry : Interaction.MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace
      ⟨row.val, trace.mainTable_index row⟩ = some entry)
    (nonzero : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range entry := by
  obtain ⟨i, producer, realWrite⟩ := source_actualCRegisterWriteAt_is_real_step
    rawProgram selected L trace start addr binding steps rawDecodes atPc row entry written
  have sourceBefore : i.val < cut.val := by
    by_contra notBefore
    have monotone : sourceStart L cut ≤ sourceStart L i :=
      prefix_mono (sourceWidth L) (Nat.le_of_not_gt notBefore)
    have placement := ExecutionSpanLegacy.producer_eq_index_or_succ
      (physicalStart L i) (steps i) (D i)
    change stepProducerRow (physicalStart L i) (steps i) (D i) = sourceStart L i ∨
      stepProducerRow (physicalStart L i) (steps i) (D i) = sourceStart L i + 1 at placement
    simp only [physicalStart_val] at before placement
    dsimp only at producer placement
    rcases placement with first | second <;> omega
  exact PhysicalRegisterWriteRanges.real_stepRegWrite_entry_range
    (physicalStart L i) (steps i) (D i) (inputs i sourceBefore)
    (outside i sourceBefore) (memoryPresent i sourceBefore) realWrite nonzero

end Source
end ZiskFv.Compliance.SerializedExecutionRows
