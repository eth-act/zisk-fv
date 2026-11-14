import ZiskFv.Compliance.TraceLevelExport.SerializedSourceBounds
import ZiskFv.Compliance.TraceLevelExport.SerializedSpanSelectors
import ZiskFv.Compliance.TraceLevelExport.MappedSourceSailChain

/-!
# Actual serialized Main spans and canonical physical coverage

The generic span statements use arbitrary physical Main rows and actual source
widths; they do not impose old architectural starts=i. Old-domain comparison
is separately named and consumes exactly the existing raw-decode/binding facts.
No root interface or memory-seed field is changed by these internal proofs.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.AirsClean.Main (romMessage)

/-- The existing decode's actual successor witness gives room for its entire
source-sized physical span; this is not an extra Main-height premise. -/
theorem old_decode_span_room {n : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (step : ZiskStep trace i)
    (decoded : RowDecode trace i step) :
    i.val + (stepProducerRow i step decoded + 1 - i.val) <
      trace.mainTable.table.length := by
  have placement := ExecutionSpanLegacy.producer_eq_index_or_succ i step decoded
  have successor := ExecutionSpanLegacy.producer_has_successor i step decoded
  omega

/-- The all63-arm old raw-decode comparison now feeds the actual Main/ROM
binding, not an unused source certificate or import. -/
theorem old_raw_source_first_rom {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i step start addr rawProgram) :
    ∃ k : Fin rawLength, ∃ lowering : SuccessfulRowLowering (rawProgram k),
      addr k = (mainOfTable trace.program trace.mainTable).pc i.val ∧
      lowering.width = stepProducerRow i step (rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i step start addr rawProgram
          binding rawDecode)) + 1 - i.val ∧
      romMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val) =
        romRowOf (addr k) lowering.rows.first_row := by
  obtain ⟨k, atPc, lowering, width⟩ := RawDecodeRowLowering.sourceWidth_of_rawProgramDecode
    trace i step start addr rawProgram binding rawDecode
  exact ⟨k, lowering, atPc, width, main_first_rom trace start addr rawProgram binding
    k lowering ⟨i.val, trace.mainTable_index i⟩ atPc.symm⟩

/-- The real first-row selectors and accepted physical PC recurrence advance
to the auxiliary address. The source decoder bounds are derived internally. -/
theorem expanded_pc_successor {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2) (row : Fin trace.mainTable.table.length)
    (successor : row.val + 1 < trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (mainOfTable trace.program trace.mainTable).pc (row.val + 1) = addr k + 1 := by
  obtain ⟨hrd, hrs1⟩ := expanded_source_register_bounds lowering widthTwo
  obtain ⟨setpc, _, jump⟩ := expanded_main_first_core trace start addr rawProgram
    binding k lowering widthTwo hrd hrs1 row atPc
  rw [mainOfTable_pc_succ_eq_nextPcMux row.val successor]
  simp only [nextPcMux, setpc, zero_mul, sub_zero, one_mul, zero_add, jump, atPc]

/-- Every actual physical member of a width-one/two span equals the complete
source row. Arbitrary physical starts are allowed, including nonfinal width2.
Room is a real table bound, derived from old decode in the comparison below. -/
theorem main_full_serialized_span {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (row : Fin trace.mainTable.table.length)
    (room : row.val + lowering.width ≤ trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    ∀ offset : Fin lowering.width,
      romMessage (mainTableRowAtOrZero trace.program trace.mainTable
        (row.val + offset.val)) =
      romRowOf (addr k + (offset.val : FGL))
        (if offset.val = 0 then lowering.rows.first_row else lowering.rows.last_row) := by
  intro offset
  by_cases zero : offset.val = 0
  · simpa only [zero, Nat.add_zero, Nat.cast_zero, add_zero, if_true] using
      main_first_rom trace start addr rawProgram binding k lowering row atPc
  · have widthTwo : lowering.width = 2 := by
      rcases lowering.count with one | two
      · have bound := offset.isLt
        omega
      · exact two
    have one : offset.val = 1 := by
      have bound := offset.isLt
      omega
    have successor : row.val + 1 < trace.mainTable.table.length := by omega
    have auxPc := expanded_pc_successor trace start addr rawProgram binding k lowering
      widthTwo row successor atPc
    have terminal := main_terminal_rom_of_auxiliary_pc trace start addr rawProgram binding
      k lowering widthTwo ⟨row.val + 1, successor⟩ auxPc
    simpa only [one, Nat.cast_one, if_false, Nat.one_ne_zero] using terminal

/-- Same-world old raw evidence supplies the actual entire serialized span;
neither source success nor physical room is added to the root caller. -/
theorem old_raw_full_serialized_span {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i step start addr rawProgram) :
    ∃ k : Fin rawLength, ∃ lowering : SuccessfulRowLowering (rawProgram k),
      addr k = (mainOfTable trace.program trace.mainTable).pc i.val ∧
      lowering.width = stepProducerRow i step (rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i step start addr rawProgram
          binding rawDecode)) + 1 - i.val ∧
      ∀ offset : Fin lowering.width,
        romMessage (mainTableRowAtOrZero trace.program trace.mainTable
          (i.val + offset.val)) =
        romRowOf (addr k + (offset.val : FGL))
          (if offset.val = 0 then lowering.rows.first_row else lowering.rows.last_row) := by
  obtain ⟨k, atPc, lowering, width⟩ := RawDecodeRowLowering.sourceWidth_of_rawProgramDecode
    trace i step start addr rawProgram binding rawDecode
  refine ⟨k, lowering, atPc, width, ?_⟩
  apply main_full_serialized_span trace start addr rawProgram binding k lowering
    ⟨i.val, trace.mainTable_index i⟩
  · have covered := old_decode_span_room trace i step (rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i step start addr rawProgram binding rawDecode))
    rw [width]
    omega
  · exact atPc.symm

section CanonicalCoverage

open CanonicalExecutionRows

variable {m rawLength : Nat}
variable (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
variable (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
variable (trace : AcceptedZiskTrace (sourceEnd L))
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (binding : ProgramRowsBinding trace start addr rawProgram)

/-- Accepted physical-prefix coverage is sufficient for every source span.
It is obtained from the existing accepted Main index bound, including q=0. -/
theorem canonical_span_room (i : Fin m) :
    (physicalStart L i).val + (L i).width ≤ trace.mainTable.table.length := by
  have stop := prefix_succ (sourceWidth L) i
  have endBound := prefix_mono (sourceWidth L) (Nat.succ_le_of_lt i.isLt)
  have height : sourceEnd L ≤ trace.mainTable.table.length := by
    by_cases empty : sourceEnd L = 0
    · omega
    · have index := trace.mainTable_index
        ⟨sourceEnd L - 1, by omega⟩
      omega
  change rowPrefix (sourceWidth L) (i.val + 1) =
    sourceStart L i + (L i).width at stop
  change rowPrefix (sourceWidth L) (i.val + 1) ≤ sourceEnd L at endBound
  change sourceStart L i + (L i).width ≤ trace.mainTable.table.length
  omega

/-- Whole-prefix source consumption at the actual interval-derived owner.
The PC selections are ordinary selected-word facts, not an independent row map.
There is no old starts=i/StepRowsAligned restriction in this new coverage. -/
theorem canonical_main_serialized_prefix
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i))
    (row : Fin (sourceEnd L)) :
    let i := physicalOwner L row
    let offset := row.val - sourceStart L i
    romMessage (mainTableRowAtOrZero trace.program trace.mainTable row.val) =
      romRowOf (addr (selected i) + (offset : FGL))
        (if offset = 0 then (L i).rows.first_row else (L i).rows.last_row) := by
  let i := physicalOwner L row
  have owner := physicalOwner_spec L row
  have deltaBound : row.val - sourceStart L i < (L i).width := by omega
  let delta : Fin (L i).width := ⟨row.val - sourceStart L i, deltaBound⟩
  have span := main_full_serialized_span trace start addr rawProgram binding
    (selected i) (L i)
    ⟨(physicalStart L i).val, trace.mainTable_index (physicalStart L i)⟩
    (canonical_span_room rawProgram selected L trace i) (atPc i) delta
  simpa only [physicalStart_val, delta, Nat.add_sub_of_le owner.1] using span

/-- Width agreement and producer/next-source placement are DERIVED from the
existing raw-decode facts at each source-selected physical start. -/
theorem mapped_producer_successor_eq_source_stop
    (steps : ∀ i, ZiskStep trace (physicalStart L i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
      start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i)) (i : Fin m) :
    stepProducerRow (physicalStart L i) (steps i)
      (rowDecode_of_programDecode trace (physicalStart L i)
        (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
          start addr rawProgram binding (rawDecodes i))) + 1 =
      (physicalStart L i).val + (L i).width := by
  have width := source_width_at_selected_pc trace (physicalStart L i) (steps i)
    start addr rawProgram binding (rawDecodes i) (selected i) (L i) (atPc i)
  have placement := ExecutionSpanLegacy.producer_eq_index_or_succ (physicalStart L i)
    (steps i) (rowDecode_of_programDecode trace (physicalStart L i)
      (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
        start addr rawProgram binding (rawDecodes i)))
  omega

/-- Actual mapped architectural retire reaches the next deterministic source
start, even when the preceding instruction occupies two physical rows.
No producer-next-start oracle or old StepRowsAligned premise is used. -/
theorem mapped_pc_at_next_source_start
    (steps : ∀ i, ZiskStep trace (physicalStart L i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
      start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i j : Fin m) (next : j.val = i.val + 1)
    (sound : StepSound trace (mappedSailTrace L steps init) (physicalStart L i) (steps i)
      (rowDecode_of_programDecode trace (physicalStart L i)
        (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
          start addr rawProgram binding (rawDecodes i)))) :
    (mappedSailTrace L steps init (physicalStart L j)).regs.get? Register.PC =
      some (register_type_pc_equiv ▸ BitVec.ofNat 64
        ((mainOfTable trace.program trace.mainTable).pc (physicalStart L j).val).val) := by
  have stop := mapped_producer_successor_eq_source_stop rawProgram selected L trace
    start addr binding steps rawDecodes atPc i
  have consecutive := source_successor L i j next
  have joined : stepProducerRow (physicalStart L i) (steps i)
      (rowDecode_of_programDecode trace (physicalStart L i)
        (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
          start addr rawProgram binding (rawDecodes i))) + 1 =
        (physicalStart L j).val := by
    simpa only [physicalStart_val, consecutive] using stop
  have pc := mappedSailTrace_pc_of_stepSound L steps init i j next
    (rowDecode_of_programDecode trace (physicalStart L i)
      (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
        start addr rawProgram binding (rawDecodes i))) sound
  rw [joined] at pc
  exact pc

end CanonicalCoverage

end ZiskFv.Compliance.SerializedExecutionRows
