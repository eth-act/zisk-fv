import ZiskFv.Compliance.TraceLevelExport.AuxiliaryReplayNeutrality
import ZiskFv.Compliance.TraceLevelExport.MappedRegisterInvariant

set_option maxRecDepth 10000

/-!
# Actual physical C-register replay

The fold below visits the real finite Main prefix. Source serialization makes
its C selectors exclusive; decode and accepted address placement identify its
terminal write with the architectural channel write away from x0. Expanded
first rows are inactive requests, not synthetic architectural instructions.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Air.Flat
open CanonicalExecutionRows
open Goldilocks Interaction
open RawProgramBinding
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.Channels.MemoryBus

/-- The action of the actual C request at one in-range physical Main row. -/
noncomputable def actualCRegisterAction {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length)
    (regs : Fin 32 → BitVec 64) (k : Fin 32) : BitVec 64 :=
  match actualCRegisterWriteAt trace row with
  | some e => if Transpiler.wrap_to_regidx e.ptr = k then entryRegValue e else regs k
  | none => regs k

theorem actualCRegisterAction_of_none {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length)
    (none : actualCRegisterWriteAt trace row = Option.none)
    (regs : Fin 32 → BitVec 64) : actualCRegisterAction trace row regs = regs := by
  funext k
  unfold actualCRegisterAction
  rw [none]

private theorem actualCRegisterAction_congr {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) (a b : Fin 32 → BitVec 64)
    (k : Fin 32) (same : a k = b k) :
    actualCRegisterAction trace row a k = actualCRegisterAction trace row b k := by
  unfold actualCRegisterAction
  cases actualCRegisterWriteAt trace row <;> simp [same]

private theorem cRequestEvalMult
    (env : Environment FGL) (v : Var MainRowWithRom FGL) :
    (((MemBusChannel.emitted
      (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg))
      (cMemMessageExpr v)).toRaw).eval env).mult =
      -((eval env v).rom.store_mem + (eval env v).rom.store_ind +
        (eval env v).rom.store_reg) := by
  change Expression.eval env
    (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg)) = _
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  ring

private theorem cRequestMult {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) :
    (mainCMemInteractionAt trace row).mult =
      -((mainRowWithRomAt trace row).rom.store_mem +
        (mainRowWithRomAt trace row).rom.store_ind +
        (mainRowWithRomAt trace row).rom.store_reg) := by
  rw [mainCMemInteractionAt, cRequestEvalMult,
    ← ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
      trace.program trace.mainTable row]

/-- The three store flags are decoded from ONE source enum. In particular,
register writes cannot coexist with a mutable-memory store selector. This
uses full serialized ROM agreement, not an additional selector promise. -/
private theorem actualCRegisterWriteAt_of_serialized_flags {n : Nat}
    (trace : AcceptedZiskTrace n) (row : Fin trace.mainTable.table.length)
    (source : zisk_core.aeneas_extract.ZiskInstExtract)
    (flags : romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val) =
      packFlags (romFlagBitsOfExtract source)) :
    actualCRegisterWriteAt trace row =
      if (mainRowWithRomAt trace row).rom.store_reg = 1 then
        some ((cMemMessage (mainRowWithRomAt trace row)).toEntry 1 1)
      else none := by
  obtain ⟨_, sm, si, _, _, sr⟩ :=
    RomDecodeBinding.mainMemorySelectorColumns_of_packFlags_at trace row _ flags
  change (mainRowWithRomAt trace row).rom.store_mem = _ at sm
  change (mainRowWithRomAt trace row).rom.store_ind = _ at si
  change (mainRowWithRomAt trace row).rom.store_reg = _ at sr
  rw [actualCRegisterWriteAt, cRequestMult]
  by_cases hm : source.store = zisk_core.zisk_inst.STORE_MEM <;>
    by_cases hi : source.store = zisk_core.zisk_inst.STORE_IND <;>
    by_cases hr : source.store = zisk_core.zisk_inst.STORE_REG <;>
    simp_all [sm, si, sr, cMemMessage, romFlagBitsOfExtract,
      ZiskFv.AirsClean.boolF, zisk_core.zisk_inst.STORE_MEM,
      zisk_core.zisk_inst.STORE_IND, zisk_core.zisk_inst.STORE_REG]

private theorem stepWrite_none_or_actualC {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (step : ZiskStep trace i) (decoded : RowDecode trace i step) :
    stepRegWrite (stepChannelOutput i step decoded) = none ∨
      stepRegWrite (stepChannelOutput i step decoded) =
        some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable
          (stepProducerRow i step decoded))).toEntry 1 1) := by
  cases step <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem no_stepWrite_storeReg_zero {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (step : ZiskStep trace i) (decoded : RowDecode trace i step)
    (none : stepRegWrite (stepChannelOutput i step decoded) = Option.none) :
    (mainTableRowAtOrZero trace.program trace.mainTable
      (stepProducerRow i step decoded)).rom.store_reg = 0 := by
  cases step <;> first | exact decoded.h_store_reg | exact nomatch none

/-- The address equation is essential here: a suppressed source write has a
zero destination, even though the architectural bus shape retains its entry. -/
private theorem nonzero_stepWrite_storeReg_one {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (step : ZiskStep trace i) (decoded : RowDecode trace i step)
    (e : MemoryBusEntry FGL)
    (write : stepRegWrite (stepChannelOutput i step decoded) = some e)
    (nonzero : Transpiler.wrap_to_regidx e.ptr ≠ 0) :
    (mainTableRowAtOrZero trace.program trace.mainTable
      (stepProducerRow i step decoded)).rom.store_reg = 1 := by
  have address := RomDecodeBinding.mainAddressSpec_at trace
    ⟨stepProducerRow i step decoded,
      Nat.lt_of_succ_lt (ExecutionSpanLegacy.producer_has_successor i step decoded)⟩
  cases step with
  | beq c => exact nomatch write
  | bne c => exact nomatch write
  | blt c => exact nomatch write
  | bge c => exact nomatch write
  | bltu c => exact nomatch write
  | bgeu c => exact nomatch write
  | sb c => exact nomatch write
  | sh c => exact nomatch write
  | sw c => exact nomatch write
  | sd c => exact nomatch write
  | fence c => exact nomatch write
  | jalr c =>
    change (mainRowWithRomAt trace decoded.rows.finish).rom.store_reg = 1
    rw [decoded.h_store_reg]
    suffices hn : (regidx_to_fin c.rd : Fin 32) ≠ 0 by simp [hn, Fin.ext_iff]
    intro hz
    apply nonzero
    have he := Option.some.inj write
    rw [show e.ptr = (eRdAt trace decoded.rows.finish).ptr from
      congrArg (·.ptr) he.symm]
    have off : (mainRowWithRomAt trace decoded.rows.finish).rom.store_offset =
        Transpiler.ind (regidx_to_fin c.rd) := by
      rw [decoded.h_store_offset, hz]
      simp [Transpiler.ind]
    rw [← eRdAt_rd_idx_of_decode decoded.h_store_ind off, hz]
  | _ =>
    simp only [stepProducerRow] at address ⊢
    rw [decoded.h_store_reg]
    have addr := address.2.2.1
    rw [decoded.h_store_ind, decoded.h_store_offset] at addr
    simp at addr
    have he := Option.some.inj write
    rw [show e.ptr = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.addr2
      from congrArg (·.ptr) he.symm] at nonzero
    rw [addr, Transpiler.wrap_to_regidx_ind] at nonzero
    try simp only [Transpiler.regidxOfBitVec5, ne_eq, Fin.ext_iff, Fin.val_zero] at nonzero
    simp [ZiskFv.AirsClean.boolF, Fin.ext_iff, nonzero, Transpiler.regidxOfBitVec5]

/-- The physical recurrence has no step, output, or fallback outside its finite
accepted Main domain. Auxiliary rows are visited just like all other rows. -/
noncomputable def actualPhysicalRegFile {n : Nat} (trace : AcceptedZiskTrace n)
    (p : Nat) (_h : p ≤ n) : Fin 32 → BitVec 64 :=
  ((List.finRange n).take p).foldl
    (fun regs row => actualCRegisterAction trace
      ⟨row.val, trace.mainTable_index row⟩ regs) (fun _ => 0)

@[simp] theorem actualPhysicalRegFile_zero {n : Nat} (trace : AcceptedZiskTrace n)
    (h : 0 ≤ n) : actualPhysicalRegFile trace 0 h = fun _ => 0 := by
  simp [actualPhysicalRegFile]

theorem actualPhysicalRegFile_succ {n : Nat} (trace : AcceptedZiskTrace n)
    (p : Fin n) :
    actualPhysicalRegFile trace (p.val + 1) (Nat.succ_le_of_lt p.isLt) =
      actualCRegisterAction trace ⟨p.val, trace.mainTable_index p⟩
        (actualPhysicalRegFile trace p.val (Nat.le_of_lt p.isLt)) := by
  simp only [actualPhysicalRegFile, finitePrefix_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

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

include binding atPc

/-- Source-producer correspondence places this actual C request at the terminal
physical slot. The conclusion excludes precisely the original RegAgree x0. -/
theorem source_terminal_actualCRegisterAction (i : Fin m)
    (regs : Fin 32 → BitVec 64) (k : Fin 32) (hk : k ≠ 0) :
    actualCRegisterAction trace
      ⟨stepProducerRow (physicalStart L i) (steps i) (D i),
        Nat.lt_of_succ_lt (ExecutionSpanLegacy.producer_has_successor
          (physicalStart L i) (steps i) (D i))⟩ regs k =
      mappedRegWriteAction
        (stepChannelOutput (physicalStart L i) (steps i) (D i)) regs k := by
  have stop := mapped_producer_successor_eq_source_stop rawProgram selected L trace
    start addr binding steps rawDecodes atPc i
  have positive := (L i).width_pos
  let offset : Fin (L i).width := ⟨(L i).width - 1, by omega⟩
  have span := main_full_serialized_span trace start addr rawProgram binding
    (selected i) (L i)
    ⟨(physicalStart L i).val, trace.mainTable_index (physicalStart L i)⟩
    (canonical_span_room rawProgram selected L trace i) (atPc i) offset
  have terminal : (physicalStart L i).val + offset.val =
      stepProducerRow (physicalStart L i) (steps i) (D i) := by
    change sourceStart L i + offset.val = _
    simp only [physicalStart_val] at stop
    dsimp [offset]
    omega
  rw [terminal] at span
  have flags := congrArg ZiskFv.Channels.ZiskRomBus.ZiskRomMessage.flags span
  let row : Fin trace.mainTable.table.length :=
    ⟨stepProducerRow (physicalStart L i) (steps i) (D i),
      Nat.lt_of_succ_lt (ExecutionSpanLegacy.producer_has_successor
        (physicalStart L i) (steps i) (D i))⟩
  have classify := actualCRegisterWriteAt_of_serialized_flags trace row _ flags
  have rowEq : mainRowWithRomAt trace row =
      mainTableRowAtOrZero trace.program trace.mainTable row.val := rfl
  rw [rowEq] at classify
  change actualCRegisterAction trace row regs k = _
  unfold actualCRegisterAction mappedRegWriteAction
  rw [classify]
  rcases stepWrite_none_or_actualC (physicalStart L i) (steps i) (D i) with hn | hs
  · have zero := no_stepWrite_storeReg_zero (physicalStart L i) (steps i) (D i) hn
    simp [hn, row, zero]
  · rw [hs]
    by_cases active : (mainTableRowAtOrZero trace.program trace.mainTable row.val).rom.store_reg = 1
    · simp [active, row]
    · have zero : Transpiler.wrap_to_regidx
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable row.val)).toEntry 1 1).ptr = 0 := by
        by_contra nz
        exact active (nonzero_stepWrite_storeReg_one (physicalStart L i)
          (steps i) (D i) _ hs nz)
      change Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable row.val).rom.addr2 = 0 at zero
      dsimp only [row] at active zero ⊢
      simp [active, zero, Ne.symm hk]

/-- The expanded first request is genuinely inactive, including its RAW
multiplicity; no phantom entry or auxiliary Sail instruction is introduced. -/
theorem source_first_actualCRegisterWriteAt_none (i : Fin m)
    (two : (L i).width = 2) :
    actualCRegisterWriteAt trace
      ⟨(physicalStart L i).val, trace.mainTable_index (physicalStart L i)⟩ = none := by
  obtain ⟨rd, rs1⟩ := expanded_source_register_bounds (L i) two
  exact actualCRegisterWriteAt_of_mult_zero trace _
    (expanded_main_first_cMemInteraction_mult_zero trace start addr rawProgram binding
      (selected i) (L i) two rd rs1 _ (atPc i))

/-- Every architectural cut is the actual physical prefix, not a fold over an
arbitrary supplied write family. Prefix induction includes the empty execution. -/
theorem mappedZiskRegFile_eq_actualPhysicalRegFile (j : Nat) (h : j ≤ m)
    (k : Fin 32) (hk : k ≠ 0) :
    mappedZiskRegFile L steps D j h k =
      actualPhysicalRegFile trace (rowPrefix (sourceWidth L) j)
        (prefix_mono (sourceWidth L) h) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : j < m := by omega
    let i : Fin m := ⟨j, hj⟩
    have stop := mapped_producer_successor_eq_source_stop rawProgram selected L trace
      start addr binding steps rawDecodes atPc i
    simp only [physicalStart_val] at stop
    have cutSucc := prefix_succ (sourceWidth L) i
    have endBound := sourceSpanStop_le_sourceEnd L i
    change rowPrefix (sourceWidth L) (j + 1) =
      sourceStart L i + (L i).width at cutSucc
    have terminal := source_terminal_actualCRegisterAction rawProgram selected L trace
      start addr binding steps rawDecodes atPc i
    change mappedZiskRegFile L steps D (i.val + 1) h k = _
    rw [mappedZiskRegFile_succ]
    simp only [cutSucc]
    rcases (L i).count with one | two
    · change (L i).width = 1 at one
      have room : sourceStart L i < sourceEnd L := sourceStart_lt_sourceEnd L i
      have producer : stepProducerRow (physicalStart L i) (steps i) (D i) =
          sourceStart L i := by
        exact Nat.add_right_cancel (by simpa only [one] using stop)
      simp only [one]
      rw [actualPhysicalRegFile_succ trace ⟨sourceStart L i, room⟩]
      simp only [producer] at terminal
      rw [← terminal (mappedZiskRegFile L steps D i.val (Nat.le_of_lt i.isLt)) k hk]
      apply actualCRegisterAction_congr
      exact ih (Nat.le_of_lt hj)
    · change (L i).width = 2 at two
      have room : sourceStart L i + 1 < sourceEnd L := by
        omega
      have producer : stepProducerRow (physicalStart L i) (steps i) (D i) =
          sourceStart L i + 1 := by
        exact Nat.add_right_cancel (by simpa only [two] using stop)
      simp only [producer] at terminal
      have neutral := source_first_actualCRegisterWriteAt_none rawProgram selected L trace
        start addr binding atPc i two
      have firstSucc := actualPhysicalRegFile_succ trace (physicalStart L i)
      simp only [physicalStart_val] at firstSucc neutral
      simp only [two]
      rw [actualPhysicalRegFile_succ trace ⟨sourceStart L i + 1, room⟩,
        firstSucc,
        actualCRegisterAction_of_none trace _ neutral]
      rw [← terminal (mappedZiskRegFile L steps D i.val (Nat.le_of_lt i.isLt)) k hk]
      apply actualCRegisterAction_congr
      exact ih (Nat.le_of_lt hj)

omit binding atPc in
private theorem mappedRegPrefix_eq_take (j : Nat) (h : j ≤ m) :
    mappedRegPrefix j h = (List.finRange m).take j := by
  induction j with
  | zero => simp [mappedRegPrefix]
  | succ j ih =>
    have hj : j < m := by omega
    rw [mappedRegPrefix, ih, finitePrefix_succ (⟨j, hj⟩ : Fin m)]

/-- The same physical prefix is the source spine's ordered flatten, with empty
auxiliary slots. This is an action equality away from x0, not equality of
phantom architectural entries at x0. -/
theorem actualPhysicalRegFile_eq_sourcePhysicalPrefix_fold
    (j : Nat) (h : j ≤ m) (k : Fin 32) (hk : k ≠ 0) :
    actualPhysicalRegFile trace (rowPrefix (sourceWidth L) j)
        (prefix_mono (sourceWidth L) h) k =
      ((sourcePhysicalPrefix L (fun i => [i]) j h).flatten.foldl
        (fun regs i => mappedRegWriteAction
          (stepChannelOutput (physicalStart L i) (steps i) (D i)) regs)
        (fun _ => 0)) k := by
  rw [← mappedZiskRegFile_eq_actualPhysicalRegFile rawProgram selected L trace
    start addr binding steps rawDecodes atPc j h k hk,
    mappedZiskRegFile_eq_fold, mappedRegPrefix_eq_take,
    sourcePhysicalPrefix_flatten]
  simp

/-- Transport the existing Sail register invariant to the actual physical Main
cut. The only excluded register is exactly x0 from the original RegAgree. -/
theorem mappedRegAgree_actualPhysical_prefix
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (j : Nat) (h : j ≤ m)
    (sounds : ∀ i : Fin m, i.val < j →
      StepSound trace (mappedSailTrace L steps init)
        (physicalStart L i) (steps i) (D i)) :
    ∀ k : Fin 32, k ≠ 0 →
      (mappedSailStates L steps init j h).regs.get? (reg_of_fin k) =
        some (cast (by rw [register_type_reg_of_fin_equiv])
          (actualPhysicalRegFile trace (rowPrefix (sourceWidth L) j)
            (prefix_mono (sourceWidth L) h) k)) := by
  intro k hk
  rw [← mappedZiskRegFile_eq_actualPhysicalRegFile rawProgram selected L trace
    start addr binding steps rawDecodes atPc j h k hk]
  exact mappedRegAgree_prefix L steps D init regBoot j h sounds k hk

end Source
end ZiskFv.Compliance.SerializedExecutionRows
