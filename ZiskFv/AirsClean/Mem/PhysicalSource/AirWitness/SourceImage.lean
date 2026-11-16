import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.Data
import ZiskFv.AirsClean.Mem.PhysicalSource.CompleteConstructibility

/-! One chosen UNPACKED source image as a supplemental satisfiability witness,
not an exclusion of packed/GPU/native production inputs. Existing both-mode
representation constructors are unchanged. Original primary/auxiliary/fixed
buffers are allocated once; there is no decoded full-row map or free data
function supplied by a caller. Full AIR satisfaction is proved separately. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native

/-- Original UInt64 storage producer for the explicit thirteen-cell witness.
This is NOT an alternate decoder; canonical logical reads still use the sole
shared NativeTraceCells implementation. -/
def traceWord (index : Nat) : UInt64 :=
  if index % 13 = 0 then UInt64.ofNat address.val
  else if index % 13 = 3 then (if index / 13 = 0 then 1 else 0)
  else if index % 13 = 12 then (if index / 13 = 0 then 0 else 1)
  else 0

def traceBuffer : Array UInt64 := Array.ofFn fun index : Fin (13 * N + 5) =>
  if index.val < 13 * N then traceWord index.val else 37

/-- Exact arithmetic-progression gsum and explicit inverse cluster in the
original auxiliary buffer, with its thirteen-N prefix retained. -/
def auxiliaryWord (index : Nat) : FGL :=
  if index < 13 * N then 0
  else if (index - 13 * N) % 9 = 0 then
    (((index - 13 * N) / 9 + 1 : Nat) : FGL) * delta
  else if (index - 13 * N) % 9 = 3 then cluster
  else 0

def auxiliaryBuffer : Array FGL := Array.ofFn fun index : Fin (22 * N) =>
  auxiliaryWord index.val

def airBuffer : Array FGL := Array.ofFn fun index : Fin 33 =>
  if before : index.val < 15 then baseAir[index.val]
  else (direct ⟨(index.val - 15) / 3, by omega⟩).coeff ⟨(index.val - 15) % 3, by omega⟩

def groupBuffer : Array FGL := #[groupResult.c0, groupResult.c1, groupResult.c2]

def slot : Instance FGL :=
  { Constructibility.slot false with
    trace := traceBuffer,
    auxTrace := auxiliaryBuffer,
    airvalues := airBuffer,
    airgroupValues := groupBuffer }

def source : SourceObject FGL :=
  { Constructibility.source false with slots := #[slot] }

def occurrence : ResolvedOccurrence source :=
  ⟨⟨0, by change 0 < 1; decide⟩, by change 0 < 1; decide⟩

theorem actual_slot : occurrence.slotData = slot := rfl

theorem actual_setup : occurrence.setup? = some Constructibility.setup := by
  simp [occurrence, ResolvedOccurrence.setup?, SourceObject.setupAt?,
    SourceObject.registryEntry, source, Constructibility.source]

theorem traceBuffer_size : traceBuffer.size = 13 * N + 5 := by
  simp only [traceBuffer, Array.size_ofFn]

theorem auxiliaryBuffer_size : auxiliaryBuffer.size = 22 * N := by
  simp only [auxiliaryBuffer, Array.size_ofFn]

theorem airBuffer_size : airBuffer.size = 33 := by
  simp only [airBuffer, Array.size_ofFn]

theorem slot_trace : slot.trace = traceBuffer := by dsimp only [slot]
theorem slot_auxiliary : slot.auxTrace = auxiliaryBuffer := by dsimp only [slot]
theorem slot_fixed : slot.fixed = Constructibility.fixedBuffer := by
  dsimp only [slot]
  exact Constructibility.slot_fixed false

theorem params_trace : (occurrence.params false).trace = traceBuffer := by
  dsimp only [ResolvedOccurrence.params, paramsOf]
  rw [actual_slot, slot_trace]
theorem params_air : (occurrence.params false).airvalues = airBuffer := by
  dsimp only [ResolvedOccurrence.params, paramsOf]
  rw [actual_slot]
  dsimp only [slot]
theorem params_group : (occurrence.params false).airgroupValues = groupBuffer := by
  dsimp only [ResolvedOccurrence.params, paramsOf]
  rw [actual_slot]
  dsimp only [slot]
theorem params_challenges : (occurrence.params false).challenges = #[0, 0, 0, 1, 0, 0] := rfl

theorem actual_auxiliary : occurrence.slotData.auxTrace = auxiliaryBuffer := by
  rw [actual_slot, slot_auxiliary]

theorem trace_original_suffix (index : Fin 5) :
    traceBuffer[13 * N + index.val]'(by rw [traceBuffer_size]; omega) = 37 := by
  simp [traceBuffer, Array.getElem_ofFn]

theorem trace_coordinate (row : Index) (column : Fin 13) :
    traceBuffer[13 * row.val + column.val]'(by
      rw [traceBuffer_size]
      have bound : row.val < N := row.isLt
      omega) = UInt64.ofNat ((primary row)[column]).val := by
  have bound : row.val < N := row.isLt
  have col := column.isLt
  have within : 13 * row.val + column.val < 13 * N := by omega
  have quotient : (13 * row.val + column.val) / 13 = row.val := by omega
  have remainder : (13 * row.val + column.val) % 13 = column.val := by omega
  simp only [traceBuffer, Array.getElem_ofFn, if_pos within, traceWord, quotient, remainder]
  by_cases first : row.val = 0 <;> fin_cases column <;>
    simp [primary, firstFlag, first, address]

theorem auxiliary_coordinate (row : Index) (column coordinate : Fin 3) :
    auxiliaryBuffer[13 * N + 9 * row.val + 3 * column.val + coordinate.val]'(by
      rw [auxiliaryBuffer_size]
      have bound : row.val < N := row.isLt
      have col := column.isLt
      have coord := coordinate.isLt
      omega) = (extensionWitness row column).coeff coordinate := by
  have bound : row.val < N := row.isLt
  have col := column.isLt
  have coord := coordinate.isLt
  have quotient : (9 * row.val + 3 * column.val + coordinate.val) / 9 = row.val := by omega
  have remainder : (9 * row.val + 3 * column.val + coordinate.val) % 9 =
      3 * column.val + coordinate.val := by omega
  have after : ¬13 * N + 9 * row.val + 3 * column.val + coordinate.val < 13 * N := by omega
  have subtract : 13 * N + 9 * row.val + 3 * column.val + coordinate.val - 13 * N =
      9 * row.val + 3 * column.val + coordinate.val := by omega
  simp only [auxiliaryBuffer, Array.getElem_ofFn, auxiliaryWord, if_neg after,
    subtract, quotient, remainder]
  fin_cases column <;> fin_cases coordinate <;>
    simp [extensionWitness, running, Stage2.Ext3.ofBase]
  all_goals rfl

theorem group_selected : NativeValuesLayout.groupWords? .mem (occurrence.params false) =
    some #v[groupResult.c0, groupResult.c1, groupResult.c2] := by
  rw [NativeValuesLayout.group_reads_actual_buffer]
  rfl

theorem directs_selected : directBatch? occurrence = some
    #v[#v[(direct 0).c0, (direct 0).c1, (direct 0).c2],
       #v[(direct 1).c0, (direct 1).c1, (direct 1).c2],
       #v[(direct 2).c0, (direct 2).c1, (direct 2).c2],
       #v[(direct 3).c0, (direct 3).c1, (direct 3).c2],
       #v[(direct 4).c0, (direct 4).c1, (direct 4).c2],
       #v[(direct 5).c0, (direct 5).c1, (direct 5).c2]] := by
  simp [directBatch?, NativeValuesLayout.mem_inverse_reads_actual_buffer,
    params_air, airBuffer, Stage2.Ext3.coeff, direct]

/-- Actual physical constructor, not a caller-provided count or holds oracle. -/
theorem base_nonvacuous : (fromResolved? occurrence).isSome = true := by
  unfold fromResolved?
  split
  · rename_i absent
    simp [actual_setup] at absent
  · rename_i selectedSetup selected
    have equal := Option.some.inj (selected.symm.trans actual_setup)
    subst selectedSetup
    split
    · rename_i absent
      simp [Constructibility.exact_cm1] at absent
    · rename_i selectedCm1 selected
      have equal := Option.some.inj (selected.symm.trans Constructibility.exact_cm1)
      subst selectedCm1
      split_ifs with checked
      · split
        · rename_i absent
          simp [group_selected] at absent
        · split
          · rename_i absent
            simp [directs_selected] at absent
          · rfl
      · apply False.elim
        apply checked
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, ?_, rfl, ?_, ?_⟩
        · rw [actual_slot, slot_trace, traceBuffer_size]
          change N * 13 ≤ 13 * N + 5
          omega
        · rw [actual_slot, slot_fixed, Constructibility.fixedBuffer_size]
          rfl
        · rw [actual_slot, slot_fixed, Constructibility.fixedBuffer_scan]

private theorem challenge0_map : Constructibility.setup.challengesMap.findIdx?
    (fun entry => entry.stage == 2 && entry.stageId == 0 && entry.dim == 3) = some 0 := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  omega

private theorem challenge1_map : Constructibility.setup.challengesMap.findIdx?
    (fun entry => entry.stage == 2 && entry.stageId == 1 && entry.dim == 3) = some 1 := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  interval_cases index <;> decide +revert

theorem actual_alpha : Stage2.challenge? occurrence 2 0 = some alpha := by
  unfold Stage2.challenge?
  rw [if_pos (by decide : 2 = 2 ∧ (0 : Nat) < 2)]
  simp only [actual_setup, bind, Option.bind_some, challenge0_map]
  rfl

theorem actual_gamma : Stage2.challenge? occurrence 2 1 = some gamma := by
  unfold Stage2.challenge?
  rw [if_pos (by decide : 2 = 2 ∧ (1 : Nat) < 2)]
  simp only [actual_setup, bind, Option.bind_some, challenge1_map]
  rfl

private theorem chosen_auxiliary_entry
    {s : SourceObject FGL} {r : ResolvedOccurrence s} (view : CompleteView r) (column : Fin 3) :
    auxiliaryEntry? view.base.setup column.val = some (view.mapId column, view.mapEntry column) := by
  unfold auxiliaryEntry?
  simp only [bind]
  rw [(view.selected_map column).1]
  simp only [Option.bind_some]
  rw [(view.selected_map column).2.1]
  rfl

/-- Reuse the already checked SAME native setup metadata shape, not the old
fixture's buffer values, fields, or a new caller certificate. -/
theorem complete_nonvacuous : (completeFromResolved? occurrence).isSome = true := by
  have oldPresent := CompleteConstructibility.constructor_nonvacuous false
  cases oldSelected : completeFromResolved? (CompleteConstructibility.occurrence false) with
  | none => simp [oldSelected] at oldPresent
  | some old =>
    have oldSetup : old.base.setup = Constructibility.setup :=
      Option.some.inj (old.base.setupSelected.symm.trans (CompleteConstructibility.exact_setup false))
    have present := base_nonvacuous
    cases baseSelected : fromResolved? occurrence with
    | none => simp [baseSelected] at present
    | some base =>
      have sameSetup : base.setup = old.base.setup :=
        (Option.some.inj (base.setupSelected.symm.trans actual_setup)).trans oldSetup.symm
      have e0 : auxiliaryEntry? base.setup 0 = some (old.mapId 0, old.mapEntry 0) := by
        simpa only [sameSetup] using chosen_auxiliary_entry old 0
      have e1 : auxiliaryEntry? base.setup 1 = some (old.mapId 1, old.mapEntry 1) := by
        simpa only [sameSetup] using chosen_auxiliary_entry old 1
      have e2 : auxiliaryEntry? base.setup 2 = some (old.mapId 2, old.mapEntry 2) := by
        simpa only [sameSetup] using chosen_auxiliary_entry old 2
      simp only [completeFromResolved?, baseSelected, bind, Option.bind_some]
      split
      · rename_i absent
        simp [e0] at absent
      · rename_i found0 selected0
        have equal := Option.some.inj (selected0.symm.trans e0)
        subst found0
        split
        · rename_i absent
          simp [e1] at absent
        · rename_i found1 selected1
          have equal := Option.some.inj (selected1.symm.trans e1)
          subst found1
          split
          · rename_i absent
            simp [e2] at absent
          · rename_i found2 selected2
            have equal := Option.some.inj (selected2.symm.trans e2)
            subst found2
            split_ifs with checked
            · split
              · rename_i absent
                simp [actual_alpha] at absent
              · split
                · rename_i absent
                  simp [actual_gamma] at absent
                · rfl
            · apply False.elim
              apply checked
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [sameSetup]
                exact old.auxiliary_width
              · rw [sameSetup]
                exact old.auxiliary_offset
              · intro column
                fin_cases column
                · exact (old.selected_map 0).2.2
                · exact (old.selected_map 1).2.2
                · exact (old.selected_map 2).2.2
              · rw [actual_auxiliary, auxiliaryBuffer_size]
                rfl

/-- Actual computed result, never an externally supplied successful-view binder. -/
def complete : CompleteView occurrence :=
  match selected : completeFromResolved? occurrence with
  | some view => view
  | none => False.elim (by simpa [selected] using complete_nonvacuous)

theorem complete_recovers : completeFromResolved? occurrence = some complete := by
  unfold complete
  split
  · assumption
  · rename_i absent
    have present := complete_nonvacuous
    simp [absent] at present

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage
