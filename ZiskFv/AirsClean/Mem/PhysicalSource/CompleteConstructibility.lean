import ZiskFv.AirsClean.Mem.PhysicalSource.Columns
import ZiskFv.AirsClean.Mem.PhysicalSource.Constructibility

/-! Concrete representation nonvacuity only, not all AIR equations, native
execution, compiled-id/PIL/ABI/snapshot/source-world authentication or numeric
logUp. Both native trace modes retain the original five-word suffix. The sole
new large allocation is the ORIGINAL auxiliary buffer, not decoded row maps.
Its cm2 coefficients and both challenge triples are genuinely non-base. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.CompleteConstructibility

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Stage1.SourceColumns

/-- Full native offset13N plus width9N, without cropping/rebasing the buffer. -/
def auxiliaryBuffer : Array FGL := Array.ofFn fun index : Fin (22 * physicalRows) =>
  ((index.val % 3 + 2 : Nat) : FGL)

def slot (packed : Bool) : Instance FGL :=
  { Constructibility.slot packed with auxTrace := auxiliaryBuffer }

def source (packed : Bool) : SourceObject FGL :=
  { Constructibility.source packed with
    slots := #[slot packed],
    globals := { (Constructibility.source packed).globals with
      challenges := #[29, 31, 37, 41, 43, 47] } }

def occurrence (packed : Bool) : ResolvedOccurrence (source packed) :=
  ⟨⟨0, by change 0 < 1; decide⟩, by change 0 < 1; decide⟩

theorem actual_slot (packed : Bool) : (occurrence packed).slotData = slot packed := rfl

theorem slot_fixed (packed : Bool) : (slot packed).fixed = Constructibility.fixedBuffer := by
  dsimp only [slot]
  exact Constructibility.slot_fixed packed

theorem actual_auxiliary (packed : Bool) :
    (occurrence packed).slotData.auxTrace = auxiliaryBuffer := by
  rw [actual_slot]
  dsimp only [slot]

theorem exact_setup (packed : Bool) :
    (occurrence packed).setup? = some Constructibility.setup := by
  change (Constructibility.occurrence packed).setup? = some Constructibility.setup
  exact Constructibility.exact_setup_selected packed

theorem original_trace_retained (packed : Bool) :
    (slot packed).trace = (Constructibility.slot packed).trace ∧
    (slot packed).trace.size = physicalRows * (if packed then 4 else 13) + 5 := by
  constructor
  · dsimp only [slot]
  · change (Constructibility.traceBuffer packed).size = _
    exact Constructibility.traceBuffer_size packed

theorem auxiliaryBuffer_size : auxiliaryBuffer.size = 22 * physicalRows := by
  simp only [auxiliaryBuffer, Array.size_ofFn]

theorem exact_group (packed : Bool) :
    NativeValuesLayout.groupWords? .mem ((occurrence packed).params false) =
      some #v[7, 11, 13] := by
  rw [NativeValuesLayout.group_reads_actual_buffer]
  rfl

theorem exact_directs (packed : Bool) :
    directBatch? (occurrence packed) =
      some #v[#v[15, 16, 17], #v[18, 19, 20], #v[21, 22, 23],
        #v[24, 25, 26], #v[27, 28, 29], #v[30, 31, 32]] := by
  simp [directBatch?, NativeValuesLayout.mem_inverse_reads_actual_buffer,
    occurrence, ResolvedOccurrence.params, paramsOf, ResolvedOccurrence.slotData,
    ResolvedOccurrence.globalSlot, source, slot, Constructibility.source,
    Constructibility.slot, Constructibility.airBuffer]

theorem base_constructor_nonvacuous (packed : Bool) :
    (fromResolved? (occurrence packed)).isSome = true := by
  unfold fromResolved?
  split
  · rename_i absent
    simp [exact_setup] at absent
  · rename_i selectedSetup selected
    have equal := Option.some.inj (selected.symm.trans (exact_setup packed))
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
          simp [exact_group] at absent
        · split
          · rename_i absent
            simp [exact_directs] at absent
          · rfl
      · apply False.elim
        apply checked
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, ?_, ?_⟩
        · change 0 < (if packed then 4 else 13)
          cases packed <;> decide
        · rw [actual_slot]
          change physicalRows * (if packed then 4 else 13) ≤
            (Constructibility.traceBuffer packed).size
          rw [Constructibility.traceBuffer_size]
          omega
        · rw [actual_slot, slot_fixed, Constructibility.fixedBuffer_size]
          rfl
        · rw [actual_slot, slot_fixed, Constructibility.fixedBuffer_scan]

private theorem cm2_width : Constructibility.setup.mapSectionsN["cm2"]? = some 9 := by
  simp [Constructibility.setup, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

private theorem cm2_offset :
    Constructibility.setup.mapOffsets[("cm2", false)]? = some (13 * physicalRows) := by
  simp [Constructibility.setup, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
    Nat.mul_comm]

private theorem map0 : Stage2.witnessMapId? Constructibility.setup 2 0 = some 13 := by
  unfold Stage2.witnessMapId?
  rw [if_pos (by decide : 2 = 2 ∧ (0 : Nat) = 0)]
  unfold SourceFinalizer.gsumMapId?
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  interval_cases index <;> decide +revert

private theorem map1 : Stage2.witnessMapId? Constructibility.setup 2 1 = some 14 := by
  unfold Stage2.witnessMapId?
  rw [if_neg (by decide : ¬(2 = 2 ∧ (1 : Nat) = 0))]
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  interval_cases index <;> decide +revert

private theorem map2 : Stage2.witnessMapId? Constructibility.setup 2 2 = some 15 := by
  unfold Stage2.witnessMapId?
  rw [if_neg (by decide : ¬(2 = 2 ∧ (2 : Nat) = 0))]
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  interval_cases index <;> decide +revert

private theorem entry0 : auxiliaryEntry? Constructibility.setup 0 =
    some (13, Constructibility.cmMap[13]) := by
  unfold auxiliaryEntry?
  rw [map0]
  rfl
private theorem entry1 : auxiliaryEntry? Constructibility.setup 1 =
    some (14, Constructibility.cmMap[14]) := by
  unfold auxiliaryEntry?
  rw [map1]
  rfl
private theorem entry2 : auxiliaryEntry? Constructibility.setup 2 =
    some (15, Constructibility.cmMap[15]) := by
  unfold auxiliaryEntry?
  rw [map2]
  rfl

private theorem challenge0_map :
    Constructibility.setup.challengesMap.findIdx?
      (fun entry => entry.stage == 2 && entry.stageId == 0 && entry.dim == 3) = some 0 := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  omega

private theorem challenge1_map :
    Constructibility.setup.challengesMap.findIdx?
      (fun entry => entry.stage == 2 && entry.stageId == 1 && entry.dim == 3) = some 1 := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by decide, by decide, ?_⟩
  intro index before
  interval_cases index <;> decide +revert

theorem actual_alpha (packed : Bool) : Stage2.challenge? (occurrence packed) 2 0 =
    some (⟨29, 31, 37⟩ : Stage2.Ext3 FGL) := by
  simp only [Stage2.challenge?, show 2 = 2 ∧ (0 : Nat) < 2 by decide, if_true,
    exact_setup, bind, Option.bind_some, challenge0_map]
  rfl

theorem actual_gamma (packed : Bool) : Stage2.challenge? (occurrence packed) 2 1 =
    some (⟨41, 43, 47⟩ : Stage2.Ext3 FGL) := by
  simp only [Stage2.challenge?, show 2 = 2 ∧ (1 : Nat) < 2 by decide, if_true,
    exact_setup, bind, Option.bind_some, challenge1_map]
  rfl

/-- Actual computed success on BOTH full native layouts. No arbitrary stage2
field functions, successful-read certificate or source-validity premise enters. -/
theorem constructor_nonvacuous (packed : Bool) :
    (completeFromResolved? (occurrence packed)).isSome = true := by
  have basePresent := base_constructor_nonvacuous packed
  cases selected : fromResolved? (occurrence packed) with
  | none => simp [selected] at basePresent
  | some base =>
    have setupEqual : base.setup = Constructibility.setup :=
      Option.some.inj (base.setupSelected.symm.trans (exact_setup packed))
    have e0 : auxiliaryEntry? base.setup 0 = some (13, Constructibility.cmMap[13]) := by
      rw [setupEqual]
      exact entry0
    have e1 : auxiliaryEntry? base.setup 1 = some (14, Constructibility.cmMap[14]) := by
      rw [setupEqual]
      exact entry1
    have e2 : auxiliaryEntry? base.setup 2 = some (15, Constructibility.cmMap[15]) := by
      rw [setupEqual]
      exact entry2
    simp only [completeFromResolved?, selected, bind, Option.bind_some]
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
            · rw [setupEqual]
              exact cm2_width
            · rw [setupEqual]
              exact cm2_offset
            · intro column
              fin_cases column <;> decide
            · rw [actual_auxiliary, auxiliaryBuffer_size]
              rfl

/-- Recovery reads actual original auxiliary words; the symbolic proof never
materializes or enumerates four million decoded rows. All coefficients differ
from zero, including the two that scalar-only models discard. -/
theorem auxiliary_coefficients (packed : Bool) (view : CompleteView (occurrence packed))
    (row : view.Index) (column : Fin 3) (rotation : Int) :
    view.auxiliary row column rotation = (⟨3, 4, 2⟩ : Stage2.Ext3 FGL) := by
  apply Stage2.Ext3.ext
  all_goals
    simp only [CompleteView.auxiliary, Fin.getElem_fin, CompleteView.auxiliaryAddress,
      actual_auxiliary, auxiliaryBuffer, Array.getElem_ofFn]
    have within := (view.base.rotate row rotation).isLt
    have col := column.isLt
    apply Fin.ext
    change ((13 * physicalRows + 9 * (view.base.rotate row rotation).val +
      3 * column.val + _ ) % 3 + 2 : Nat) % 18446744069414584321 = _
    norm_num [physicalRows, Extraction.SourceDimensions.Mem.rowCount]
    omega

theorem recovered_challenges (packed : Bool) (view : CompleteView (occurrence packed)) :
    view.alpha = (⟨29, 31, 37⟩ : Stage2.Ext3 FGL) ∧
    view.gamma = (⟨41, 43, 47⟩ : Stage2.Ext3 FGL) :=
  ⟨Option.some.inj (view.alphaSelected.symm.trans (actual_alpha packed)),
   Option.some.inj (view.gammaSelected.symm.trans (actual_gamma packed))⟩

theorem nonbase_stage2 : (⟨3, 4, 2⟩ : Stage2.Ext3 FGL).c1 ≠ 0 ∧
    (⟨3, 4, 2⟩ : Stage2.Ext3 FGL).c2 ≠ 0 := by decide

theorem nonbase_challenges : (⟨29, 31, 37⟩ : Stage2.Ext3 FGL).c1 ≠ 0 ∧
    (⟨41, 43, 47⟩ : Stage2.Ext3 FGL).c2 ≠ 0 := by decide

end ZiskFv.AirsClean.Mem.PhysicalSource.CompleteConstructibility
