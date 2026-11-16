import ZiskFv.AirsClean.Mem.PhysicalSource.Rotation
import ZiskFv.AirsClean.Mem.PhysicalSource.NativeProjection
import ZiskFv.AirsClean.Mem.Stage2.Native

/-! Additive representation-only Mem view. Its private constructor computes
stage2 map selections, full original auxiliary coverage and both challenges
from the SAME occurrence as the existing physical view. No caller supplies a
trace function, reader, coherence/SourceValid promise or parse-success binder.
Neither this model nor metadata matching authenticates native execution,
compiled operand/opening ids, ABI, snapshots or complete AIR validity. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- Actual metadata lookup used by the existing stage2 partial reader. -/
def auxiliaryEntry? (setup : NativeSetup) (column : Nat) : Option (Nat × PolMap) := do
  let id ← Stage2.witnessMapId? setup 2 column
  let entry ← setup.cmPolsMap[id]?
  return (id, entry)

private theorem auxiliaryEntry_selected (setup : NativeSetup) (column : Nat)
    (entry : Nat × PolMap) (selected : auxiliaryEntry? setup column = some entry) :
    Stage2.witnessMapId? setup 2 column = some entry.1 ∧
    setup.cmPolsMap[entry.1]? = some entry.2 := by
  cases hid : Stage2.witnessMapId? setup 2 column with
  | none => simp [auxiliaryEntry?, hid, bind] at selected
  | some id =>
    cases he : setup.cmPolsMap[id]? with
    | none => simp [auxiliaryEntry?, hid, he, bind] at selected
    | some actual =>
      have equal : (id, actual) = entry := by
        simpa [auxiliaryEntry?, hid, he, bind] using selected
      cases equal
      exact ⟨rfl, he⟩

private def auxiliaryGeometry (view : View resolved) (entries : Vector (Nat × PolMap) 3) : Prop :=
  view.setup.mapSectionsN["cm2"]? = some 9 ∧
  view.setup.mapOffsets[("cm2", false)]? = some (13 * view.count) ∧
  (∀ column : Fin 3,
    entries[column].2.stage = 2 ∧ entries[column].2.dim = 3 ∧
    entries[column].2.stagePos = 3 * column.val) ∧
  22 * view.count ≤ resolved.slotData.auxTrace.size

private instance auxiliaryGeometryDecidable (view : View resolved)
    (entries : Vector (Nat × PolMap) 3) : Decidable (auxiliaryGeometry view entries) := by
  unfold auxiliaryGeometry
  infer_instance

structure CompleteView (resolved : ResolvedOccurrence source) where
  private mk ::
  base : View resolved
  private entries : Vector (Nat × PolMap) 3
  private entriesSelected : ∀ column : Fin 3,
    Stage2.witnessMapId? base.setup 2 column.val = some entries[column].1 ∧
    base.setup.cmPolsMap[entries[column].1]? = some entries[column].2
  private auxiliaryChecked : auxiliaryGeometry base entries
  alpha : Stage2.Ext3 FGL
  alphaSelected : Stage2.challenge? resolved 2 0 = some alpha
  gamma : Stage2.Ext3 FGL
  gammaSelected : Stage2.challenge? resolved 2 1 = some gamma

/-- Failure remains failure; no cell or extension coefficient is defaulted. -/
def completeFromResolved? (resolved : ResolvedOccurrence source) : Option (CompleteView resolved) := do
  let base ← fromResolved? resolved
  match h0 : auxiliaryEntry? base.setup 0 with
  | none => none
  | some entry0 =>
    match h1 : auxiliaryEntry? base.setup 1 with
    | none => none
    | some entry1 =>
      match h2 : auxiliaryEntry? base.setup 2 with
      | none => none
      | some entry2 =>
        let entries := #v[entry0, entry1, entry2]
        have selections : ∀ column : Fin 3,
            Stage2.witnessMapId? base.setup 2 column.val = some entries[column].1 ∧
            base.setup.cmPolsMap[entries[column].1]? = some entries[column].2 := by
          intro column
          fin_cases column
          · exact auxiliaryEntry_selected base.setup 0 entry0 h0
          · exact auxiliaryEntry_selected base.setup 1 entry1 h1
          · exact auxiliaryEntry_selected base.setup 2 entry2 h2
        if checked : auxiliaryGeometry base entries then
          match alphaSelected : Stage2.challenge? resolved 2 0 with
          | none => none
          | some alpha =>
            match gammaSelected : Stage2.challenge? resolved 2 1 with
            | none => none
            | some gamma =>
              some ⟨base, entries, selections, checked, alpha, alphaSelected, gamma, gammaSelected⟩
        else none

namespace CompleteView

abbrev Index (view : CompleteView resolved) := view.base.Index

theorem auxiliary_width (view : CompleteView resolved) :
    view.base.setup.mapSectionsN["cm2"]? = some 9 := view.auxiliaryChecked.1

theorem auxiliary_offset (view : CompleteView resolved) :
    view.base.setup.mapOffsets[("cm2", false)]? = some (13 * view.base.count) :=
  view.auxiliaryChecked.2.1

theorem auxiliary_coverage (view : CompleteView resolved) :
    22 * view.base.count ≤ resolved.slotData.auxTrace.size := view.auxiliaryChecked.2.2.2

def mapId (view : CompleteView resolved) (column : Fin 3) : Nat := view.entries[column].1

def mapEntry (view : CompleteView resolved) (column : Fin 3) : PolMap := view.entries[column].2

theorem selected_map (view : CompleteView resolved) (column : Fin 3) :
    Stage2.witnessMapId? view.base.setup 2 column.val = some (view.mapId column) ∧
    view.base.setup.cmPolsMap[view.mapId column]? = some (view.mapEntry column) ∧
    (view.mapEntry column).stage = 2 ∧ (view.mapEntry column).dim = 3 ∧
    (view.mapEntry column).stagePos = 3 * column.val :=
  ⟨(view.entriesSelected column).1, (view.entriesSelected column).2,
    view.auxiliaryChecked.2.2.1 column⟩

theorem auxiliary_nonempty (view : CompleteView resolved) :
    resolved.slotData.auxTrace.isEmpty = false := by
  have capacity := view.auxiliary_coverage
  have positive := view.base.count_pos
  apply Bool.eq_false_iff.mpr
  intro empty
  have zero := Array.isEmpty_iff_size_eq_zero.mp empty
  omega

theorem same_auxiliary_buffer (view : CompleteView resolved) :
    (resolved.params false).auxTrace = some resolved.slotData.auxTrace := by
  simp [ResolvedOccurrence.params, paramsOf, view.auxiliary_nonempty]

/-- Three words are addressed in the ORIGINAL source buffer, with the actual
cm2 offset retained. This is not a row-array copy or a rebased auxiliary image. -/
def auxiliaryAddress (view : CompleteView resolved) (row : view.Index) (column : Fin 3)
    (rotation : Int) (coordinate : Fin 3) : Fin resolved.slotData.auxTrace.size :=
  ⟨13 * view.base.count + 9 * (view.base.rotate row rotation).val +
    3 * column.val + coordinate.val, by
    have within : (view.base.rotate row rotation).val < view.base.count :=
      (view.base.rotate row rotation).isLt
    have coverage := view.auxiliary_coverage
    have col := column.isLt
    have coord := coordinate.isLt
    omega⟩

def auxiliary (view : CompleteView resolved) (row : view.Index) (column : Fin 3)
    (rotation : Int) : Stage2.Ext3 FGL :=
  ⟨resolved.slotData.auxTrace[view.auxiliaryAddress row column rotation 0],
   resolved.slotData.auxTrace[view.auxiliaryAddress row column rotation 1],
   resolved.slotData.auxTrace[view.auxiliaryAddress row column rotation 2]⟩

theorem auxiliary_coeff (view : CompleteView resolved) (row : view.Index) (column : Fin 3)
    (rotation : Int) (coordinate : Fin 3) :
    (view.auxiliary row column rotation).coeff coordinate =
      resolved.slotData.auxTrace[view.auxiliaryAddress row column rotation coordinate] := by
  fin_cases coordinate <;> rfl

private theorem extension_read_at (params : Params FGL) (values : Array FGL) (offset : Nat)
    (selected : params.auxTrace = some values) (bound : offset + 3 ≤ values.size) :
    Stage2.extensionWords? (readBlock? params .auxTrace offset 3) =
      some (⟨values[offset], values[offset + 1], values[offset + 2]⟩ : Stage2.Ext3 FGL) := by
  have b0 : offset < values.size := by omega
  have b1 : offset + 1 < values.size := by omega
  have b2 : offset + 2 < values.size := by omega
  simp [Stage2.extensionWords?, readBlock?, buffer?, selected, bound,
    Array.size_extract, b0, b1, b2, Array.getElem_extract]

/-- Every rotated block and all three coefficients recover the ACTUAL existing
metadata-selected partial reader, in both original stage1 storage modes. -/
theorem auxiliary_source (view : CompleteView resolved) (row : view.Index) (column : Fin 3)
    (rotation : Int) :
    Stage2.witness? resolved row.val 2 column.val rotation =
      some (view.auxiliary row column rotation) := by
  have chosen := view.selected_map column
  have supported : (2 = 1 ∧ column.val < 13) ∨ (2 = 2 ∧ column.val < 3) :=
    Or.inr ⟨rfl, column.isLt⟩
  have bound :
      (13 * view.base.count + (view.base.rotate row rotation).val * 9 + 3 * column.val) + 3 ≤
        resolved.slotData.auxTrace.size := by
    have within : (view.base.rotate row rotation).val < view.base.count :=
      (view.base.rotate row rotation).isLt
    have capacity := view.auxiliary_coverage
    have col := column.isLt
    omega
  unfold Stage2.witness?
  rw [if_pos supported]
  simp only [bind, view.base.setupSelected, Option.bind_some, chosen.1,
    show (2 : Nat) ≠ 1 by decide, ↓reduceIte]
  simp only [ResolvedOccurrence.cmWords?, bind, view.base.setupSelected, Option.bind_some,
    chosen.2.1, chosen.2.2.1, show (2 : Nat) ≠ 1 by decide,
    show (1 : Nat) < 2 by decide, ↓reduceIte]
  simp only [cmAuxAt?, bind, chosen.2.2.1, view.base.native_rotation row rotation,
    Option.bind_some, view.auxiliary_width, view.auxiliary_offset,
    chosen.2.2.2.1, chosen.2.2.2.2]
  rw [show "cm" ++ toString (2 : Nat) = "cm2" by decide]
  simp only [view.auxiliary_width, view.auxiliary_offset, Option.bind_some]
  rw [extension_read_at _ _ _ view.same_auxiliary_buffer bound]
  simp only [auxiliary, auxiliaryAddress, Nat.mul_comm]
  rfl

theorem auxiliary_coefficient_source (view : CompleteView resolved) (row : view.Index)
    (column : Fin 3) (rotation : Int) (coordinate : Fin 3) :
    (Stage2.witness? resolved row.val 2 column.val rotation).map
      (fun value => value.coeff coordinate) =
      some resolved.slotData.auxTrace[view.auxiliaryAddress row column rotation coordinate] := by
  rw [view.auxiliary_source, Option.map_some, view.auxiliary_coeff]

/-- The generic source-finalizer reader shares precisely the same auxiliary
branch; its field type is unchanged and not replaced by a conversion oracle. -/
theorem auxiliary_generic_source (view : CompleteView resolved) (row : view.Index)
    (column : Fin 3) (rotation : Int) :
    Stage2.extensionWords?
      (resolved.cmAuxWords? false (view.mapId column) row.val rotation) =
      some (view.auxiliary row column rotation) := by
  have chosen := view.selected_map column
  have branch := ResolvedOccurrence.cmWords_aux resolved false (view.mapId column)
    row.val rotation view.base.setup (view.mapEntry column) view.base.setupSelected
    chosen.2.1 (by omega : 1 < (view.mapEntry column).stage)
  have actual := view.auxiliary_source row column rotation
  have supported : (2 = 1 ∧ column.val < 13) ∨ (2 = 2 ∧ column.val < 3) :=
    Or.inr ⟨rfl, column.isLt⟩
  unfold Stage2.witness? at actual
  rw [if_pos supported] at actual
  simp only [bind, view.base.setupSelected, Option.bind_some, chosen.1,
    show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at actual
  rw [branch] at actual
  exact actual

def challenge (view : CompleteView resolved) (index : Fin 2) : Stage2.Ext3 FGL :=
  if index.val = 0 then view.alpha else view.gamma

theorem challenge_source (view : CompleteView resolved) (index : Fin 2) :
    Stage2.challenge? resolved 2 index.val = some (view.challenge index) := by
  fin_cases index
  · exact view.alphaSelected
  · exact view.gammaSelected

theorem challenge_coeff_source (view : CompleteView resolved) (index : Fin 2)
    (coordinate : Fin 3) :
    (Stage2.challenge? resolved 2 index.val).map (fun value => value.coeff coordinate) =
      some ((view.challenge index).coeff coordinate) := by
  rw [view.challenge_source]
  rfl

def stage1 (view : CompleteView resolved) (row : view.Index) : Vector FGL 13 :=
  NativeProjection.logicalRow view.base row

/-- Named scalar access calls the sole cached native cell reader directly,
without allocating a thirteen-cell vector for each individual named field. -/
def scalar (view : CompleteView resolved) (row : view.Index) (column : Fin 13) : FGL :=
  match selected : (NativeProjection.sharedRow view.base row).cell? column.val with
  | some value => value
  | none => False.elim (by
      obtain ⟨value, present⟩ := (NativeProjection.sharedRow view.base row).cell_defined column
      simp [selected] at present)

theorem scalar_checked (view : CompleteView resolved) (row : view.Index) (column : Fin 13) :
    (NativeProjection.sharedRow view.base row).cell? column.val =
      some (view.scalar row column) := by
  unfold scalar
  split
  · assumption
  · rename_i absent
    obtain ⟨value, present⟩ := (NativeProjection.sharedRow view.base row).cell_defined column
    simp [absent] at present

theorem scalar_source (view : CompleteView resolved) (row : view.Index) (column : Fin 13) :
    ZiskFv.AirsClean.NativeTraceCells.cell? .mem resolved false row.val column.val =
      some (view.scalar row column) := by
  rw [← (NativeProjection.sharedRow view.base row).cell_eq_global]
  exact view.scalar_checked row column

theorem scalar_is_logicalRow (view : CompleteView resolved) (row : view.Index) (column : Fin 13) :
    view.scalar row column = (view.stage1 row)[column] := by
  exact Option.some.inj ((view.scalar_source row column).symm.trans
    (NativeProjection.actual_coordinates view.base row column))

def group (view : CompleteView resolved) : Stage2.Ext3 FGL := view.base.group

def direct (view : CompleteView resolved) (index : Fin 6) : Stage2.Ext3 FGL := view.base.direct index

def l1 (view : CompleteView resolved) (row : view.Index) : FGL :=
  resolved.slotData.fixed[2 * row.val + 1]'(by
    have capacity := view.base.fixed_coverage
    have within : row.val < view.base.count := row.isLt
    omega)

theorem l1_source (view : CompleteView resolved) (row : view.Index) :
    view.base.l1? row = some (view.l1 row) := by
  simp [View.l1?, l1]

theorem same_source (view : CompleteView resolved) :
    (resolved.params false).trace = resolved.slotData.trace ∧
    (resolved.params false).auxTrace = some resolved.slotData.auxTrace ∧
    (resolved.params false).challenges = source.globals.challenges ∧
    (resolved.params false).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params false).airvalues = resolved.slotData.airvalues :=
  ⟨rfl, view.same_auxiliary_buffer, rfl, rfl, rfl⟩

end CompleteView
end ZiskFv.AirsClean.Mem.PhysicalSource
