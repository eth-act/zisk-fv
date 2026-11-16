import ZiskFv.AirsClean.Mem.PhysicalSource.FixedScan
import ZiskFv.AirsClean.Mem.Stage1.NativeProfile
import ZiskFv.AirsClean.Mem.Stage2.Cubic
import ZiskFv.AirsClean.MemAlignWriteByte.SourceInstance
import ZiskFv.AirsClean.NativeValuesLayout

/-! INTERNAL Mem physical domain from one actual resolved source occurrence.
No Root/Valid/Framework interface, populated-prefix count, row list, copied
trace, independent profile-success certificate or arbitrary reader is supplied.
The computed constructor checks the SAME selected setup, original UInt64 trace
capacity and native width, and scans column1 of the SAME width2 fixed buffer.
Both packed and unpacked source layouts are admitted; logical decoding is
provided separately ONLY by the shared NativeTraceCells implementation.
Native/PIL/ABI/snapshot authentication and stage2 auxiliary/challenge coverage
are not established by this internal geometry/source-value constructor. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Extraction.RuntimeMemWriteByteTraceLayout

variable {source : SourceObject FGL}

/-- Source-defined global blocks, not row-aux aliases or per-row callbacks. -/
def directBatch? (resolved : ResolvedOccurrence source) :
    Option (Vector (Vector FGL 3) 6) := do
  let a ← NativeValuesLayout.memInverseWords? 0 (resolved.params false)
  let b ← NativeValuesLayout.memInverseWords? 1 (resolved.params false)
  let c ← NativeValuesLayout.memInverseWords? 2 (resolved.params false)
  let d ← NativeValuesLayout.memInverseWords? 3 (resolved.params false)
  let e ← NativeValuesLayout.memInverseWords? 4 (resolved.params false)
  let f ← NativeValuesLayout.memInverseWords? 5 (resolved.params false)
  return #v[a, b, c, d, e, f]

/-- All three coefficients are retained without assuming an extension Field. -/
def extension (words : Vector FGL 3) : Stage2.Ext3 FGL :=
  ⟨words[0], words[1], words[2]⟩

/-- Actual data checked by the private constructor, not a new caller/Root
validity hypothesis. Widths are source-layout agreement, not value bounds. -/
private def geometry (resolved : ResolvedOccurrence source) (setup : NativeSetup)
    (cm1 : Nat) : Prop :=
  resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 14 ∧
  setup.profile.verify = false ∧ setup.profile.gpu = false ∧
  setup.rowCount = Stage1.SourceColumns.physicalRows ∧
  resolved.slotData.metadata.numRows = setup.rowCount ∧
  cm1 = memProfile.unpackedWords ∧
  resolved.slotData.metadata.nColsTrace =
    (if resolved.slotData.metadata.isPacked then memProfile.packedWords
      else memProfile.unpackedWords) ∧
  0 < resolved.slotData.metadata.nColsTrace ∧
  setup.rowCount * resolved.slotData.metadata.nColsTrace ≤ resolved.slotData.trace.size ∧
  setup.nConstants = 2 ∧
  2 * setup.rowCount ≤ resolved.slotData.fixed.size ∧
  FixedScan.check resolved.slotData.fixed = true

private instance geometryDecidable (resolved : ResolvedOccurrence source)
    (setup : NativeSetup) (cm1 : Nat) : Decidable (geometry resolved setup cm1) := by
  unfold geometry
  infer_instance

/-- Only fromResolved? can construct this source-owned lazy view. The finite
native/group/direct data are computed, not supplied as coherence hypotheses. -/
structure View (resolved : ResolvedOccurrence source) where
  private mk ::
  setup : NativeSetup
  setupSelected : resolved.setup? = some setup
  cm1 : Nat
  cm1Selected : setup.mapSectionsN["cm1"]? = some cm1
  private geometryChecked : geometry resolved setup cm1
  groupWords : Vector FGL 3
  groupSelected : NativeValuesLayout.groupWords? .mem (resolved.params false) = some groupWords
  directWords : Vector (Vector FGL 3) 6
  directSelected : directBatch? resolved = some directWords

def fromResolved? (resolved : ResolvedOccurrence source) : Option (View resolved) := do
  match hsetup : resolved.setup? with
  | none => none
  | some setup =>
    match hcm1 : setup.mapSectionsN["cm1"]? with
    | none => none
    | some cm1 =>
      if checked : geometry resolved setup cm1 then
        match hgroup : NativeValuesLayout.groupWords? .mem (resolved.params false) with
        | none => none
        | some group =>
          match hdirect : directBatch? resolved with
          | none => none
          | some direct =>
            some ⟨setup, hsetup, cm1, hcm1, checked, group, hgroup, direct, hdirect⟩
      else none

namespace View

variable {resolved : ResolvedOccurrence source}

abbrev Index (_view : View resolved) := Fin Stage1.SourceColumns.physicalRows

def count (_view : View resolved) : Nat := Stage1.SourceColumns.physicalRows

def nativeStride (_view : View resolved) : Nat := resolved.slotData.metadata.nColsTrace

theorem count_pos (view : View resolved) : 0 < view.count := by
  change 0 < 4194304
  decide

theorem registry_scope (view : View resolved) :
    resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 14 :=
  ⟨view.geometryChecked.1, view.geometryChecked.2.1⟩

theorem setup_rows (view : View resolved) : view.setup.rowCount = view.count :=
  view.geometryChecked.2.2.2.2.1

theorem cpu_profile (view : View resolved) :
    view.setup.profile.verify = false ∧ view.setup.profile.gpu = false :=
  ⟨view.geometryChecked.2.2.1, view.geometryChecked.2.2.2.1⟩

theorem metadata_rows (view : View resolved) :
    resolved.slotData.metadata.numRows = view.count := by
  have h := view.geometryChecked.2.2.2.2.2.1
  exact h.trans view.setup_rows

theorem logical_width (view : View resolved) : view.cm1 = memProfile.unpackedWords :=
  view.geometryChecked.2.2.2.2.2.2.1

theorem native_stride_profile (view : View resolved) :
    view.nativeStride = (if resolved.slotData.metadata.isPacked then memProfile.packedWords
      else memProfile.unpackedWords) :=
  view.geometryChecked.2.2.2.2.2.2.2.1

theorem native_stride_positive (view : View resolved) : 0 < view.nativeStride :=
  view.geometryChecked.2.2.2.2.2.2.2.2.1

theorem trace_coverage (view : View resolved) :
    view.count * view.nativeStride ≤ resolved.slotData.trace.size := by
  have h := view.geometryChecked.2.2.2.2.2.2.2.2.2.1
  simpa [count, nativeStride, view.setup_rows] using h

theorem fixed_width (view : View resolved) : view.setup.nConstants = 2 :=
  view.geometryChecked.2.2.2.2.2.2.2.2.2.2.1

theorem fixed_coverage (view : View resolved) :
    2 * view.count ≤ resolved.slotData.fixed.size := by
  have h := view.geometryChecked.2.2.2.2.2.2.2.2.2.2.2.1
  simpa [count, view.setup_rows] using h

theorem fixed_scan (view : View resolved) : FixedScan.check resolved.slotData.fixed = true :=
  view.geometryChecked.2.2.2.2.2.2.2.2.2.2.2.2

/-- Every address belongs to the ORIGINAL full native store. No prefix row
count replaces the setup/PIL physical domain; shared suffix words are retained. -/
def nativeAddress (view : View resolved) (row : view.Index)
    (word : Fin view.nativeStride) : Fin resolved.slotData.trace.size :=
  ⟨row.val * view.nativeStride + word.val, by
    have hrow : row.val + 1 ≤ view.count := by exact Nat.succ_le_iff.mpr row.isLt
    have hprefix := Nat.mul_le_mul_right view.nativeStride hrow
    have hcell : row.val * view.nativeStride + word.val <
        (row.val + 1) * view.nativeStride := by nlinarith [word.isLt]
    exact lt_of_lt_of_le hcell (le_trans hprefix view.trace_coverage)⟩

/-- The native fixed address is row*2+1, never byte width1/column0. -/
def l1? (_view : View resolved) (row : _view.Index) : Option FGL :=
  resolved.slotData.fixed[2 * row.val + 1]?

theorem actual_l1 (view : View resolved) (row : view.Index) :
    view.l1? row = some (if row.val = 0 then 1 else 0) := by
  exact FixedScan.check_iff _ |>.mp view.fixed_scan row

theorem same_native_fixed_buffer (view : View resolved) (row : view.Index) :
    readWord? (resolved.params false) .fixed
      (row.val * view.setup.nConstants + 1) = view.l1? row := by
  rw [view.fixed_width]
  simp [readWord?, buffer?, ResolvedOccurrence.params, paramsOf, l1?, Nat.mul_comm]

/-- Actual native mathematical CPU row-zero rotation, not an unbounded Nat
row or a caller-provided row map. Machine-address correctness remains separate. -/
theorem native_current_row (view : View resolved) (row : view.Index) :
    view.setup.baseRow? row.val 0 = some row.val := by
  have within : row.val < view.setup.rowCount := by
    rw [view.setup_rows]
    exact row.isLt
  have integerWithin : (row.val : Int) < (view.setup.rowCount : Int) := by
    exact_mod_cast within
  simp [NativeSetup.baseRow?, view.cpu_profile.1, view.cpu_profile.2, within,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) integerWithin]

def first (view : View resolved) : view.Index := ⟨0, view.count_pos⟩

def next (view : View resolved) (row : view.Index) : view.Index :=
  ⟨(row.val + 1) % view.count, Nat.mod_lt _ view.count_pos⟩

theorem native_next_row (view : View resolved) (row : view.Index) :
    view.setup.baseRow? row.val 1 = some (view.next row).val := by
  have within : row.val < view.setup.rowCount := by
    rw [view.setup_rows]
    exact row.isLt
  simp only [NativeSetup.baseRow?, view.cpu_profile.1, view.cpu_profile.2,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, within]
  congr 1
  rw [Int.toNat_emod (by omega) (by omega)]
  simp [next, view.setup_rows]

def last (view : View resolved) : view.Index :=
  ⟨view.count - 1, by
    change view.count - 1 < view.count
    have := view.count_pos
    omega⟩

theorem shifted_l1 (view : View resolved) (row : view.Index) :
    view.l1? (view.next row) = some (if row.val + 1 = view.count then 1 else 0) := by
  rw [actual_l1]
  by_cases atLast : row.val + 1 = view.count
  · simp [next, atLast]
  · have within : row.val < view.count := row.isLt
    have before : row.val + 1 < view.count := by omega
    simp [next, Nat.mod_eq_of_lt before, atLast]

/-- A unique PHYSICAL last row, derived from the full native/pulse scan. -/
theorem unique_physical_last (view : View resolved) :
    ∃! row : view.Index, view.l1? (view.next row) = some 1 := by
  refine ⟨view.last, ?_, ?_⟩
  · have positive := view.count_pos
    simp [shifted_l1, last, Nat.sub_add_cancel (by omega : 1 ≤ view.count)]
  · intro row selected
    have atLast : row.val + 1 = view.count := by
      by_contra absent
      simpa [shifted_l1, absent] using selected
    apply Fin.ext
    simp only [last]
    omega

def group (view : View resolved) : Stage2.Ext3 FGL := extension view.groupWords

def direct (view : View resolved) (index : Fin 6) : Stage2.Ext3 FGL :=
  extension view.directWords[index]

/-- Global extension values and direct inverses come from the SAME source
object/occurrence as all native rows, not another table or free group oracle. -/
theorem joint_source_buffers (view : View resolved) :
    NativeValuesLayout.groupWords? .mem (resolved.params false) = some view.groupWords ∧
    directBatch? resolved = some view.directWords ∧
    (resolved.params false).trace = resolved.slotData.trace ∧
    (resolved.params false).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params false).airvalues = resolved.slotData.airvalues :=
  ⟨view.groupSelected, view.directSelected, rfl, rfl, rfl⟩

end View
end ZiskFv.AirsClean.Mem.PhysicalSource
