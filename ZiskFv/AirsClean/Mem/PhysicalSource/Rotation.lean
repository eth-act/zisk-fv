import ZiskFv.AirsClean.Mem.PhysicalSource.Domain

/-! Additive mathematical CPU rotations on the source-owned full physical
Mem domain. This does not authenticate machine addresses or native openings. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open Goldilocks

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

namespace View

@[inline] def rotate (view : View resolved) (row : view.Index) (rotation : Int) : view.Index :=
  if rotation = 0 then row else
    ⟨(((row.val : Int) + rotation) % (view.count : Int)).toNat, by
      have positive : (0 : Int) < view.count := by exact_mod_cast view.count_pos
      have lower := Int.emod_nonneg ((row.val : Int) + rotation) (ne_of_gt positive)
      have upper := Int.emod_lt_of_pos ((row.val : Int) + rotation) positive
      change (((row.val : Int) + rotation) % (view.count : Int)).toNat < view.count
      omega⟩

theorem native_rotation (view : View resolved) (row : view.Index) (rotation : Int) :
    view.setup.baseRow? row.val rotation = some (view.rotate row rotation).val := by
  have within : row.val < view.setup.rowCount := by
    rw [view.setup_rows]
    exact row.isLt
  by_cases zero : rotation = 0
  · subst rotation
    simpa [rotate] using view.native_current_row row
  · simp [NativeSetup.baseRow?, view.cpu_profile.1, view.cpu_profile.2, within,
      view.setup_rows, rotate, zero]
    exact row.isLt

@[simp] theorem rotate_zero (view : View resolved) (row : view.Index) :
    view.rotate row 0 = row := by
  apply Fin.ext
  have native := view.native_rotation row 0
  rw [view.native_current_row row] at native
  exact (Option.some.inj native).symm

@[simp] theorem rotate_one (view : View resolved) (row : view.Index) :
    view.rotate row 1 = view.next row := by
  apply Fin.ext
  have native := view.native_rotation row 1
  rw [view.native_next_row row] at native
  exact (Option.some.inj native).symm

def previous (view : View resolved) (row : view.Index) : view.Index :=
  view.rotate row (-1)

theorem native_previous (view : View resolved) (row : view.Index) :
    view.setup.baseRow? row.val (-1) = some (view.previous row).val :=
  view.native_rotation row (-1)

theorem previous_first (view : View resolved) : view.previous view.first = view.last := by
  apply Fin.ext
  have negative : (-1 : Int) ≠ 0 := by decide
  simp only [previous, rotate, first, last, if_neg negative]
  norm_num [count, Stage1.SourceColumns.physicalRows, Extraction.SourceDimensions.Mem.rowCount]
  rfl

theorem previous_of_positive (view : View resolved) (row : view.Index) (positive : 0 < row.val) :
    (view.previous row).val = row.val - 1 := by
  have within : row.val < view.count := row.isLt
  have negative : (-1 : Int) ≠ 0 := by decide
  simp only [previous, rotate, if_neg negative]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

end View
end ZiskFv.AirsClean.Mem.PhysicalSource
