import ZiskFv.AirsClean.Mem.PhysicalSource.NativeProjection
import ZiskFv.AirsClean.Mem.PhysicalSource.Constructibility

/-! SOURCE-ONLY evidence for the smallest protected Mem type/domain decision.
These witnesses are not new live assumptions, weakened AIR statements or a
claimed native execution. Existing Valid_Mem/PermutationColumns and public c33
remain untouched. The actual projection must be checked before using this
package to request the protected scalar-to-Ext3/cyclic-domain correction. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.Comparison

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native

/-- Retaining only coordinate zero cannot carry the actual extension element. -/
theorem scalar_projection_loses_coordinates :
    ∃ left right : Stage2.Ext3 FGL, left.c0 = right.c0 ∧ left ≠ right := by
  refine ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, rfl, ?_⟩
  intro equal
  have bad := congrArg Stage2.Ext3.c1 equal
  norm_num at bad

/-- A full physical source predecessor at first row is the physical LAST row,
not saturating Nat subtraction. This involves no row list or populated prefix. -/
theorem actual_source_predecessor :
    Constructibility.setup.baseRow? 0 (-1) = some 4194303 := by
  decide

theorem saturating_nat_predecessor : (0 : Nat) - 1 = 0 := rfl

theorem actual_predecessor_not_saturating :
    Constructibility.setup.baseRow? 0 (-1) ≠ some ((0 : Nat) - 1) := by
  rw [actual_source_predecessor]
  decide

/-- The concrete SAME source-image constructor has GROUP[7,11,13] but AIR0=0.
Replacing GROUP0 by segment_id is an actual kind/value loss even in this
nonvacuous source representation, not another name for the same caller promise. -/
theorem group_not_air_zero (packed : Bool) :
    NativeValuesLayout.groupWords? .mem ((Constructibility.occurrence packed).params false) =
      some #v[7, 11, 13] ∧
    readWord? ((Constructibility.occurrence packed).params false) .airValue 0 = some 0 ∧
    (7 : FGL) ≠ 0 := by
  refine ⟨Constructibility.exact_group packed, ?_, by decide⟩
  rfl

/-- Actual bounded source constructor/projection shape: every physical row has
all13 canonical source cells, and global extension blocks retain all3 words.
No map into the protected unbounded/scalar Mem interface is silently invented. -/
theorem actual_projection_package {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} (view : View resolved) :
    (∀ row : view.Index, ∀ column : Stage1.SourceColumns.Column,
      NativeTraceCells.cell? .mem resolved false row.val column.val =
        some (NativeProjection.logicalRow view row)[column.val]) ∧
    (∃! row : view.Index, view.l1? (view.next row) = some 1) ∧
    NativeValuesLayout.groupWords? .mem (resolved.params false) = some view.groupWords ∧
    directBatch? resolved = some view.directWords :=
  ⟨NativeProjection.actual_coordinates view, view.unique_physical_last,
    view.groupSelected, view.directSelected⟩

end ZiskFv.AirsClean.Mem.PhysicalSource.Comparison
