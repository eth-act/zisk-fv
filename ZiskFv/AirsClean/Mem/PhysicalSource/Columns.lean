import ZiskFv.AirsClean.Mem.PhysicalSource.CompleteView

/-! Internal finite named columns only. These are NOT replacements for the
protected public Valid_Mem/PermutationColumns and are not installed in a
Component, Table, Accepted trace or Root. Source-facing construction below is
exclusively a projection of ONE privately computed CompleteView. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

abbrev PhysicalIndex := Fin Stage1.SourceColumns.physicalRows

structure PhysicalMemColumns (F : Type) where
  addr : PhysicalIndex → F
  step : PhysicalIndex → F
  sel : PhysicalIndex → F
  addr_changes : PhysicalIndex → F
  step_dual : PhysicalIndex → F
  sel_dual : PhysicalIndex → F
  value_0 : PhysicalIndex → F
  value_1 : PhysicalIndex → F
  wr : PhysicalIndex → F
  previous_step : PhysicalIndex → F
  increment_0 : PhysicalIndex → F
  increment_1 : PhysicalIndex → F
  read_same_addr : PhysicalIndex → F
  gsum : PhysicalIndex → Stage2.Ext3 F
  im_0 : PhysicalIndex → Stage2.Ext3 F
  im_1 : PhysicalIndex → Stage2.Ext3 F

structure PhysicalPermutationColumns (F : Type) where
  std_alpha : Stage2.Ext3 F
  std_gamma : Stage2.Ext3 F
  l1 : PhysicalIndex → F
  im_direct_0 : Stage2.Ext3 F
  im_direct_1 : Stage2.Ext3 F
  im_direct_2 : Stage2.Ext3 F
  im_direct_3 : Stage2.Ext3 F
  im_direct_4 : Stage2.Ext3 F
  im_direct_5 : Stage2.Ext3 F
  gsum_result : Stage2.Ext3 F

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

namespace CompleteView

def memColumns (view : CompleteView resolved) : PhysicalMemColumns FGL where
  addr := fun row => view.scalar row 0
  step := fun row => view.scalar row 1
  sel := fun row => view.scalar row 2
  addr_changes := fun row => view.scalar row 3
  step_dual := fun row => view.scalar row 4
  sel_dual := fun row => view.scalar row 5
  value_0 := fun row => view.scalar row 6
  value_1 := fun row => view.scalar row 7
  wr := fun row => view.scalar row 8
  previous_step := fun row => view.scalar row 9
  increment_0 := fun row => view.scalar row 10
  increment_1 := fun row => view.scalar row 11
  read_same_addr := fun row => view.scalar row 12
  gsum := fun row => view.auxiliary row 0 0
  im_0 := fun row => view.auxiliary row 1 0
  im_1 := fun row => view.auxiliary row 2 0

def permutationColumns (view : CompleteView resolved) : PhysicalPermutationColumns FGL where
  std_alpha := view.challenge 0
  std_gamma := view.challenge 1
  l1 := view.l1
  im_direct_0 := view.direct 0
  im_direct_1 := view.direct 1
  im_direct_2 := view.direct 2
  im_direct_3 := view.direct 3
  im_direct_4 := view.direct 4
  im_direct_5 := view.direct 5
  gsum_result := view.group

theorem current_stage1_source (view : CompleteView resolved) (row : view.Index)
    (column : Fin 13) :
    ZiskFv.AirsClean.NativeTraceCells.cell? .mem resolved false row.val column.val =
      some (view.stage1 row)[column] :=
  NativeProjection.actual_coordinates view.base row column

theorem named_stage2_source (view : CompleteView resolved) (row : view.Index) :
    Stage2.witness? resolved row.val 2 0 0 = some (view.memColumns.gsum row) ∧
    Stage2.witness? resolved row.val 2 1 0 = some (view.memColumns.im_0 row) ∧
    Stage2.witness? resolved row.val 2 2 0 = some (view.memColumns.im_1 row) :=
  ⟨view.auxiliary_source row 0 0, view.auxiliary_source row 1 0,
   view.auxiliary_source row 2 0⟩

theorem named_challenges_source (view : CompleteView resolved) :
    Stage2.challenge? resolved 2 0 = some view.permutationColumns.std_alpha ∧
    Stage2.challenge? resolved 2 1 = some view.permutationColumns.std_gamma :=
  ⟨view.challenge_source 0, view.challenge_source 1⟩

theorem named_global_source (view : CompleteView resolved) :
    view.permutationColumns.gsum_result = view.base.group ∧
    view.permutationColumns.im_direct_0 = view.base.direct 0 ∧
    view.permutationColumns.im_direct_1 = view.base.direct 1 ∧
    view.permutationColumns.im_direct_2 = view.base.direct 2 ∧
    view.permutationColumns.im_direct_3 = view.base.direct 3 ∧
    view.permutationColumns.im_direct_4 = view.base.direct 4 ∧
    view.permutationColumns.im_direct_5 = view.base.direct 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact polynomial boundary target, not an assertion that the source image
satisfies it or that numeric gsum realizes the assumed interaction balance. -/
def finalizerResidual (view : CompleteView resolved) (row : view.Index) : Stage2.Ext3 FGL :=
  Stage2.Ext3.ofBase (view.l1 (view.base.next row)) *
    (view.group - view.memColumns.gsum row -
      (((((view.direct 0 + view.direct 1) + view.direct 2) + view.direct 3) + view.direct 4) +
        view.direct 5))

theorem finalizer_coefficients (view : CompleteView resolved) (row : view.Index) :
    view.finalizerResidual row = 0 ↔
      ∀ coordinate : Fin 3, (view.finalizerResidual row).coeff coordinate = 0 := by
  constructor
  · intro zero coordinate
    rw [zero]
    exact Stage2.Ext3.coeff_zero_block coordinate
  · intro coordinates
    apply Stage2.Ext3.eq_of_coeff_eq
    intro coordinate
    rw [coordinates coordinate, Stage2.Ext3.coeff_zero_block]

end CompleteView
end ZiskFv.AirsClean.Mem.PhysicalSource
