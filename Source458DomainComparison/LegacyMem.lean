import ZiskFv.AirsClean.Mem.Circuit

/-!
# Historical scalar Mem domain at a015aaa7

This comparison-only snapshot preserves the former base-field restrictions;
it does NOT identify them with the actual extension-field source equations.
Production Mem and Root never import this module. Its sole purpose is to
state the original accepted domains and prove their conservative transport.
The scalar formula block is copied exactly from a015aaa7 Airs/Mem.lean.
-/

namespace ZiskFv.AirsClean.Mem.Legacy457

open Goldilocks Air.Flat
open ZiskFv.Airs.Mem

variable {F : Type} [Field F]

/-- Non-witness Mem columns used by generated constraints 24-33. -/
structure PermutationColumns (F : Type) [Field F] where
  std_alpha : F
  std_gamma : F
  l1 : ℕ → F
  im_direct_0 : F
  im_direct_1 : F
  im_direct_2 : F
  im_direct_3 : F
  im_direct_4 : F
  im_direct_5 : F

@[simp]
def gsum_increment_1
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.increment_1 row * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def gsum_dual_step
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  ((v.step_dual row - v.step row) - v.wr row) * cols.std_alpha
    + 102 + cols.std_gamma

@[simp]
def gsum_increment_0
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.increment_0 row * cols.std_alpha + 104 + cols.std_gamma

@[simp]
def gsum_primary_mem
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  (((((((v.value_1 row * cols.std_alpha + v.value_0 row) * cols.std_alpha
      + 8) * cols.std_alpha + v.step row) * cols.std_alpha
      + v.addr row * 8) * cols.std_alpha + (v.wr row + 1))
      * cols.std_alpha + 10) + cols.std_gamma)

@[simp]
def gsum_dual_mem
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  (((((((v.value_1 row * cols.std_alpha + v.value_0 row) * cols.std_alpha
      + 8) * cols.std_alpha + v.step_dual row) * cols.std_alpha
      + v.addr row * 8) * cols.std_alpha + 1)
      * cols.std_alpha + 10) + cols.std_gamma)

@[simp]
def direct_gsum_0
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  ((((((seg.previous_segment_value_1 * cols.std_alpha
      + seg.previous_segment_value_0) * cols.std_alpha
      + seg.previous_segment_step) * cols.std_alpha
      + seg.previous_segment_addr) * cols.std_alpha
      + seg.segment_id) * cols.std_alpha + 2684354560)
      * cols.std_alpha + 11) + cols.std_gamma

@[simp]
def direct_gsum_1
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  ((((((seg.segment_last_value_1 * cols.std_alpha
      + seg.segment_last_value_0) * cols.std_alpha
      + seg.segment_last_step) * cols.std_alpha
      + seg.segment_last_addr) * cols.std_alpha
      + (seg.segment_id + 1)) * cols.std_alpha + 2684354560)
      * cols.std_alpha + 11) + cols.std_gamma

@[simp]
def direct_gsum_distance_base_0
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_base_0 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def direct_gsum_distance_base_1
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_base_1 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def direct_gsum_distance_end_0
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_end_0 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def direct_gsum_distance_end_1
    (seg : SegmentColumns F) (cols : PermutationColumns F) : F :=
  seg.distance_end_1 * cols.std_alpha + 103 + cols.std_gamma

@[simp]
def gsum_accumulator_delta
    (cols : PermutationColumns F) (v : Valid_Mem F F) (row : ℕ) : F :=
  v.gsum row - v.gsum (row - 1) * (1 - cols.l1 row)
    - (v.im_0 row + v.im_1 row)

/-- Generated Mem constraints 24-33. -/
@[simp]
def permutation_every_row
    (seg : SegmentColumns F) (cols : PermutationColumns F)
    (v : Valid_Mem F F) (row : ℕ) : Prop :=
  v.im_0 row * (gsum_increment_1 cols v row * gsum_dual_step cols v row)
      - ((18446744069414584320 * gsum_dual_step cols v row)
        + ((0 - v.sel_dual row) * gsum_increment_1 cols v row)) = 0
  ∧ v.im_1 row * (gsum_primary_mem cols v row * gsum_dual_mem cols v row)
      - (v.sel row * gsum_dual_mem cols v row
        + v.sel_dual row * gsum_primary_mem cols v row) = 0
  ∧ gsum_accumulator_delta cols v row * gsum_increment_0 cols v row + 1 = 0
  ∧ cols.im_direct_0 * direct_gsum_0 seg cols + 1 = 0
  ∧ cols.im_direct_1 * direct_gsum_1 seg cols
      - (1 - seg.is_last_segment) = 0
  ∧ cols.im_direct_2 * direct_gsum_distance_base_0 seg cols + 1 = 0
  ∧ cols.im_direct_3 * direct_gsum_distance_base_1 seg cols + 1 = 0
  ∧ cols.im_direct_4 * direct_gsum_distance_end_0 seg cols + 1 = 0
  ∧ cols.im_direct_5 * direct_gsum_distance_end_1 seg cols + 1 = 0
  ∧ cols.l1 (row + 1) *
      (seg.segment_id - v.gsum row
        - (((((cols.im_direct_0 + cols.im_direct_1) + cols.im_direct_2)
          + cols.im_direct_3) + cols.im_direct_4) + cols.im_direct_5)) = 0

/-- The complete generated Mem every-row surface currently named in source. -/
@[simp]
def generated_every_row
    (seg : SegmentColumns F) (perm : PermutationColumns F)
    (v : Valid_Mem F F) (row : ℕ) : Prop :=
  segment_every_row seg v row ∧ permutation_every_row seg perm v row

/-- The active local Mem bridge is also a projection of the full generated
every-row surface. -/
theorem core_every_row_of_generated_every_row
    {seg : SegmentColumns F} {perm : PermutationColumns F}
    {v : Valid_Mem F F} {row : ℕ}
    (h : generated_every_row seg perm v row) :
    core_every_row v row :=
  core_every_row_of_segment_every_row h.1


/-- Exact former scalar auxiliary decoder; historical model data, not a
lossless decoder for native extension-field source cells. -/
def permutationColumnsOfProverDataAndFixed
    (data : ProverData FGL) (l1 : Nat → FGL) : PermutationColumns FGL where
  std_alpha := proverDataScalar data "Mem.sidecar.permutation.std_alpha"
  std_gamma := proverDataScalar data "Mem.sidecar.permutation.std_gamma"
  l1 := l1
  im_direct_0 := proverDataScalar data "Mem.sidecar.permutation.im_direct_0"
  im_direct_1 := proverDataScalar data "Mem.sidecar.permutation.im_direct_1"
  im_direct_2 := proverDataScalar data "Mem.sidecar.permutation.im_direct_2"
  im_direct_3 := proverDataScalar data "Mem.sidecar.permutation.im_direct_3"
  im_direct_4 := proverDataScalar data "Mem.sidecar.permutation.im_direct_4"
  im_direct_5 := proverDataScalar data "Mem.sidecar.permutation.im_direct_5"

/-- Former live D1 predicate, including its incorrect scalar restriction. -/
def generatedTransition (columns : IndexedFixedColumns FGL 17)
    (index : Nat) (previous current : Environment FGL) : Prop :=
  let mem := memWindow index previous current
  let segment := memSegmentColumnsOfProverDataAndFixed current.data
    (fun row => columns.fixedAt MemFixedColumn.segmentL1 row)
  let permutation := permutationColumnsOfProverDataAndFixed current.data
    (fun row => columns.fixedAt MemFixedColumn.l1 row)
  ZiskFv.Airs.Mem.segmentResidualEveryRow segment mem index
    ∧ permutation_every_row segment permutation mem index
    ∧ memRangeSidecarBridge current

/-- Historical component: original circuit, row width and fixed schema;
only the retired D1 predicate differs from the corrected component. -/
def componentWithDualMemBus : Component FGL :=
  { circuit := circuitWithDualMemBus
    rawWidth := 17
    fixedColumns := some memFixedColumns
    transition := generatedTransition memFixedColumns }

 theorem operations_eq_current :
    componentWithDualMemBus.operations =
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations := rfl

 theorem generatedTransition_implies_current
    (columns : IndexedFixedColumns FGL 17) (index : Nat)
    (previous current : Environment FGL)
    (h : generatedTransition columns index previous current) :
    ZiskFv.AirsClean.Mem.generatedTransition columns index previous current :=
  ⟨h.1, h.2.2⟩

end ZiskFv.AirsClean.Mem.Legacy457
