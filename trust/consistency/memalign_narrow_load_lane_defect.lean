import ZiskFv.AirsClean.MemAlign.Circuit
import ZiskFv.AirsClean.MemAlignRomTable

/-!
# MemAlign narrow-load high-lane constraint repro

The source's width-1 virtual-ROM row is real, but the corresponding prove row
may reconstruct a nonzero high value lane from `reg_4..reg_7`. This checks the
local source model only: it deliberately does not claim a complete malicious
accepted witness.
-/

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.MemAlign
open ZiskFv.AirsClean.MemAlignRomTable
open ZiskFv.Channels.MemAlignRom

private def narrowLoadDefectRow : MemAlignRow FGL :=
  memAlignRowOf .prove false false false
    true false false false false false false false
    0 0 0 0 1 0 0 0
    0 0 1 0 0 (-1) 1

private def narrowLoadHonestRow : MemAlignRow FGL :=
  memAlignRowOf .prove false false false
    true false false false false false false false
    0 0 0 0 0 0 0 0
    0 0 1 0 0 (-1) 1

private def narrowLoadRomMessage : MemAlignRomMessage FGL :=
  { pc := 1, deltaPc := -1, deltaAddr := 0, offset := 0, width := 1, flags := 1 }

/-- The physical virtual-ROM row used by the repro is row 2 of the extracted
    256-row table: `[1, -1, 0, 0, 1, 1]`. -/
theorem memAlign_narrow_load_rom_row_membership :
    memAlignRomTable.Spec narrowLoadRomMessage := by
  refine ⟨⟨2, by norm_num [tableSize, Extraction.MemAlignRom.tableSize]⟩, ?_⟩
  rfl

/-- The selected width-1 prove row satisfies the extracted per-row constraint
    model, its source-shaped predecessor transition, and the unmasked cyclic
    successor transition to row zero, while its high lane is nonzero. -/
theorem memAlign_narrow_load_high_lane_constraint_repro :
    Spec narrowLoadDefectRow
      ∧ transitionRows narrowLoadDefectRow narrowLoadDefectRow
      ∧ cyclicSuccessorTransitionRows narrowLoadDefectRow memAlignIdleRow
      ∧ narrowLoadDefectRow.sel_prove = 1
      ∧ narrowLoadDefectRow.width = 1
      ∧ narrowLoadDefectRow.value_1 = 1 := by
  norm_num [narrowLoadDefectRow, memAlignIdleRow, memAlignRowOf,
    memAlignValue0Of, memAlignValue1Of, memAlignLane, Spec, transitionRows,
    cyclicSuccessorTransitionRows]

/-- The exclusion is non-vacuous on the same real ROM/D1/D3 shape: zeroing the
    high source bytes produces the architectural narrow-load high lane. -/
theorem memAlign_narrow_load_honest_high_lane :
    Spec narrowLoadHonestRow
      ∧ transitionRows narrowLoadHonestRow narrowLoadHonestRow
      ∧ cyclicSuccessorTransitionRows narrowLoadHonestRow memAlignIdleRow
      ∧ narrowLoadHonestRow.sel_prove = 1
      ∧ narrowLoadHonestRow.width = 1
      ∧ narrowLoadHonestRow.value_1 = 0 := by
  norm_num [narrowLoadHonestRow, memAlignIdleRow, memAlignRowOf,
    memAlignValue0Of, memAlignValue1Of, memAlignLane, Spec, transitionRows,
    cyclicSuccessorTransitionRows]

#print axioms memAlign_narrow_load_high_lane_constraint_repro
#print axioms memAlign_narrow_load_honest_high_lane

end ZiskFv.TrustConsistency
