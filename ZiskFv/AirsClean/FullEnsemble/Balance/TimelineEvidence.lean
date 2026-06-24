import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction
import ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridges
import ZiskFv.AirsClean.FullEnsemble.Balance.MemRowReplayProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.SidecarColumns
import ZiskFv.AirsClean.FullEnsemble.Balance.RowsBridgeFacts

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- The remaining semantic input required by the active table replay fold:
    every selected primary read agrees with the memory obtained by replaying
    the preceding active table rows. -/
def ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ∀ priorRows providerRow laterRows,
    table.table = priorRows ++ providerRow :: laterRows →
    (eval (table.environment providerRow)
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1 →
    (eval (table.environment providerRow)
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0 →
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
          (priorRows.flatMap fun priorProviderRow =>
            activeMemReplayEntriesOfRow
              (eval (table.environment priorProviderRow)
                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (eval (table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))

/-- Row-local active replay soundness composes over a list of generated Mem
    rows. The only semantic input still required at each row is the replay
    agreement for a selected primary read at the memory obtained from the
    preceding active rows. -/
theorem memoryBusRowsReadWriteSound_flatMap_activeMemReplayEntriesOfRow
    {α : Type}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (items : List α)
    (rowOf : α → ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_specs :
      ∀ item, item ∈ items → ZiskFv.AirsClean.Mem.Spec (rowOf item))
    (h_primary_read :
      ∀ priorItems item laterItems,
        items = priorItems ++ item :: laterItems →
        (rowOf item).sel = 1 →
        (rowOf item).wr = 0 →
          ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
            (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
              (priorItems.flatMap fun priorItem =>
                activeMemReplayEntriesOfRow (rowOf priorItem)))
            (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
              (memPrimaryReplayEntryOfRow (rowOf item)))) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory
      (items.flatMap fun item => activeMemReplayEntriesOfRow (rowOf item)) := by
  induction items generalizing initialMemory with
  | nil =>
      simp [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
  | cons item rest ih =>
      simp only [List.flatMap_cons]
      apply ZiskFv.ZiskCircuit.MemTrace.memoryBusRowsReadWriteSound_append
      · exact
          memoryBusRowsReadWriteSound_activeMemReplayEntriesOfRow_of_spec
            initialMemory
            (h_specs item (by simp))
            (fun h_sel h_wr =>
              h_primary_read [] item rest (by simp) h_sel h_wr)
      · exact
          ih
            (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
              (activeMemReplayEntriesOfRow (rowOf item)))
            (fun restItem h_restItem =>
              h_specs restItem (by simp [h_restItem]))
            (fun priorItems restItem laterItems h_split h_sel h_wr => by
              have h_split_full :
                  item :: rest = (item :: priorItems) ++ restItem :: laterItems := by
                simp [h_split]
              have h_agreement :=
                h_primary_read (item :: priorItems) restItem laterItems
                  h_split_full h_sel h_wr
              simpa [List.flatMap_cons,
                ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows_append]
                using h_agreement)

/-- Table-level wrapper for the active replay-row fold. It packages the
    mechanical `flatMap` induction while keeping the selected-primary-read
    prefix obligation explicit. -/
theorem memoryBusRowsReadWriteSound_activeMemReplayRowsOfTable_of_primary_reads
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL)
    (h_specs :
      ∀ providerRow, providerRow ∈ table.table →
        ZiskFv.AirsClean.Mem.Spec
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
    (h_primary_read :
      ActiveMemReplayRowsOfTablePrimaryReadPrefixSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory (activeMemReplayRowsOfTable table) := by
  unfold activeMemReplayRowsOfTable
  exact
    memoryBusRowsReadWriteSound_flatMap_activeMemReplayEntriesOfRow
      initialMemory table.table
      (fun providerRow =>
        eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      h_specs
      h_primary_read

/-- The indexed table bridge and range facts prove local chronological order
    for the active replay emissions projected from one concrete table row.

    This discharges the primary-before-dual part of the chronological proof
    from the generated Mem row and `mem.pil:397` range check. It does not claim
    full table-level `Pairwise` order across different provider rows. -/
theorem activeMemReplayEntriesOfTableRow_chronological_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow
        (eval (table.environment (table.table.get idx))
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) := by
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_rowAt : row = ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    dsimp [row]
    exact h_bridge.rowAt_eq idx
  have h_spec_rowAt :
      ZiskFv.AirsClean.Mem.Spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) :=
    rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_spec_row : ZiskFv.AirsClean.Mem.Spec row := by
    simpa [h_rowAt] using h_spec_rowAt
  have h_step_le_of_dual :
      row.sel_dual = 1 → row.step.val ≤ row.step_dual.val := by
    intro h_sel_dual
    have h_sel_dual_mem : mem.sel_dual idx.val = 1 := by
      simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_dual
    have h_wr_lt := wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx
    have h_step_le_rowAt :
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val).step.val ≤
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val).step_dual.val :=
      ZiskFv.AirsClean.Mem.rowAt_step_le_step_dual_of_dual_step_delta_range
        mem idx.val (h_ranges.stepColumns idx) h_wr_lt
        (h_ranges.dualStepDelta idx h_sel_dual_mem)
    simpa [h_rowAt] using h_step_le_rowAt
  exact activeMemReplayEntriesOfRow_chronological_of_spec_of_dual_step_le
    h_spec_row h_step_le_of_dual

/-- On a bridged non-boundary same-address Mem table position, if the previous
    `Valid_Mem` row has no dual emission, the previous primary timestamp is no
    later than the current primary timestamp. This is the adjacent-row
    cross-row ordering step behind full chronological `Pairwise` order. -/
theorem previous_primary_step_le_step_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_no_dual : mem.sel_dual (idx.val - 1) = 0) :
    (mem.step (idx.val - 1)).val ≤ (mem.step idx.val).val := by
  exact
    ZiskFv.Airs.Mem.previous_primary_step_le_step_of_same_addr_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary
      (h_ranges.stepColumns idx)
      (wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx)
      (h_ranges.incrementChunks idx) h_no_dual

/-- On a bridged non-boundary same-address Mem table position, if the previous
    `Valid_Mem` row has a dual emission, the previous dual timestamp is no
    later than the current primary timestamp. This is the dual predecessor case
    for adjacent-row chronological order. -/
theorem previous_dual_step_le_step_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_dual : mem.sel_dual (idx.val - 1) = 1) :
    (mem.step_dual (idx.val - 1)).val ≤ (mem.step idx.val).val := by
  exact
    ZiskFv.Airs.Mem.previous_dual_step_le_step_of_same_addr_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary
      (h_ranges.stepColumns idx)
      (wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx)
      (h_ranges.incrementChunks idx) h_dual

/-- On a bridged non-boundary address-change Mem table position, the previous
    row's address is strictly smaller than the current row's address. This is
    the adjacent address-order step behind the prior-prefix disjointness proof. -/
theorem previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    (mem.addr (idx.val - 1)).val < (mem.addr idx.val).val := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  exact
    ZiskFv.Airs.Mem.previous_addr_lt_addr_of_addr_change_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_addr_change h_not_boundary
      (h_ranges.addrColumns idx) (h_ranges.addrColumns previousIdx)
      (h_ranges.incrementChunks idx)

/-- Adjacent Mem rows in a generated single-segment table have monotone
    addresses after the first row.

    This splits on the generated `addr_changes` bit: same-address rows carry
    the previous address, and address-change rows strictly increase it. The
    non-boundary premise is supplied by the fixed `SEGMENT_L1 = [1,0...]`
    column from `mem.pil:86`. -/
theorem previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val) :
    (mem.addr (idx.val - 1)).val ≤ (mem.addr idx.val).val := by
  have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_addr_changes_zero | h_addr_changes_one
  · have h_addr_changes_zero_mem : mem.addr_changes idx.val = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero
    have h_addr_eq :=
      addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
        h_bridge idx h_addr_changes_zero_mem h_not_boundary
    rw [h_addr_eq]
  · have h_addr_changes_one_mem : mem.addr_changes idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one
    exact le_of_lt
      (previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
        h_bridge h_ranges idx h_addr_changes_one_mem h_not_boundary)

/-- The generated single-segment Mem address order is monotone between any two
    table indices. -/
theorem addr_le_of_index_le_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (earlier later : Fin table.table.length)
    (h_le : earlier.val ≤ later.val) :
    (mem.addr earlier.val).val ≤ (mem.addr later.val).val := by
  have h_mono :
      ∀ n, (h_earlier_le_n : earlier.val ≤ n) →
        n < table.table.length →
          (mem.addr earlier.val).val ≤ (mem.addr n).val := by
    intro n h_earlier_le_n h_n_lt
    induction n, h_earlier_le_n using Nat.le_induction with
    | base =>
        exact le_rfl
    | succ n _h_earlier_le_n ih =>
        have h_adj :
            (mem.addr n).val ≤ (mem.addr (n + 1)).val := by
          simpa using
            previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge
              h_bridge h_ranges h_fixed ⟨n + 1, h_n_lt⟩ (Nat.succ_pos n)
        have h_n_lt' : n < table.table.length := by omega
        exact le_trans (ih h_n_lt') h_adj
  exact h_mono later.val h_le later.isLt

/-- At a selected address-change row, every prior table row has a different
    Mem address.

    The final adjacent step is strict by the address-change increment
    constraint; all earlier adjacent steps are monotone by generated
    same-address carry or strict address-change order. -/
theorem prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1) :
    ∀ otherIdx : Fin table.table.length,
      otherIdx.val < idx.val → mem.addr otherIdx.val ≠ mem.addr idx.val := by
  intro otherIdx h_other_lt h_addr_eq
  have h_idx_pos : 0 < idx.val := by omega
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
  have h_previous_lt_current :
      (mem.addr previousIdx.val).val < (mem.addr idx.val).val := by
    simpa [previousIdx] using
      previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
        h_bridge h_ranges idx h_addr_change h_not_boundary
  have h_other_le_previous :
      (mem.addr otherIdx.val).val ≤ (mem.addr previousIdx.val).val := by
    apply addr_le_of_index_le_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed otherIdx previousIdx
    simp [previousIdx]
    omega
  have h_other_lt_current :
      (mem.addr otherIdx.val).val < (mem.addr idx.val).val :=
    lt_of_le_of_lt h_other_le_previous h_previous_lt_current
  rw [h_addr_eq] at h_other_lt_current
  exact (lt_irrefl _ h_other_lt_current)

/-- A nonempty generated Mem segment carries a 29-bit previous-segment address.

    The segment distance chunks (`mem.pil:267-268`) and generated base-distance
    equation (`mem.pil:265`) first give a coarse `2^33` bound. The fixed
    `SEGMENT_L1` row-0 boundary (`mem.pil:86`) then splits on row 0:
    same-address rows identify `mem.addr 0` with `previous_segment_addr`, and
    address-change rows make `previous_segment_addr < mem.addr 0`. In both
    cases the row address has the 29-bit witness-column bound from
    `mem.pil:109`. -/
theorem previous_segment_addr_lt_two_pow_29_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    segment.previous_segment_addr.val < 2 ^ 29 := by
  let idx0 : Fin table.table.length := ⟨0, h_nonempty⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    simpa [idx0] using (h_bridge.generatedAt idx0).1
  have h_boundary : segment.segment_l1 0 = 1 :=
    h_fixed.segmentL1_first h_nonempty
  have h_prev_lt_33 : segment.previous_segment_addr.val < 2 ^ 33 :=
    ZiskFv.Airs.Mem.previous_segment_addr_lt_two_pow_33_of_segment_every_row
      h_segment h_segment_ranges.distanceBaseChunks
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx0
  rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem 0) h_spec with
    h_addr_changes_zero | h_addr_changes_one
  · have h_addr_changes_zero_mem : mem.addr_changes 0 = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero
    have h_addr_eq :=
      ZiskFv.Airs.Mem.addr_eq_previous_segment_of_same_addr_boundary_segment_every_row
        h_segment h_addr_changes_zero_mem h_boundary
    rw [← h_addr_eq]
    exact h_ranges.addrColumns idx0
  · have h_addr_changes_one_mem : mem.addr_changes 0 = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one
    have h_prev_expr :=
      ZiskFv.Airs.Mem.segment_previous_addr_eq_previous_segment_of_boundary
        (cols := segment) (v := mem) (row := 0) h_boundary
    have h_prev_expr_range :
        (ZiskFv.Airs.Mem.segment_previous_addr segment mem 0).val < 2 ^ 33 := by
      rw [h_prev_expr]
      exact h_prev_lt_33
    have h_lt :=
      ZiskFv.Airs.Mem.segment_previous_addr_lt_addr_of_addr_change_segment_every_row_of_previous_lt_two_pow_33
        (cols := segment) (v := mem) (row := 0)
        h_segment h_addr_changes_one_mem (h_ranges.addrColumns idx0)
        h_prev_expr_range (h_ranges.incrementChunks idx0)
    rw [h_prev_expr] at h_lt
    exact lt_trans h_lt (h_ranges.addrColumns idx0)

/-- The previous-segment carried address is no greater than any generated Mem row
    address, assuming the carried address has the same 29-bit no-wrap bound as
    row addresses.

    Row zero is the fixed segment boundary (`mem.pil:86`): same-address rows
    equal the carried address, while address-change rows are strictly larger by
    the generated increment equation (`mem.pil:375`) plus range checks. Later
    rows inherit the bound from adjacent monotonicity. -/
theorem previous_segment_addr_le_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29)
    (idx : Fin table.table.length) :
    segment.previous_segment_addr.val ≤ (mem.addr idx.val).val := by
  have h_mono :
      ∀ n, n < table.table.length →
        segment.previous_segment_addr.val ≤ (mem.addr n).val := by
    intro n h_n_lt
    induction n with
    | zero =>
        let idx0 : Fin table.table.length := ⟨0, h_n_lt⟩
        have h_segment :
            ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
          simpa [idx0] using (h_bridge.generatedAt idx0).1
        have h_boundary : segment.segment_l1 0 = 1 := h_fixed.segmentL1_first h_n_lt
        have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx0
        rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
            (ZiskFv.AirsClean.Mem.rowAt mem 0) h_spec with
          h_addr_changes_zero | h_addr_changes_one
        · have h_addr_changes_zero_mem : mem.addr_changes 0 = 0 := by
            simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero
          have h_addr_eq :=
            ZiskFv.Airs.Mem.addr_eq_previous_segment_of_same_addr_boundary_segment_every_row
              h_segment h_addr_changes_zero_mem h_boundary
          rw [h_addr_eq]
        · have h_addr_changes_one_mem : mem.addr_changes 0 = 1 := by
            simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one
          have h_prev_expr :=
            ZiskFv.Airs.Mem.segment_previous_addr_eq_previous_segment_of_boundary
              (cols := segment) (v := mem) (row := 0) h_boundary
          have h_prev_expr_range :
              (ZiskFv.Airs.Mem.segment_previous_addr segment mem 0).val < 2 ^ 29 := by
            rw [h_prev_expr]
            exact h_previous_segment_addr_range
          have h_lt :=
            ZiskFv.Airs.Mem.segment_previous_addr_lt_addr_of_addr_change_segment_every_row
              (cols := segment) (v := mem) (row := 0)
              h_segment h_addr_changes_one_mem (h_ranges.addrColumns idx0)
              h_prev_expr_range (h_ranges.incrementChunks idx0)
          rw [h_prev_expr] at h_lt
          exact le_of_lt h_lt
    | succ n ih =>
        have h_n_lt' : n < table.table.length := by omega
        have h_adj :
            (mem.addr n).val ≤ (mem.addr (n + 1)).val := by
          simpa using
            previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge
              h_bridge h_ranges h_fixed ⟨n + 1, h_n_lt⟩ (Nat.succ_pos n)
        exact le_trans (ih h_n_lt') h_adj
  exact h_mono idx.val idx.isLt

/-- At an address-change row, the previous-segment seed address is strictly less
    than the current row address. -/
theorem previous_segment_addr_lt_addr_of_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1) :
    segment.previous_segment_addr.val < (mem.addr idx.val).val := by
  by_cases h_idx_zero : idx.val = 0
  · let idx0 : Fin table.table.length := ⟨0, by omega⟩
    have h_segment :
        ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
      simpa [idx0] using (h_bridge.generatedAt idx0).1
    have h_boundary : segment.segment_l1 0 = 1 :=
      h_fixed.segmentL1_first idx0.isLt
    have h_prev_expr :=
      ZiskFv.Airs.Mem.segment_previous_addr_eq_previous_segment_of_boundary
        (cols := segment) (v := mem) (row := 0) h_boundary
    have h_prev_expr_range :
        (ZiskFv.Airs.Mem.segment_previous_addr segment mem 0).val < 2 ^ 29 := by
      rw [h_prev_expr]
      exact h_previous_segment_addr_range
    have h_addr_change_zero : mem.addr_changes 0 = 1 := by
      simpa [h_idx_zero] using h_addr_change
    have h_lt :=
      ZiskFv.Airs.Mem.segment_previous_addr_lt_addr_of_addr_change_segment_every_row
        (cols := segment) (v := mem) (row := 0)
        h_segment h_addr_change_zero (h_ranges.addrColumns idx0)
        h_prev_expr_range (h_ranges.incrementChunks idx0)
    rw [h_prev_expr] at h_lt
    simpa [h_idx_zero] using h_lt
  · have h_idx_pos : 0 < idx.val := by omega
    let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
    have h_seed_le_previous :
        segment.previous_segment_addr.val ≤ (mem.addr previousIdx.val).val :=
      previous_segment_addr_le_addr_memTableGeneratedRowsBridge
        h_bridge h_ranges h_fixed h_previous_segment_addr_range previousIdx
    have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
    have h_previous_lt_current :
        (mem.addr previousIdx.val).val < (mem.addr idx.val).val := by
      simpa [previousIdx] using
        previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
          h_bridge h_ranges idx h_addr_change h_not_boundary
    exact lt_of_le_of_lt h_seed_le_previous h_previous_lt_current

/-- Address-change primary reads are byte-disjoint from the continuation seed
    entry once the seed address has the 29-bit no-wrap bound. -/
theorem previousSegmentSeedDisjoint_of_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val))
      (memPreviousSegmentReplayEntry segment) := by
  have h_seed_lt_current :=
    previous_segment_addr_lt_addr_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed h_previous_segment_addr_range idx h_addr_change
  have h_row_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_addr_ne :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        segment.previous_segment_addr := by
    intro h_addr_eq
    have h_mem_addr_eq : mem.addr idx.val = segment.previous_segment_addr := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq
    rw [h_mem_addr_eq] at h_seed_lt_current
    exact lt_irrefl _ h_seed_lt_current
  exact
    memoryBusEntryByteDisjoint_primary_previousSegment_of_addr_ne
      h_row_range h_previous_segment_addr_range h_addr_ne

/-- Address-change reads are justified against their concrete split prefix when
some selected row at the same Mem address contributes the zero-preload pointer.

This generalizes the selected-row address-change theorem to inactive predecessor
rows used by the same-address carry induction. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx preloadIdx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_preload_sel : mem.sel preloadIdx.val = 1)
    (h_addr_eq : mem.addr idx.val = mem.addr preloadIdx.val)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_zero :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) := by
    simpa [readEntry] using
      readEventReplayAgreement_after_zeroMemoryOfRows_same_addr_memTableGeneratedRowsBridge
        h_bridge h_ranges idx preloadIdx h_preload_sel h_addr_eq h_addr_change h_read
  apply
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
      h_zero
  intro entry h_entry
  rcases List.mem_flatMap.mp h_entry with
    ⟨priorProviderRow, h_prior_mem, h_entry_row⟩
  rcases priorRows_mem_index_lt_of_split
      (xs := table.table) (priorRows := priorRows)
      (laterRows := laterRows) (providerRow := providerRow)
      h_split h_prior_mem with
    ⟨otherIdx, h_get, h_other_lt_prior_length⟩
  have h_other_lt_idx : otherIdx.val < idx.val := by omega
  have h_addr_ne :=
    prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed idx h_addr_change otherIdx h_other_lt_idx
  have h_entry_rowAt :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
    rw [← h_get] at h_entry_row
    rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
    exact h_entry_row
  have h_selected_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_other_range :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
  have h_addr_ne_row :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
    intro h_addr_eq_row
    exact h_addr_ne (by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq_row.symm)
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry_rowAt with
    h_entry_primary | h_entry_dual
  · simpa [readEntry, h_entry_primary] using
      memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row
  · simpa [readEntry, h_entry_dual] using
      memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row

/-- Address-change reads are justified against the continuation-seeded initial
    memory when the previous-segment seed entry is byte-disjoint from the read.

    This factors the replay-fold mechanics from the remaining AIR/range fact:
    proving the seed disjointness (or a safe overwrite alternative) is the next
    continuation-specific obligation. -/
theorem readEventReplayAgreement_after_previousSegmentInitialMemory_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx preloadIdx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_preload_sel : mem.sel preloadIdx.val = 1)
    (h_addr_eq : mem.addr idx.val = mem.addr preloadIdx.val)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_seed_disjoint :
      ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
        (memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val))
        (memPreviousSegmentReplayEntry segment)) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_zero :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) := by
    simpa [readEntry] using
      readEventReplayAgreement_after_zeroMemoryOfRows_same_addr_memTableGeneratedRowsBridge
        h_bridge h_ranges idx preloadIdx h_preload_sel h_addr_eq h_addr_change h_read
  have h_seed :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) := by
    have h_lift :=
      ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_disjoint
        h_zero
        (by simpa [readEntry] using h_seed_disjoint)
    simpa [previousSegmentInitialMemoryOfRows] using h_lift
  apply
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
      h_seed
  intro entry h_entry
  rcases List.mem_flatMap.mp h_entry with
    ⟨priorProviderRow, h_prior_mem, h_entry_row⟩
  rcases priorRows_mem_index_lt_of_split
      (xs := table.table) (priorRows := priorRows)
      (laterRows := laterRows) (providerRow := providerRow)
      h_split h_prior_mem with
    ⟨otherIdx, h_get, h_other_lt_prior_length⟩
  have h_other_lt_idx : otherIdx.val < idx.val := by omega
  have h_addr_ne :=
    prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed idx h_addr_change otherIdx h_other_lt_idx
  have h_entry_rowAt :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
    rw [← h_get] at h_entry_row
    rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
    exact h_entry_row
  have h_selected_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_other_range :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
  have h_addr_ne_row :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
    intro h_addr_eq_row
    exact h_addr_ne (by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq_row.symm)
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry_rowAt with
    h_entry_primary | h_entry_dual
  · simpa [readEntry, h_entry_primary] using
      memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row
  · simpa [readEntry, h_entry_dual] using
      memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row

/-- Iterate same-address predecessor carry for any read row up to a selected row
    at the same Mem address over an arbitrary initial memory.

The induction itself only uses generated same-address predecessor facts. The
caller supplies the semantic bases: row-0/segment-boundary same-address reads,
and address-change reads against the chosen initial memory. -/
theorem readEventReplayAgreement_after_initialMemory_splitPrefix_to_selected_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (selectedIdx : Fin table.table.length)
    (h_boundary_same_addr :
      ∀ providerRow laterRows,
        table.table = providerRow :: laterRows →
        mem.addr_changes 0 = 0 →
        mem.wr 0 = 0 →
        mem.addr 0 = mem.addr selectedIdx.val →
          ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
            initialMemory
            (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
              (memPrimaryReplayEntryOfRow
                (ZiskFv.AirsClean.Mem.rowAt mem 0))))
    (h_addr_change_base :
      ∀ currentIdx : Fin table.table.length,
        ∀ currentPriorRows currentProviderRow currentLaterRows,
          table.table =
              currentPriorRows ++ currentProviderRow :: currentLaterRows →
          currentIdx.val = currentPriorRows.length →
          currentIdx.val ≤ selectedIdx.val →
          mem.addr currentIdx.val = mem.addr selectedIdx.val →
          mem.addr_changes currentIdx.val = 1 →
          mem.wr currentIdx.val = 0 →
            ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
              (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
                initialMemory
                (currentPriorRows.flatMap fun currentPriorProviderRow =>
                  activeMemReplayEntriesOfRow
                    (eval (table.environment currentPriorProviderRow)
                      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
              (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
                (memPrimaryReplayEntryOfRow
                  (ZiskFv.AirsClean.Mem.rowAt mem currentIdx.val))))
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_idx_le_selected : idx.val ≤ selectedIdx.val)
    (h_addr_eq_selected : mem.addr idx.val = mem.addr selectedIdx.val)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        initialMemory
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let prefixRows (rows : List (Array FGL)) :=
    rows.flatMap fun priorProviderRow =>
      activeMemReplayEntriesOfRow
        (eval (table.environment priorProviderRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
  let P : ℕ → Prop := fun n =>
    ∀ (idx : Fin table.table.length)
      (priorRows : List (Array FGL))
      (providerRow : Array FGL)
      (laterRows : List (Array FGL)),
      idx.val = n →
      table.table = priorRows ++ providerRow :: laterRows →
      idx.val = priorRows.length →
      idx.val ≤ selectedIdx.val →
      mem.addr idx.val = mem.addr selectedIdx.val →
      mem.wr idx.val = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
            initialMemory (prefixRows priorRows))
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem idx.val)))
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih idx priorRows providerRow laterRows h_idx_n h_split
      h_idx_val h_idx_le_selected h_addr_eq_selected h_read
    have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
    rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
      h_addr_changes_zero_row | h_addr_changes_one_row
    · have h_addr_changes_zero : mem.addr_changes idx.val = 0 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero_row
      by_cases h_idx_zero : idx.val = 0
      · have h_prior_nil : priorRows = [] := by
          have h_prior_length_zero : priorRows.length = 0 := by omega
          exact List.length_eq_zero_iff.mp h_prior_length_zero
        have h_split_zero : table.table = providerRow :: laterRows := by
          simpa [h_prior_nil] using h_split
        have h_zero :=
          h_boundary_same_addr providerRow laterRows h_split_zero
            (by simpa [h_idx_zero] using h_addr_changes_zero)
            (by simpa [h_idx_zero] using h_read)
            (by simpa [h_idx_zero] using h_addr_eq_selected)
        simpa [prefixRows, h_prior_nil, h_idx_zero] using h_zero
      · have h_idx_pos : 0 < idx.val := Nat.pos_of_ne_zero h_idx_zero
        have h_prior_ne : priorRows ≠ [] := by
          intro h_nil
          rw [h_nil] at h_idx_val
          simp at h_idx_val
          omega
        let previousProviderRow := priorRows.getLast h_prior_ne
        let priorPrefix := priorRows.dropLast
        have h_prior_split :
            priorRows = priorPrefix ++ [previousProviderRow] := by
          exact (List.dropLast_concat_getLast h_prior_ne).symm
        have h_split_previous :
            table.table = priorPrefix ++ previousProviderRow :: providerRow :: laterRows := by
          rw [h_prior_split] at h_split
          simpa [priorPrefix, previousProviderRow, List.append_assoc] using h_split
        have h_idx_val_previous : idx.val = priorPrefix.length + 1 := by
          have h_len : priorRows.length = priorPrefix.length + 1 := by
            rw [h_prior_split]
            simp [priorPrefix, previousProviderRow]
          omega
        let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
        have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
        have h_addr_previous :=
          addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
            h_bridge idx h_addr_changes_zero h_not_boundary
        have h_previous_addr_eq_selected :
            mem.addr previousIdx.val = mem.addr selectedIdx.val := by
          simpa [previousIdx] using h_addr_previous.symm.trans h_addr_eq_selected
        have h_previous_idx_val :
            previousIdx.val = priorPrefix.length := by
          simp [previousIdx]
          omega
        have h_previous_lt : previousIdx.val < idx.val := by
          simp [previousIdx]
          omega
        have h_previous_lt_n : previousIdx.val < n := by
          omega
        have h_previous_le_selected : previousIdx.val ≤ selectedIdx.val := by
          omega
        have h_current :=
          readEventReplayAgreement_after_initialMemory_splitPrefix_previous_row_memTableGeneratedRowsBridge
            initialMemory h_bridge h_fixed idx priorPrefix previousProviderRow
            providerRow laterRows h_split_previous h_idx_val_previous
            h_addr_changes_zero h_read
            (fun h_previous_read => by
              exact
                ih previousIdx.val h_previous_lt_n previousIdx priorPrefix
                  previousProviderRow (providerRow :: laterRows) rfl
                  h_split_previous h_previous_idx_val h_previous_le_selected
                  h_previous_addr_eq_selected h_previous_read)
        simpa [prefixRows, h_prior_split] using h_current
    · have h_addr_changes_one : mem.addr_changes idx.val = 1 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one_row
      simpa [prefixRows] using
        h_addr_change_base idx priorRows providerRow laterRows h_split h_idx_val
          h_idx_le_selected h_addr_eq_selected h_addr_changes_one h_read
  exact
    hP idx.val idx priorRows providerRow laterRows rfl h_split h_idx_val
      h_idx_le_selected h_addr_eq_selected h_read

/-- Iterate same-address predecessor carry for any read row up to a selected row
at the same Mem address from the finite zero-preloaded Mem-table memory.

The only remaining base outside the extracted local constraints is the
row-0/segment-boundary same-address case. When `addr_changes = 1`, the finite
zero-preload memory supplies the read bytes; when `addr_changes = 0` at a
positive index, the predecessor lemma moves one row backward. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_to_selected_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (selectedIdx : Fin table.table.length)
    (h_selected_sel : mem.sel selectedIdx.val = 1)
    (h_boundary_same_addr :
      ∀ providerRow laterRows,
        table.table = providerRow :: laterRows →
        mem.addr_changes 0 = 0 →
        mem.wr 0 = 0 →
        mem.addr 0 = mem.addr selectedIdx.val →
          ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
            (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
              (activeMemReplayRowsOfTable table))
            (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
              (memPrimaryReplayEntryOfRow
                (ZiskFv.AirsClean.Mem.rowAt mem 0))))
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_idx_le_selected : idx.val ≤ selectedIdx.val)
    (h_addr_eq_selected : mem.addr idx.val = mem.addr selectedIdx.val)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  refine
    readEventReplayAgreement_after_initialMemory_splitPrefix_to_selected_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
      h_bridge h_fixed selectedIdx h_boundary_same_addr ?_
      idx priorRows providerRow laterRows h_split h_idx_val h_idx_le_selected
      h_addr_eq_selected h_read
  intro currentIdx currentPriorRows currentProviderRow currentLaterRows
    h_current_split h_current_idx_val _h_current_le_selected h_current_addr_eq
    h_current_addr_change h_current_read
  exact
    readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed currentIdx selectedIdx currentPriorRows currentProviderRow
      currentLaterRows h_current_split h_current_idx_val h_selected_sel
      h_current_addr_eq h_current_addr_change h_current_read

/-- The concrete table's selected-primary-read prefix obligation follows from
the Mem AIR predecessor induction plus one explicit row-0 same-address boundary
input.

This is the current reduced proof surface: all positive-index same-address
reads iterate to either an address-change zero-preload base or this row-0
segment-continuation case. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_memTableGeneratedRowsBridge_boundary_same_addr
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_boundary_same_addr :
      ∀ selectedIdx : Fin table.table.length,
        ∀ providerRow laterRows,
          mem.sel selectedIdx.val = 1 →
          table.table = providerRow :: laterRows →
          mem.addr_changes 0 = 0 →
          mem.wr 0 = 0 →
          mem.addr 0 = mem.addr selectedIdx.val →
            ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
              (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
                (activeMemReplayRowsOfTable table))
              (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
                (memPrimaryReplayEntryOfRow
                  (ZiskFv.AirsClean.Mem.rowAt mem 0)))) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      table := by
  intro priorRows providerRow laterRows h_split h_sel_row h_wr_row
  let idx : Fin table.table.length := ⟨priorRows.length, by
    rw [h_split]
    simp⟩
  have h_idx_val : idx.val = priorRows.length := rfl
  have h_provider_get : table.table.get idx = providerRow :=
    providerRow_get_eq_of_split idx h_split h_idx_val
  have h_rowAt :
      eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    rw [← h_provider_get]
    exact h_bridge.rowAt_eq idx
  have h_sel : mem.sel idx.val = 1 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_row
  have h_read : mem.wr idx.val = 0 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_wr_row
  have h_agreement :=
    readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_to_selected_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed idx h_sel
      (fun providerRow laterRows h_boundary_split h_addr_changes_zero h_boundary_read
          h_boundary_addr_eq =>
        h_boundary_same_addr idx providerRow laterRows h_sel h_boundary_split
          h_addr_changes_zero h_boundary_read h_boundary_addr_eq)
      idx priorRows providerRow laterRows h_split h_idx_val le_rfl rfl h_read
  simpa [h_rowAt] using h_agreement

/-- The generated first-segment boundary constraint forces `addr_changes = 1`
    at row 0.

    This projects `mem.pil:377`
    `is_first_segment * SEGMENT_L1 * (1 - addr_changes) = 0` through the
    indexed table bridge, using the fixed `SEGMENT_L1 0 = 1` fact from
    `mem.pil:86` and an explicit first-segment witness. -/
theorem addr_changes_eq_one_of_first_segment_row_zero_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1)
    {providerRow : Array FGL}
    {laterRows : List (Array FGL)}
    (h_split : table.table = providerRow :: laterRows) :
    mem.addr_changes 0 = 1 := by
  let idx0 : Fin table.table.length := ⟨0, by
    rw [h_split]
    simp⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    have h_generated := h_bridge.generatedAt idx0
    simpa [idx0] using h_generated.1
  have h_boundary : segment.segment_l1 0 = 1 := by
    have h_nonempty : 0 < table.table.length := by
      rw [h_split]
      simp
    exact h_fixed.segmentL1_first h_nonempty
  exact
    ZiskFv.Airs.Mem.addr_changes_eq_one_of_first_segment_boundary_segment_every_row
      h_segment h_first_segment h_boundary

/-- For the first generated Mem segment, the row-0 same-address boundary case
    is impossible: `mem.pil:377` forces row 0 to be an address-change row.

    Continuation segments still require a different initial-memory statement
    carrying `previous_segment_*`; this theorem intentionally closes only the
    first-segment specialization against the finite zero-preload memory. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_firstSegment_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      table := by
  refine
    activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_memTableGeneratedRowsBridge_boundary_same_addr
      h_bridge h_ranges h_fixed ?_
  intro selectedIdx providerRow laterRows _h_sel h_split h_addr_changes_zero _h_read _h_addr_eq
  have h_addr_changes_one :=
    addr_changes_eq_one_of_first_segment_row_zero_memTableGeneratedRowsBridge
      h_bridge h_fixed h_first_segment (providerRow := providerRow) (laterRows := laterRows)
      h_split
  rw [h_addr_changes_zero] at h_addr_changes_one
  exact False.elim (zero_ne_one h_addr_changes_one)

/-- In a continuation Mem segment, a row-0 same-address read is justified by
    the previous segment's carried-out address and value chunks.

    This is the local base case needed before changing the table-wide induction
    to use a continuation-aware initial memory. It intentionally proves only the
    row-0 read itself; preservation through later zero-preload/replay folds is a
    separate integration obligation. -/
theorem readEventReplayAgreement_after_previousSegmentInitialMemory_row_zero_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    {providerRow : Array FGL}
    {laterRows : List (Array FGL)}
    (h_split : table.table = providerRow :: laterRows)
    (h_addr_changes_zero : mem.addr_changes 0 = 0)
    (h_read : mem.wr 0 = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem 0))) := by
  let idx0 : Fin table.table.length := ⟨0, by
    rw [h_split]
    simp⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    have h_generated := h_bridge.generatedAt idx0
    simpa [idx0] using h_generated.1
  have h_boundary : segment.segment_l1 0 = 1 := by
    have h_nonempty : 0 < table.table.length := by
      rw [h_split]
      simp
    exact h_fixed.segmentL1_first h_nonempty
  have h_read_same_addr :
      mem.read_same_addr 0 = 1 := by
    simpa [idx0] using
      read_same_addr_eq_one_of_memTableGeneratedRowsBridge
        h_bridge idx0 h_addr_changes_zero h_read
  have h_addr :
      mem.addr 0 = segment.previous_segment_addr :=
    ZiskFv.Airs.Mem.addr_eq_previous_segment_of_same_addr_boundary_segment_every_row
      h_segment h_addr_changes_zero h_boundary
  have h_values :
      mem.value_0 0 = segment.previous_segment_value_0
        ∧ mem.value_1 0 = segment.previous_segment_value_1 :=
    ZiskFv.Airs.Mem.values_eq_previous_segment_of_read_same_addr_boundary_segment_every_row
      h_segment h_read_same_addr h_boundary
  let writeEntry := memPreviousSegmentReplayEntry segment
  let readEntry := memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem 0)
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    dsimp [readEntry, writeEntry]
    simp [h_addr]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry
          (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
          writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
      h_ptr h_value_0 h_value_1
  simpa [previousSegmentInitialMemoryOfRows, writeEntry, readEntry] using h_replay

/-- The continuation-seeded table's selected-primary-read prefix obligation
    follows from the generic predecessor induction plus an explicit
    address-change seed-disjointness premise.

    The row-0 same-address base is supplied by `previous_segment_*`; the
    remaining continuation-specific work is to prove the seed cannot corrupt
    zero-valued address-change reads. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_addr_change_seed_disjoint :
      ∀ currentIdx selectedIdx : Fin table.table.length,
        ∀ currentPriorRows currentProviderRow currentLaterRows,
          mem.sel selectedIdx.val = 1 →
          table.table =
              currentPriorRows ++ currentProviderRow :: currentLaterRows →
          currentIdx.val = currentPriorRows.length →
          currentIdx.val ≤ selectedIdx.val →
          mem.addr currentIdx.val = mem.addr selectedIdx.val →
          mem.addr_changes currentIdx.val = 1 →
          mem.wr currentIdx.val = 0 →
            ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
              (memPrimaryReplayEntryOfRow
                (ZiskFv.AirsClean.Mem.rowAt mem currentIdx.val))
              (memPreviousSegmentReplayEntry segment)) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  intro priorRows providerRow laterRows h_split h_sel_row h_wr_row
  let idx : Fin table.table.length := ⟨priorRows.length, by
    rw [h_split]
    simp⟩
  have h_idx_val : idx.val = priorRows.length := rfl
  have h_provider_get : table.table.get idx = providerRow :=
    providerRow_get_eq_of_split idx h_split h_idx_val
  have h_rowAt :
      eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    rw [← h_provider_get]
    exact h_bridge.rowAt_eq idx
  have h_sel : mem.sel idx.val = 1 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_row
  have h_read : mem.wr idx.val = 0 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_wr_row
  have h_agreement :=
    readEventReplayAgreement_after_initialMemory_splitPrefix_to_selected_memTableGeneratedRowsBridge
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      h_bridge h_fixed idx
      (fun boundaryProviderRow boundaryLaterRows h_boundary_split
          h_addr_changes_zero h_boundary_read _h_boundary_addr_eq =>
        readEventReplayAgreement_after_previousSegmentInitialMemory_row_zero_memTableGeneratedRowsBridge
          h_bridge h_fixed h_boundary_split h_addr_changes_zero h_boundary_read)
      (fun currentIdx currentPriorRows currentProviderRow currentLaterRows
          h_current_split h_current_idx_val h_current_le_selected h_current_addr_eq
          h_current_addr_change h_current_read =>
        readEventReplayAgreement_after_previousSegmentInitialMemory_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
          h_bridge h_ranges h_fixed currentIdx idx currentPriorRows currentProviderRow
          currentLaterRows h_current_split h_current_idx_val h_sel h_current_addr_eq
          h_current_addr_change h_current_read
          (h_addr_change_seed_disjoint currentIdx idx currentPriorRows
            currentProviderRow currentLaterRows h_sel h_current_split h_current_idx_val
            h_current_le_selected h_current_addr_eq h_current_addr_change h_current_read))
      idx priorRows providerRow laterRows h_split h_idx_val le_rfl rfl h_read
  simpa [h_rowAt] using h_agreement

/-- The continuation-seeded table's selected-primary-read prefix obligation
    follows from concrete Mem facts plus a 29-bit range fact for the carried
    previous-segment address.

    The explicit range premise is the remaining extractor-facing input: the
    table proof no longer assumes address-change seed disjointness. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  apply
    activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed
  intro currentIdx _selectedIdx _currentPriorRows _currentProviderRow _currentLaterRows
    _h_selected_sel _h_split _h_idx_val _h_current_le_selected _h_current_addr_eq
    h_current_addr_change _h_current_read
  exact
    previousSegmentSeedDisjoint_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed h_previous_segment_addr_range
      currentIdx h_current_addr_change

/-- Continuation-seeded selected-primary-read prefix soundness with the
    previous-segment address range derived from segment-global range facts. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
      h_bridge h_ranges h_fixed
      (previous_segment_addr_lt_two_pow_29_of_memTableGeneratedRowsBridge
        h_bridge h_ranges h_segment_ranges h_fixed h_nonempty)

/-- Address-change selected primary reads are justified against their concrete
    prior table prefix from the zero-preloaded Mem-table memory.

    This closes the prior-prefix byte-disjointness premise by deriving
    all-prior address separation from the fixed `SEGMENT_L1` shape and the
    generated address-order constraints. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  exact
    readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_ne_memTableGeneratedRowsBridge
      h_bridge h_ranges idx priorRows providerRow laterRows h_split h_idx_val
      h_sel h_addr_change h_read
      (prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
        h_bridge h_ranges h_fixed idx h_addr_change)

/-- Row-order facts for the concrete mutable-Mem replay projection. This is
    the table-local target that accepted full-execution integration should
    prove from Mem sorting, segment carry, and timestamp range facts.

    The target intentionally does not require `Nodup`: the Mem PIL allows
    equal-timestamp read/read dual rows, and identical duplicate reads are
    harmless for replay because reads do not mutate memory. -/
structure MemReplayRowsOfTableOrderFacts
    (table : Table FGL) : Prop where
  chronologicalRows :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (memReplayRowsOfTable table)

/-- Prefix-read soundness for the concrete mutable-Mem replay projection.
    Proving this is the memory-continuity part of the accepted Mem trace
    bridge, after the replay row list has been identified with the concrete
    table projection. -/
def MemReplayRowsOfTablePrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
    initialMemory (memReplayRowsOfTable table)

/-- Row-order facts for the active mutable-Mem replay projection. This is the
    sound chronological target: inactive selector-gated emissions are not
    replay events.  As above, duplicate read entries are permitted. -/
structure ActiveMemReplayRowsOfTableOrderFacts
    (table : Table FGL) : Prop where
  chronologicalRows :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayRowsOfTable table)

/-- Prefix-read soundness for the active mutable-Mem replay projection. -/
def ActiveMemReplayRowsOfTablePrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
    initialMemory (activeMemReplayRowsOfTable table)

/-- Once the selected-primary-read prefix obligation is proved, the active
    table replay fold supplies prefix-read soundness for the whole projected
    active Mem table. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_primary_reads
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL)
    (h_specs :
      ∀ providerRow, providerRow ∈ table.table →
        ZiskFv.AirsClean.Mem.Spec
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
    (h_primary_read :
      ActiveMemReplayRowsOfTablePrimaryReadPrefixSound initialMemory table) :
    ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table := by
  exact
    ZiskFv.ZiskCircuit.MemTrace.memoryBusRowsPrefixReadSound_of_readWriteSound
      initialMemory (activeMemReplayRowsOfTable table)
      (memoryBusRowsReadWriteSound_activeMemReplayRowsOfTable_of_primary_reads
        initialMemory table h_specs h_primary_read)

/-- The indexed generated-row bridge discharges the row-spec input to the
    active-table prefix theorem, leaving only the selected-primary-read prefix
    obligation. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_primary_read :
      ActiveMemReplayRowsOfTablePrimaryReadPrefixSound initialMemory table) :
    ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_primary_reads
      initialMemory table
      (tableRow_specs_of_memTableGeneratedRowsBridge h_bridge)
      h_primary_read

/-- First-segment specialization of the generated Mem-table prefix-read
    theorem, with initial memory given by the finite zero-preload table memory.

    The additional first-segment input is the constructible segment selector
    needed to rule out the row-0 continuation case. Later continuation segments
    need an initial-memory theorem parameterized by `previous_segment_*`
    instead of this zero-preload specialization. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_firstSegment_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1) :
    ActiveMemReplayRowsOfTablePrefixReadSound
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
        h_bridge
        (activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_firstSegment_memTableGeneratedRowsBridge
          h_bridge h_ranges h_fixed h_first_segment)

/-- Continuation-segment specialization of the generated Mem-table prefix-read
    theorem, with initial memory seeded by `previous_segment_*`.

    The remaining segment-level range input rules out overlap between the
    previous-segment seed entry and address-change zero-valued reads. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29) :
    ActiveMemReplayRowsOfTablePrefixReadSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      h_bridge
      (activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
        h_bridge h_ranges h_fixed h_previous_segment_addr_range)

/-- Continuation-segment active-table prefix-read soundness with the
    previous-segment address range derived from segment-global range facts. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ActiveMemReplayRowsOfTablePrefixReadSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      h_bridge
      (activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
        h_bridge h_ranges h_segment_ranges h_fixed h_nonempty)

/-- Transport table-local replay-row order facts across the concrete row-list
    equality used by the raw accepted Mem extraction path. -/
theorem generatedMemRowOrderFacts_of_memReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = memReplayRowsOfTable table)
    (h_order : MemReplayRowsOfTableOrderFacts table) :
    ZiskFv.AirsClean.Mem.GeneratedMemRowOrderFacts rows := by
  rw [h_rows]
  exact
    { chronologicalRows := h_order.chronologicalRows }

/-- Transport table-local prefix-read soundness across the concrete row-list
    equality used by the raw accepted Mem extraction path. -/
theorem memoryBusRowsPrefixReadSound_of_memReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {initialMemory : Std.ExtHashMap Nat (BitVec 8)}
    (h_rows : rows = memReplayRowsOfTable table)
    (h_prefix : MemReplayRowsOfTablePrefixReadSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      initialMemory rows := by
  rw [h_rows]
  exact h_prefix

/-- Transport table-local active replay-row order facts across the concrete
    row-list equality used by the raw accepted Mem extraction path. -/
theorem generatedMemRowOrderFacts_of_activeMemReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_order : ActiveMemReplayRowsOfTableOrderFacts table) :
    ZiskFv.AirsClean.Mem.GeneratedMemRowOrderFacts rows := by
  rw [h_rows]
  exact
    { chronologicalRows := h_order.chronologicalRows }

/-- Transport table-local active prefix-read soundness across the concrete
    row-list equality used by the raw accepted Mem extraction path. -/
theorem memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {initialMemory : Std.ExtHashMap Nat (BitVec 8)}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_prefix : ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      initialMemory rows := by
  rw [h_rows]
  exact h_prefix

/-- The generated segment selector is boolean on any nonempty generated Mem
    table.

    This projects the `is_first_segment * (1 - is_first_segment) = 0`
    constraint from the row-0 `segment_every_row` bundle. -/
theorem is_first_segment_eq_one_or_zero_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_nonempty : 0 < table.table.length) :
    segment.is_first_segment = 1 ∨ segment.is_first_segment = 0 := by
  let idx0 : Fin table.table.length := ⟨0, h_nonempty⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    simpa [idx0] using (h_bridge.generatedAt idx0).1
  rcases h_segment with
    ⟨h_first_bool, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases mul_eq_zero.mp h_first_bool with h_zero | h_one_sub
  · exact Or.inr h_zero
  · exact Or.inl ((sub_eq_zero.mp h_one_sub).symm)

/-- Construct the accepted replay evidence for a first generated Mem segment
    whose accepted row list is the active replay projection of the concrete
    Mem table.

    This fills the former `AcceptedMemoryReplayEvidence.prefixReadSound`
    obligation from extracted Mem-table constraints. It is still only the
    circuit-side replay object; the Sail timeline fields in
    `MemoryTimelineEvidence` remain the separate whole-execution boundary. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
    { rows := rows
      initialMemory :=
        ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table)
      prefixReadSound :=
        memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
          h_rows
          (activeMemReplayRowsOfTablePrefixReadSound_of_firstSegment_memTableGeneratedRowsBridge
            h_bridge h_ranges h_fixed h_first_segment) }

/-- Construct the accepted replay evidence for a continuation generated Mem
    segment whose accepted row list is the active replay projection of the
    concrete Mem table.

    This is the continuation counterpart of the first-segment constructor above:
    `prefixReadSound` is derived from concrete table facts, with the
    previous-segment carried memory entry used as the initial memory seed. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  { rows := rows
    initialMemory :=
      previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table)
    prefixReadSound :=
      memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
        h_rows
        (activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
          h_bridge h_ranges h_fixed h_previous_segment_addr_range) }

/-- Construct continuation accepted replay evidence with the previous-segment
    address range derived from segment-global Mem range facts.

    This is the constructor shape expected by concrete full-witness integration:
    the remaining obligations are generated-row bridge facts, row range facts,
    segment distance-base range facts, fixed-column shape, and nonempty table
    evidence. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  { rows := rows
    initialMemory :=
      previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table)
    prefixReadSound :=
      memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
        h_rows
        (activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
          h_bridge h_ranges h_segment_ranges h_fixed h_nonempty) }

/-- Construct accepted replay evidence for a generated Mem segment by choosing
    the first-segment or continuation-segment initial memory from the segment
    selector.

    The constructor keeps the circuit-side replay proof local to generated Mem
    table facts. The remaining Sail-timeline fields of `MemoryTimelineEvidence`
    are still the separate residual boundary. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length)
    (h_segment_selector : segment.is_first_segment = 1 ∨ segment.is_first_segment = 0) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  if h_first_segment : segment.is_first_segment = 1 then
      acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge
        h_rows h_bridge h_ranges h_fixed h_first_segment
  else
      have _h_continuation : segment.is_first_segment = 0 := by
        rcases h_segment_selector with h_first | h_continuation
        · exact False.elim (h_first_segment h_first)
        · exact h_continuation
      acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
        h_rows h_bridge h_ranges h_segment_ranges h_fixed h_nonempty

/-- Construct accepted replay evidence for a nonempty generated Mem segment,
    deriving the first/continuation choice from the generated segment selector
    booleanity constraint. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge
    h_rows h_bridge h_ranges h_segment_ranges h_fixed h_nonempty
    (is_first_segment_eq_one_or_zero_of_memTableGeneratedRowsBridge
      h_bridge h_nonempty)

/-- Construct accepted replay evidence from the compact full-witness Mem replay
    bridge.

    The resulting `AcceptedMemoryReplayEvidence.prefixReadSound` is still
    derived from generated Mem AIR facts; the bridge merely collects the
    concrete full-witness/extractor facts that identify those AIR facts with
    the selected table. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_bridge : FullWitnessMemReplayBridge witness rows) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts
    h_bridge.rows_eq
    h_bridge.generatedRows
    h_bridge.rowRanges
    h_bridge.segmentRanges
    h_bridge.fixedColumns
    h_bridge.nonempty

/-- Construct the residual timeline evidence while deriving its accepted-replay
    subobject from the compact full-witness Mem replay bridge.

    The remaining parameters are exactly the intended whole-execution boundary:
    the selected row's split in the accepted trace, its read tag, and the
    byte-local Sail/replay agreement at the selected read. -/
@[reducible]
def memoryTimelineEvidence_of_fullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_bridge : FullWitnessMemReplayBridge witness rows)
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit : rows = priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge h_bridge).initialMemory
          priorRows)
        entry.ptr.toNat) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry :=
  { acceptedReplay := acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge h_bridge
    priorRows := priorRows
    laterRows := laterRows
    traceSplit := by
      by_cases h_first : h_bridge.segment.is_first_segment = 1
      · simpa [
          acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge,
          acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts,
          acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge,
          acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge,
          h_first
        ] using h_traceSplit
      · simpa [
          acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge,
          acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts,
          acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge,
          acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts,
          h_first
        ] using h_traceSplit
    selectedRead := h_selectedRead
    stateBytesAtPrefix := h_stateBytesAtPrefix }

/-- Concrete full-witness source for the global memory-timeline boundary.

    This keeps the circuit-side replay source explicit without mentioning the
    full Clean ensemble in the public compliance theorem signature. The
    evidence object carries generated sidecars for the raw full-witness Mem AIR
    facts that derive the replay bridge and accepted replay object; the
    remaining field is only the residual byte-local Sail timeline fact. -/
structure FullWitnessMemoryTimelineEvidence
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type 2 where
  length : ℕ
  program : Program length
  witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble
  sidecars : FullWitnessMemAirSourceRawSidecars witness
  priorRows : List (Interaction.MemoryBusEntry FGL)
  laterRows : List (Interaction.MemoryBusEntry FGL)
  traceSplit :
    (fullWitnessMemAirSourceOfRawSidecars witness sidecars).rows =
      priorRows ++ entry :: laterRows
  selectedRead :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
      some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry)
  stateBytesAtPrefix :
    ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          ((fullWitnessMemAirSourceOfRawSidecars witness sidecars).replayBridgeOfTraceSplit
            traceSplit)).initialMemory
        priorRows)
      entry.ptr.toNat

namespace FullWitnessMemoryTimelineEvidence

/-- The Mem AIR source selected by the carried raw full-witness facts.
    This is an accessor, not an independent structure field. -/
@[reducible]
noncomputable def memSource
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    FullWitnessMemAirSource evidence.witness :=
  fullWitnessMemAirSourceOfRawSidecars evidence.witness evidence.sidecars

/-- The replay bridge determined by the carried raw full-witness Mem AIR facts.
    This is an accessor, not an independent structure field. -/
@[reducible]
noncomputable def replayBridge
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    FullWitnessMemReplayBridge evidence.witness evidence.memSource.rows :=
  evidence.memSource.replayBridgeOfTraceSplit evidence.traceSplit

/-- The accepted replay object determined by the carried raw full-witness Mem
    AIR facts. This is an accessor, not an independent structure field. -/
@[reducible]
noncomputable def acceptedReplay
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge evidence.replayBridge

end FullWitnessMemoryTimelineEvidence

/-- Construct full-witness timeline evidence from sidecar-form raw Mem AIR
    source facts plus the residual Sail timeline facts.

    This is the generated-sidecar entry point. The sidecars select a concrete
    full-witness Mem AIR source via `fullWitnessMemAirSourceOfRawSidecars`; the
    remaining parameters are still the intended residual boundary: selected
    read tag and byte-local Sail/replay memory agreement. -/
@[reducible]
noncomputable def fullWitnessMemoryTimelineEvidence_of_rawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness h_sidecars).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness h_sidecars).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessMemoryTimelineEvidence state entry :=
  let memSource := fullWitnessMemAirSourceOfRawSidecars witness h_sidecars
  let bridge := memSource.replayBridgeOfTraceSplit h_traceSplit
  let timeline :=
    memoryTimelineEvidence_of_fullWitnessMemReplayBridge
      bridge priorRows laterRows h_traceSplit h_selectedRead
      h_stateBytesAtPrefix
  { length := length
    program := program
    witness := witness
    sidecars := h_sidecars
    priorRows := priorRows
    laterRows := laterRows
    traceSplit := h_traceSplit
    selectedRead := h_selectedRead
    stateBytesAtPrefix := timeline.stateBytesAtPrefix }

/-- Construct full-witness timeline evidence from raw full-witness Mem AIR
    source facts plus the residual Sail timeline facts.

    This is a compatibility constructor for callers that can still prove the
    raw sigma callback directly. It packages those raw facts into sidecar form
    before constructing the timeline evidence, matching the generated sidecar
    boundary stored by `FullWitnessMemoryTimelineEvidence`. -/
@[reducible]
noncomputable def fullWitnessMemoryTimelineEvidence_of_rawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_raw : FullWitnessMemAirSourceRawFacts witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_rawFacts h_raw)).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness
                (fullWitnessMemAirSourceRawSidecars_of_rawFacts h_raw)).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessMemoryTimelineEvidence state entry :=
  fullWitnessMemoryTimelineEvidence_of_rawSidecars
    witness
    (fullWitnessMemAirSourceRawSidecars_of_rawFacts h_raw)
    priorRows
    laterRows
    h_traceSplit
    h_selectedRead
    h_stateBytesAtPrefix

/-- Construct full-witness timeline evidence from ProverData-backed Clean
    assertion/lookup witnesses plus the residual Sail timeline facts.

    This is the preferred generated/full-ensemble entry point when the Mem
    sidecar columns live in the shared `witness.data` map. -/
@[reducible]
noncomputable def fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts h_witnessFacts)).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness
                (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
                  h_witnessFacts)).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessMemoryTimelineEvidence state entry :=
  fullWitnessMemoryTimelineEvidence_of_rawSidecars
    witness
    (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts h_witnessFacts)
    priorRows
    laterRows
    h_traceSplit
    h_selectedRead
    h_stateBytesAtPrefix

/-- Forget the concrete full-witness source, retaining the existing residual
    timeline API consumed by load proofs. -/
@[reducible]
noncomputable def FullWitnessMemoryTimelineEvidence.toMemoryTimelineEvidence
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry :=
  memoryTimelineEvidence_of_fullWitnessMemReplayBridge
    evidence.replayBridge
    evidence.priorRows
    evidence.laterRows
    evidence.traceSplit
    evidence.selectedRead
    evidence.stateBytesAtPrefix

noncomputable instance fullWitnessMemoryTimelineEvidenceCoe
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL} :
    CoeOut
      (FullWitnessMemoryTimelineEvidence state entry)
      (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry) where
  coe := FullWitnessMemoryTimelineEvidence.toMemoryTimelineEvidence

/-- Generated-artifact wrapper for the global memory-timeline boundary.

    The embedded `FullWitnessMemoryTimelineEvidence` is the object consumed by
    load proofs. The extra fields make the generated ProverData sidecar source
    explicit: the stored sidecars must be exactly those packaged from
    `FullWitnessMemAirSourceProverDataWitnessFacts`. -/
structure FullWitnessGeneratedTimelineEvidence
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type 2 where
  evidence : FullWitnessMemoryTimelineEvidence state entry
  witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts evidence.witness
  sidecars_eq :
    evidence.sidecars =
      fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts witnessFacts

namespace FullWitnessGeneratedTimelineEvidence

@[reducible]
noncomputable def toFullWitnessMemoryTimelineEvidence
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessGeneratedTimelineEvidence state entry) :
    FullWitnessMemoryTimelineEvidence state entry :=
  evidence.evidence

@[reducible]
noncomputable def toMemoryTimelineEvidence
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessGeneratedTimelineEvidence state entry) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry :=
  evidence.evidence.toMemoryTimelineEvidence

end FullWitnessGeneratedTimelineEvidence

noncomputable instance fullWitnessGeneratedTimelineEvidenceCoe
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL} :
    CoeOut
      (FullWitnessGeneratedTimelineEvidence state entry)
      (FullWitnessMemoryTimelineEvidence state entry) where
  coe := FullWitnessGeneratedTimelineEvidence.toFullWitnessMemoryTimelineEvidence

noncomputable instance fullWitnessGeneratedTimelineEvidenceMemoryTimelineCoe
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL} :
    CoeOut
      (FullWitnessGeneratedTimelineEvidence state entry)
      (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry) where
  coe := FullWitnessGeneratedTimelineEvidence.toMemoryTimelineEvidence

/-- Construct the generated-artifact memory-timeline boundary directly from
    ProverData-backed Clean assertion/lookup witnesses plus the residual Sail
    timeline facts. -/
@[reducible]
noncomputable def fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts h_witnessFacts)).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness
                (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
                  h_witnessFacts)).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessGeneratedTimelineEvidence state entry where
  evidence :=
    fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts
      witness
      h_witnessFacts
      priorRows
      laterRows
      h_traceSplit
      h_selectedRead
      h_stateBytesAtPrefix
  witnessFacts := h_witnessFacts
  sidecars_eq := rfl

end ZiskFv.AirsClean.FullEnsemble
