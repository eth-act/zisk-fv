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
import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- The projected read-replay rows of a concrete Mem table are embedded in
    the accepted chronological memory-bus row trace. Proving this embedding
    is the global AIR/Main/Mem integration obligation; selected-row coverage
    can then be discharged from the table-local projection lemmas below. -/
def MemReadReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ memReadReplayRowsOfTable table → entry ∈ rows

/-- The projected read/write replay rows of a concrete Mem table are embedded
    in the accepted chronological memory-bus row trace. This is the stronger
    table-level embedding needed by global memory replay: writes must be
    present in the chronological trace so store replay can update memory. -/
def MemReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ memReplayRowsOfTable table → entry ∈ rows

/-- Active read/write replay rows of a concrete Mem table are embedded in the
    accepted chronological memory-bus row trace. -/
def ActiveMemReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ activeMemReplayRowsOfTable table → entry ∈ rows

/-- If the accepted chronological row list is definitionally supplied by the
    concrete mutable-Mem table replay projection, then all projected replay
    rows are embedded in that trace. This is the structural projection lemma
    used before proving the harder chronological/replay facts. -/
theorem memReplayRowsEmbeddedInTrace_of_rows_eq
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = memReplayRowsOfTable table) :
    MemReplayRowsEmbeddedInTrace table rows := by
  intro entry h_entry
  rw [h_rows]
  exact h_entry

/-- If the accepted chronological row list is definitionally supplied by the
    active mutable-Mem table replay projection, then all active projected
    replay rows are embedded in that trace. -/
theorem activeMemReplayRowsEmbeddedInTrace_of_rows_eq
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = activeMemReplayRowsOfTable table) :
    ActiveMemReplayRowsEmbeddedInTrace table rows := by
  intro entry h_entry
  rw [h_rows]
  exact h_entry

/-- Witness-level embedding obligation for mutable Mem tables. Accepted
    full-execution integration should prove this from the chronological
    AIR/Main/Mem trace: every dual-aware mutable Mem table in the full
    ensemble witness has its projected read-replay rows embedded in the
    accepted chronological memory row list. -/
def MutableMemReadReplayRowsEmbeddedInTrace
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
      MemReadReplayRowsEmbeddedInTrace table rows

/-- Witness-level embedding obligation for all mutable-Mem replay rows,
    including primary writes. This is the trace/table projection needed before
    accepted full execution can prove chronological memory replay, while the
    older read-only embedding remains available for selected-load coverage. -/
def MutableMemReplayRowsEmbeddedInTrace
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
      MemReplayRowsEmbeddedInTrace table rows

/-- A primary read projection is the polarity-preserving primary replay row
    when the concrete Mem row is a read. -/
theorem memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 0) :
    memPrimaryReadReplayEntryOfRow row = memPrimaryReplayEntryOfRow row := by
  simp [memPrimaryReadReplayEntryOfRow, memPrimaryReplayEntryOfRow, h_wr]

/-- A primary polarity-preserving replay row is a legacy read row when
    `wr = 0`. -/
theorem memoryBusTraceEventOfRow_memPrimaryReplayEntryOfRow_read_of_wr_zero
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 0) :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow
      (memPrimaryReplayEntryOfRow row) =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read
          (memPrimaryReplayEntryOfRow row)) := by
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow,
    memPrimaryReplayEntryOfRow, h_wr]

/-- A primary polarity-preserving replay row is a legacy write row when
    `wr = 1`. -/
theorem memoryBusTraceEventOfRow_memPrimaryReplayEntryOfRow_write_of_wr_one
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow
      (memPrimaryReplayEntryOfRow row) =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.write
          (memPrimaryReplayEntryOfRow row)) := by
  have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
    decide
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow,
    memPrimaryReplayEntryOfRow, h_wr, h_one_ne_neg_one]

/-- On primary Mem writes, the raw-row replay step is exactly the store
    update carried by the polarity-preserving primary replay entry. -/
theorem replayMemoryAfterBusRow_memPrimaryReplayEntryOfRow_of_wr_one
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow
      mem (memPrimaryReplayEntryOfRow row) =
        ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent mem
          (ZiskFv.ZiskCircuit.MemTrace.storeEventOfEntry
            (memPrimaryReplayEntryOfRow row)) := by
  simp [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, h_wr]

/-- A concrete Mem table row contributes its primary polarity-preserving
    projection to the table's full replay-row surface. -/
theorem mem_primary_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReplayRowsOfTable table := by
  unfold memReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its primary
    polarity-preserving projection to the table's active replay-row surface. -/
theorem active_mem_primary_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1) :
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReplayRowsOfTable table := by
  unfold activeMemReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReplayEntriesOfRow, h_sel]⟩

/-- A concrete Mem table row contributes its dual read projection to the
    table's full replay-row surface. -/
theorem mem_dual_read_replay_entry_mem_of_replay_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReplayRowsOfTable table := by
  unfold memReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its dual read projection to
    the table's active replay-row surface. -/
theorem active_mem_dual_read_replay_entry_mem_of_replay_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReplayRowsOfTable table := by
  unfold activeMemReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReplayEntriesOfRow, h_sel_dual]⟩

/-- The all-replay-row embedding implies read-only embedding for selected
    primary reads, once the selected Mem row is known to be a read. -/
theorem mem_primary_read_replay_entry_mem_of_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows := by
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (mem_primary_replay_entry_mem_of_table_row h_row)

/-- Active replay-row embedding implies read-only embedding for selected
    primary reads, once the selected Mem row is known to be a read and active. -/
theorem mem_primary_read_replay_entry_mem_of_active_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows := by
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (active_mem_primary_replay_entry_mem_of_table_row h_row h_sel)

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace from active replay-row embedding, provided the
    concrete Mem row is selected and is a read. -/
theorem mem_primary_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact
    mem_primary_read_replay_entry_mem_of_active_replay_embedded_table_row
      h_embedded h_row h_sel h_wr

/-- The all-replay-row embedding directly implies dual-read embedding. -/
theorem mem_dual_read_replay_entry_mem_of_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows :=
  h_embedded _
    (mem_dual_read_replay_entry_mem_of_replay_table_row h_row)

/-- Active replay-row embedding directly implies selected dual-read
    embedding. -/
theorem mem_dual_read_replay_entry_mem_of_active_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows :=
  h_embedded _
    (active_mem_dual_read_replay_entry_mem_of_replay_table_row
      h_row h_sel_dual)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace from active replay-row embedding, provided the
    concrete dual emission is selected. -/
theorem mem_dual_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact
    mem_dual_read_replay_entry_mem_of_active_replay_embedded_table_row
      h_embedded h_row h_sel_dual

/-- A concrete Mem table row contributes its primary read projection to the
    table's read-replay row surface. -/
theorem mem_primary_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReadReplayRowsOfTable table := by
  unfold memReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReadReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its primary read projection
    to the table's active read-replay row surface. -/
theorem active_mem_primary_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReadReplayRowsOfTable table := by
  unfold activeMemReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReadReplayEntriesOfRow, h_sel]⟩

/-- A concrete Mem table row contributes its dual read projection to the
    table's read-replay row surface. -/
theorem mem_dual_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReadReplayRowsOfTable table := by
  unfold memReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReadReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its dual read projection to
    the table's active read-replay row surface. -/
theorem active_mem_dual_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReadReplayRowsOfTable table := by
  unfold activeMemReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReadReplayEntriesOfRow, h_sel_dual]⟩

/-- If a selected legacy memory row matches a concrete primary Mem row's
    read projection, then it is covered by the table's read-replay rows. -/
theorem mem_primary_read_replay_entry_mem_of_table_row_match
    {table : Table FGL} {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ memReadReplayRowsOfTable table := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact mem_primary_read_replay_entry_mem_of_table_row h_row

/-- If a selected legacy memory row matches a concrete dual Mem row's read
    projection, then it is covered by the table's read-replay rows. -/
theorem mem_dual_read_replay_entry_mem_of_table_row_match
    {table : Table FGL} {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ memReadReplayRowsOfTable table := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact mem_dual_read_replay_entry_mem_of_table_row h_row

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace once the table's projected replay rows are
    embedded in that trace. -/
theorem mem_primary_read_replay_entry_mem_of_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReadReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows :=
  h_embedded entry
    (mem_primary_read_replay_entry_mem_of_table_row_match h_row h_match)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace once the table's projected replay rows are
    embedded in that trace. -/
theorem mem_dual_read_replay_entry_mem_of_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReadReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows :=
  h_embedded entry
    (mem_dual_read_replay_entry_mem_of_table_row_match h_row h_match)

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace from the stronger replay-row embedding, provided
    the concrete Mem row is a read. This is the selected-load adapter needed
    to avoid requiring every primary Mem row, including writes, to appear in
    the accepted trace with read polarity. -/
theorem mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (mem_primary_replay_entry_mem_of_table_row h_row)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace from the stronger replay-row embedding. Dual Mem
    projections are always read events in the replay surface. -/
theorem mem_dual_read_replay_entry_mem_of_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact h_embedded _
    (mem_dual_read_replay_entry_mem_of_replay_table_row h_row)


end ZiskFv.AirsClean.FullEnsemble
