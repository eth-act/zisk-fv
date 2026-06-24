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

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- Row extraction for a Mem memory-bus provider interaction in the full
    ensemble. -/
theorem exists_mem_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithMemBus_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a dual-aware Mem memory-bus provider interaction in
    the full ensemble. The selected interaction is either the primary Mem
    provider emission or the pinned `dual_mem = 1` read emission. -/
theorem exists_mem_dual_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    (∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (table.environment row))
    ∨ (∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (table.environment row)) := by
  apply exists_memBus_row_eval_of_pair_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlign memory-bus interaction in the full ensemble. -/
theorem exists_memAlign_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
            - ZiskFv.AirsClean.MemAlign.selAssumeExpr
              ZiskFv.AirsClean.MemAlign.component.rowInputVar)
          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlignByte memory-bus provider interaction in the
    full ensemble. -/
theorem exists_memAlignByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlignReadByte memory-bus provider interaction in
    the full ensemble. -/
theorem exists_memAlignReadByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus
  · exact h_mem

/-! ## Full-ensemble Mem read-replay row projections -/

/-- Public replay-row view of a primary Mem provider row when it is selected
    as a read. The Clean provider interaction carries selector multiplicity,
    but chronological memory replay uses legacy read multiplicity `-1`. -/
@[reducible]
def memPrimaryReadReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusMessage row) (-1) 2

/-- Public replay-row view of a dual Mem provider row. Dual Mem emissions are
    pinned reads, so the replay multiplicity is the legacy read `-1`. -/
@[reducible]
def memDualReadReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusDualMessage row) (-1) 2

/-- Public replay-row view of a primary Mem provider row, preserving the
    read/write polarity carried by `wr`. For boolean `wr`, this maps
    `wr = 0` to legacy read multiplicity `-1` and `wr = 1` to write
    multiplicity `1`. -/
@[reducible]
def memPrimaryReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusMessage row) (2 * row.wr - 1) 2

/-- Replay seed entry carrying the previous segment's final memory state into a
    continuation Mem segment. -/
@[reducible]
def memPreviousSegmentReplayEntry
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) :
    Interaction.MemoryBusEntry FGL :=
  { multiplicity := 1
    as := 2
    ptr := segment.previous_segment_addr * 8
    value_0 := segment.previous_segment_value_0
    value_1 := segment.previous_segment_value_1
    timestamp := segment.previous_segment_step }

/-- Read-replay events contributed by one dual-aware Mem provider row, in
    provider emission order. -/
@[reducible]
def memReadReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row]

/-- Read/write replay events contributed by one dual-aware Mem provider row,
    in provider emission order. The primary event preserves `wr`, while the
    dual event is a pinned read. -/
@[reducible]
def memReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row]

/-- Active read-replay events contributed by one dual-aware Mem provider row.
    Inactive primary/dual emissions do not contribute chronological memory
    replay events. -/
@[reducible]
def activeMemReadReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  (if row.sel = 1 then [memPrimaryReadReplayEntryOfRow row] else [])
    ++
  (if row.sel_dual = 1 then [memDualReadReplayEntryOfRow row] else [])

/-- Active read/write replay events contributed by one dual-aware Mem
    provider row. The primary event preserves `wr`, while the dual event is a
    pinned read. -/
@[reducible]
def activeMemReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  (if row.sel = 1 then [memPrimaryReplayEntryOfRow row] else [])
    ++
  (if row.sel_dual = 1 then [memDualReadReplayEntryOfRow row] else [])

/-- If neither selector is active, a Mem row contributes no active read-replay
    entries. -/
theorem activeMemReadReplayEntriesOfRow_eq_nil_of_inactive
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReadReplayEntriesOfRow row = [] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- If neither selector is active, a Mem row contributes no active
    read/write replay entries. -/
theorem activeMemReplayEntriesOfRow_eq_nil_of_inactive
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReplayEntriesOfRow row = [] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A primary-only selected row contributes exactly its primary read entry to
    the active read-replay surface. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A primary-only selected row contributes exactly its primary
    polarity-preserving entry to the active read/write replay surface. -/
theorem activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A dual-only selected row contributes exactly its dual read entry to the
    active read-replay surface. -/
theorem activeMemReadReplayEntriesOfRow_eq_dual_of_not_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memDualReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A dual-only selected row contributes exactly its dual read entry to the
    active read/write replay surface. -/
theorem activeMemReplayEntriesOfRow_eq_dual_of_not_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memDualReadReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- When both selectors are active, active read-replay emission is primary
    first and then dual. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- When both selectors are active, active read/write replay emission is
    primary first and then dual. -/
theorem activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- Under the generated per-row Mem spec, selecting the dual read emission
    forces the primary selector too, so active read-replay emission is
    primary first and then the pinned dual read. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_dual_of_spec_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  exact activeMemReadReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual

/-- Under the generated per-row Mem spec, selecting the dual read emission
    forces the primary selector too, so active read/write replay emission is
    primary first and then the pinned dual read. -/
theorem activeMemReplayEntriesOfRow_eq_primary_dual_of_spec_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  exact activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual

/-- Any active read/write replay entry from a Mem row is either that row's
    primary polarity-preserving entry or its pinned dual-read entry. -/
theorem activeMemReplayEntriesOfRow_mem_eq_primary_or_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_entry : entry ∈ activeMemReplayEntriesOfRow row) :
    entry = memPrimaryReplayEntryOfRow row
      ∨ entry = memDualReadReplayEntryOfRow row := by
  unfold activeMemReplayEntriesOfRow at h_entry
  by_cases h_sel : row.sel = 1
  · by_cases h_sel_dual : row.sel_dual = 1
    · simp [h_sel, h_sel_dual] at h_entry
      exact h_entry
    · simp [h_sel, h_sel_dual] at h_entry
      exact Or.inl h_entry
  · by_cases h_sel_dual : row.sel_dual = 1
    · simp [h_sel, h_sel_dual] at h_entry
      exact Or.inr h_entry
    · simp [h_sel, h_sel_dual] at h_entry

/-- A selected primary+dual row is chronologically ordered when the primary
    timestamp is no later than the pinned dual-read timestamp. -/
theorem activeMemReplayEntriesOfRow_chronological_of_sel_of_sel_dual_of_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_le : row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    h_sel h_sel_dual]
  simpa [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological,
    memPrimaryReplayEntryOfRow, memDualReadReplayEntryOfRow,
    ZiskFv.AirsClean.Mem.memBusMessage,
    ZiskFv.AirsClean.Mem.memBusDualMessage] using h_step_le

/-- Under the generated per-row Mem spec, a selected dual row is locally
    chronological when the generated dual-step range check supplies
    `step <= step_dual`. -/
theorem activeMemReplayEntriesOfRow_chronological_of_spec_of_sel_dual_of_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_le : row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  exact activeMemReplayEntriesOfRow_chronological_of_sel_of_sel_dual_of_step_le
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual h_step_le

/-- Under the generated per-row Mem spec, local active replay emissions are
    chronological once any selected dual emission is known to have
    `step <= step_dual`. Rows with no selected dual emit zero or one active
    replay entry, so they are chronological without a timestamp comparison. -/
theorem activeMemReplayEntriesOfRow_chronological_of_spec_of_dual_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_step_le_of_dual :
      row.sel_dual = 1 → row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec row h_spec with
    h_sel_dual_zero | h_sel_dual_one
  · rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec row h_spec with
      h_sel_zero | h_sel_one
    · have h_sel_ne : row.sel ≠ 1 := by
        simp [h_sel_zero]
      have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
        h_sel_ne h_sel_dual_ne]
      simp [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological]
    · have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
        h_sel_one h_sel_dual_ne]
      simp [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological]
  · exact activeMemReplayEntriesOfRow_chronological_of_spec_of_sel_dual_of_step_le
      h_spec h_sel_dual_one (h_step_le_of_dual h_sel_dual_one)

/-- A selected primary+dual row has no duplicate replay entries when its
    primary and dual timestamps are distinct. PIL allows equality for
    read-read dual rows, so this lemma intentionally records the extra
    condition rather than hiding it. -/
theorem activeMemReplayEntriesOfRow_nodup_of_sel_of_sel_dual_of_step_ne
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_ne : row.step ≠ row.step_dual) :
    (activeMemReplayEntriesOfRow row).Nodup := by
  rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    h_sel h_sel_dual]
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false,
    not_false_eq_true]
  constructor
  · intro h_eq
    have h_ts :
        (memPrimaryReplayEntryOfRow row).timestamp =
          (memDualReadReplayEntryOfRow row).timestamp := by
      rw [h_eq]
    simp at h_ts
    exact h_step_ne h_ts
  · simp

/-- Primary replay entries from different 29-bit internal Mem addresses have
    disjoint eight-byte byte-address ranges after the provider `addr * 8`
    pointer conversion. -/
theorem memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
    {left right : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_left_range : left.addr.val < 2 ^ 29)
    (h_right_range : right.addr.val < 2 ^ 29)
    (h_addr_ne : left.addr ≠ right.addr) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow left) (memPrimaryReplayEntryOfRow right) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
  intro i j hi hj h_eq
  have h_left_ptr :
      (memPrimaryReplayEntryOfRow left).ptr.toNat = left.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_left_range]
  have h_right_ptr :
      (memPrimaryReplayEntryOfRow right).ptr.toNat = right.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_right_range]
  rw [h_left_ptr, h_right_ptr] at h_eq
  have h_addr_val_ne : left.addr.val ≠ right.addr.val := by
    intro h_val
    exact h_addr_ne (Fin.ext h_val)
  rcases lt_trichotomy left.addr.val right.addr.val with h_lt | h_eq_addr | h_gt
  · have h_le : left.addr.val + 1 ≤ right.addr.val := Nat.succ_le_of_lt h_lt
    have h_bound_left : left.addr.val * 8 + i < right.addr.val * 8 := by
      have hi_le : i ≤ 7 := by omega
      nlinarith
    have h_bound_right : right.addr.val * 8 ≤ right.addr.val * 8 + j := by
      omega
    omega
  · exact h_addr_val_ne h_eq_addr
  · have h_le : right.addr.val + 1 ≤ left.addr.val := Nat.succ_le_of_lt h_gt
    have h_bound_right : right.addr.val * 8 + j < left.addr.val * 8 := by
      have hj_le : j ≤ 7 := by omega
      nlinarith
    have h_bound_left : left.addr.val * 8 ≤ left.addr.val * 8 + i := by
      omega
    omega

/-- A selected primary entry is byte-disjoint from another row's dual read
    entry when their internal Mem addresses differ. -/
theorem memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
    {left right : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_left_range : left.addr.val < 2 ^ 29)
    (h_right_range : right.addr.val < 2 ^ 29)
    (h_addr_ne : left.addr ≠ right.addr) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow left) (memDualReadReplayEntryOfRow right) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
  intro i j hi hj h_eq
  have h_left_ptr :
      (memPrimaryReplayEntryOfRow left).ptr.toNat = left.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_left_range]
  have h_right_ptr :
      (memDualReadReplayEntryOfRow right).ptr.toNat = right.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_right_range]
  rw [h_left_ptr, h_right_ptr] at h_eq
  have h_addr_val_ne : left.addr.val ≠ right.addr.val := by
    intro h_val
    exact h_addr_ne (Fin.ext h_val)
  rcases lt_trichotomy left.addr.val right.addr.val with h_lt | h_eq_addr | h_gt
  · have h_le : left.addr.val + 1 ≤ right.addr.val := Nat.succ_le_of_lt h_lt
    have h_bound_left : left.addr.val * 8 + i < right.addr.val * 8 := by
      have hi_le : i ≤ 7 := by omega
      nlinarith
    have h_bound_right : right.addr.val * 8 ≤ right.addr.val * 8 + j := by
      omega
    omega
  · exact h_addr_val_ne h_eq_addr
  · have h_le : right.addr.val + 1 ≤ left.addr.val := Nat.succ_le_of_lt h_gt
    have h_bound_right : right.addr.val * 8 + j < left.addr.val * 8 := by
      have hj_le : j ≤ 7 := by omega
      nlinarith
    have h_bound_left : left.addr.val * 8 ≤ left.addr.val * 8 + i := by
      omega
    omega

/-- A selected primary entry is byte-disjoint from the previous-segment seed
    entry when their internal Mem addresses differ. -/
theorem memoryBusEntryByteDisjoint_primary_previousSegment_of_addr_ne
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    (h_row_range : row.addr.val < 2 ^ 29)
    (h_segment_range : segment.previous_segment_addr.val < 2 ^ 29)
    (h_addr_ne : row.addr ≠ segment.previous_segment_addr) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow row) (memPreviousSegmentReplayEntry segment) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
  intro i j hi hj h_eq
  have h_row_ptr :
      (memPrimaryReplayEntryOfRow row).ptr.toNat = row.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_row_range]
  have h_segment_ptr :
      (memPreviousSegmentReplayEntry segment).ptr.toNat =
        segment.previous_segment_addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_segment_range]
  rw [h_row_ptr, h_segment_ptr] at h_eq
  have h_addr_val_ne : row.addr.val ≠ segment.previous_segment_addr.val := by
    intro h_val
    exact h_addr_ne (Fin.ext h_val)
  rcases lt_trichotomy row.addr.val segment.previous_segment_addr.val with
    h_lt | h_eq_addr | h_gt
  · have h_le : row.addr.val + 1 ≤ segment.previous_segment_addr.val :=
      Nat.succ_le_of_lt h_lt
    have h_bound_left : row.addr.val * 8 + i < segment.previous_segment_addr.val * 8 := by
      have hi_le : i ≤ 7 := by omega
      nlinarith
    have h_bound_right :
        segment.previous_segment_addr.val * 8 ≤
          segment.previous_segment_addr.val * 8 + j := by
      omega
    omega
  · exact h_addr_val_ne h_eq_addr
  · have h_le : segment.previous_segment_addr.val + 1 ≤ row.addr.val :=
      Nat.succ_le_of_lt h_gt
    have h_bound_right :
        segment.previous_segment_addr.val * 8 + j < row.addr.val * 8 := by
      have hj_le : j ≤ 7 := by omega
      nlinarith
    have h_bound_left : row.addr.val * 8 ≤ row.addr.val * 8 + i := by
      omega
    omega

/-- Primary-read replay rows projected from every row of a Mem table. -/
@[reducible]
def memPrimaryReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Dual-read replay rows projected from every row of a Mem table. -/
@[reducible]
def memDualReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Read-replay row surface exposed by a dual-aware Mem table.

    Unlike the legacy compatibility projections above, this list is shaped in
    provider emission order: for each concrete Mem table row, primary comes
    before dual. Chronological ordering and read/write soundness remain
    separate global trace obligations. -/
@[reducible]
def memReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    memReadReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Primary replay rows projected from every Mem table row, preserving
    read/write polarity. -/
@[reducible]
def memPrimaryReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Full replay-row surface exposed by a dual-aware Mem table.

    Events are projected in provider emission order: primary first, preserving
    read/write polarity, then the pinned dual read for the same provider row. -/
@[reducible]
def memReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    memReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Active read-replay rows projected from selected emissions of a Mem table.
    This is the replay surface accepted-trace extraction should use when
    proving chronological memory soundness from concrete Mem rows. -/
@[reducible]
def activeMemReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    activeMemReadReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Active read/write replay rows projected from selected emissions of a Mem
    table. Inactive rows are omitted instead of replayed as spurious memory
    events. -/
@[reducible]
def activeMemReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    activeMemReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- If the active replay projection is nonempty, then the underlying concrete
    Mem table is nonempty. -/
theorem table_nonempty_of_activeMemReplayRowsOfTable_nonempty
    {table : Table FGL}
    (h_rows : 0 < (activeMemReplayRowsOfTable table).length) :
    0 < table.table.length := by
  cases h_table : table.table with
  | nil =>
      simp [activeMemReplayRowsOfTable, h_table] at h_rows
  | cons _ _ =>
      simp

/-- The selected-entry split used by timeline evidence proves that the active
    replay projection is nonempty. -/
theorem activeMemReplayRowsOfTable_nonempty_of_split
    {table : Table FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_split :
      activeMemReplayRowsOfTable table = priorRows ++ entry :: laterRows) :
    0 < (activeMemReplayRowsOfTable table).length := by
  rw [h_split]
  simp


end ZiskFv.AirsClean.FullEnsemble
