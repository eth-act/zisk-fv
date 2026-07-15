import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections
import ZiskFv.AirsClean.Main.CrossRow

/-!
# Main cross-row PC handshake: trace-level transition derivation

`AcceptedZiskTrace.mainTransition_to_next_pc` derives the per-row next-PC
handshake (`pc_handshake_with_next_pc`) at a within-segment Main row directly
from the accepted trace's `transitions_hold` certificate — the in-circuit
`Air.Flat.Component.transition` (= `pcHandshakeBetween`, `main.pil:409-410`)
that ZisK's Main AIR enforces on every consecutive row pair. This replaces the
per-opcode caller-supplied `h_nextPC_matches` promise with a derivation from the
accepted trace.

`MainTableGeneratedFixedColumnFacts` is the Main analog of the Mem precedent
`MemTableGeneratedFixedColumnFacts` (`Balance/TableProjections.lean`): the
fixed-column constructibility obligation for `SEGMENT_L1 = [1,0,0,...]`
(`main.pil:19`), in the `main_height` epistemic class — PIL-faithful and
constructible (a real ZisK Main witness genuinely carries this deterministic
column). Its `segment_l1_succ` accessor yields the non-boundary fact
`segment_l1 (i + 1) = 0` that `mainTransition_to_next_pc` consumes.
-/

namespace ZiskFv.Compliance

open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open Air.Flat

/-- Bridge: the Clean per-row input of the unified Main component at an in-range
    concrete row equals the named-column `mainTableRowAtOrZero` projection. The
    Clean `rowInput` is `eval … rowInputVar` (`eval_varFromOffset_valueFromOffset`),
    which `mainTableRowAtOrZero_get` identifies with the projection on in-range
    rows. -/
theorem rowInput_eq_mainTableRowAtOrZero
    {length : ℕ} (program : Program length) (table : Table FGL)
    (j : ℕ) (h : j < table.table.length) :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInput
        (table.environment (table.table[j]'h)) =
      mainTableRowAtOrZero program table j := by
  have hget : (table.table[j]'h) = table.table.get ⟨j, h⟩ := rfl
  rw [hget, mainTableRowAtOrZero_get program table ⟨j, h⟩]
  simp only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar,
    eval_varFromOffset_valueFromOffset]

/-- The indexed effective-row environment projects to the corresponding Main row. -/
private theorem rowInputAt_eq_mainTableRowAtOrZero
    {length : ℕ} (program : Program length) (table : Table FGL)
    (index : Fin table.length) :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInput
        (table.environmentAt index) =
      mainTableRowAtOrZero program table index.val := by
  have h_index : index.val < table.table.length := by
    simpa only [Table.table_length] using index.isLt
  change (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInput
      (table.environment (table.table[index.val]'h_index)) =
    mainTableRowAtOrZero program table index.val
  exact rowInput_eq_mainTableRowAtOrZero program table index.val h_index

/-- The saturated predecessor environment projects to the preceding effective Main row. -/
private theorem rowInputPrevious_eq_mainTableRowAtOrZero
    {length : ℕ} (program : Program length) (table : Table FGL)
    (index : Fin table.length) (h_positive : 0 < index.val) :
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInput
        (table.previousEnvironment index) =
      mainTableRowAtOrZero program table (index.val - 1) := by
  have h_index : index.val - 1 < table.table.length := by
    have h_raw : index.val - 1 < table.length := by omega
    simpa only [Table.table_length] using h_raw
  change (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInput
      (table.environment (table.table[index.val - 1]'h_index)) =
    mainTableRowAtOrZero program table (index.val - 1)
  exact rowInput_eq_mainTableRowAtOrZero program table (index.val - 1) h_index

/-- **Trace-level next-PC handshake.** From the accepted trace's in-circuit
    PC-handshake transition certificate (`transitions_hold`), at a within-segment
    Main row `i + 1` (`segment_l1 (i + 1) = 0`), the named-column Main view
    satisfies the next-PC specialization form `pc_handshake_with_next_pc` at row
    `i`, with next-row pc cell `pc (i + 1)`.

    This is the core derivation that lets the trace-level export discharge the
    per-opcode `h_nextPC_matches` promise from the accepted trace rather than
    carrying it as a caller-supplied hypothesis. -/
theorem AcceptedZiskTrace.mainTransition_to_next_pc
    (trace : AcceptedZiskTrace n) (i : ℕ)
    (h_idx : i + 1 < trace.mainTable.table.length)
    (h_seg :
      (mainOfTable trace.program trace.mainTable).segment_l1 (i + 1) = 0) :
    ZiskFv.Airs.Main.pc_handshake_with_next_pc
      (mainOfTable trace.program trace.mainTable) i
      ((mainOfTable trace.program trace.mainTable).pc (i + 1)) := by
  have h_transition_index_lt : i + 1 < trace.mainTable.length := by
    simpa only [Table.length, Table.table_length] using h_idx
  let transitionIndex : Fin trace.mainTable.length := ⟨i + 1, h_transition_index_lt⟩
  have h_trans := trace.transitions_hold trace.mainTable trace.mainTable_mem transitionIndex
  have hcomp : trace.mainTable.component
      = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program :=
    trace.mainTable_component
  rw [hcomp] at h_trans
  change ZiskFv.AirsClean.Main.pcHandshakeTransition transitionIndex.val
    (trace.mainTable.previousEnvironment transitionIndex)
    (trace.mainTable.environmentAt transitionIndex) at h_trans
  have h_transition : ZiskFv.AirsClean.Main.pcHandshakeBetween
      ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInput
        (trace.mainTable.previousEnvironment transitionIndex))
      ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInput
        (trace.mainTable.environmentAt transitionIndex)) := by
    simpa only [ZiskFv.AirsClean.Main.pcHandshakeTransition, Air.Flat.Component.rowInput,
      Air.Flat.Component.rowInputVar, eval_varFromOffset_valueFromOffset] using h_trans
  have h_previous := rowInputPrevious_eq_mainTableRowAtOrZero trace.program trace.mainTable
    transitionIndex (by simp [transitionIndex])
  have h_current := rowInputAt_eq_mainTableRowAtOrZero trace.program trace.mainTable
    transitionIndex
  rw [h_previous, h_current] at h_transition
  have h_trans_between : ZiskFv.AirsClean.Main.pcHandshakeBetween
      (mainTableRowAtOrZero trace.program trace.mainTable i)
      (mainTableRowAtOrZero trace.program trace.mainTable (i + 1)) := by
    simpa [transitionIndex] using h_transition
  simp only [ZiskFv.AirsClean.Main.pcHandshakeBetween] at h_trans_between
  have h_at :
      ZiskFv.AirsClean.Main.pc_handshake_at
        (mainOfTable trace.program trace.mainTable) (i + 1) := by
    simp only [ZiskFv.AirsClean.Main.pc_handshake_at, mainOfTable_segment_l1, mainOfTable_pc,
      mainOfTable_set_pc, mainOfTable_c_0, mainOfTable_jmp_offset1, mainOfTable_jmp_offset2,
      mainOfTable_flag, Nat.add_sub_cancel]
    exact h_trans_between
  rw [ZiskFv.AirsClean.Main.pc_handshake_at_iff_v1] at h_at
  exact ZiskFv.Airs.Main.pc_handshake_to_next_pc
    (mainOfTable trace.program trace.mainTable) i h_seg h_at

/-- Fixed-column facts for the Main execution table's `SEGMENT_L1` column
    (`main.pil:19`: `col fixed SEGMENT_L1 = [1,0,0,...]`). The first row is a
    segment boundary; every later row is within-segment.

    **Faithful Main analog of `MemTableGeneratedFixedColumnFacts`** (the Mem
    precedent in `Balance/TableProjections.lean`): the canonical
    component-owned fixed schema derives the full `[1,0,...]` shape. Keeping
    both the boundary row and the within-segment rows makes the fixed-column
    model explicit instead of asserting a bare `segment_l1 = 0` divorced from
    the PIL column. -/
structure MainTableGeneratedFixedColumnFacts
    {length : ℕ} (program : Program length) (table : Table FGL) : Prop where
  segmentL1_first :
    0 < table.table.length → (mainOfTable program table).segment_l1 0 = 1
  segmentL1_nonfirst :
    ∀ idx : Fin table.table.length, 0 < idx.val →
      (mainOfTable program table).segment_l1 idx.val = 0

/-- The non-boundary fact `segment_l1 (i + 1) = 0` consumed by
    `mainTransition_to_next_pc`: every `i + 1 < length` row is positive, hence
    within-segment by the fixed `SEGMENT_L1 = [1,0,...]` column. -/
theorem MainTableGeneratedFixedColumnFacts.segment_l1_succ
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_fixed : MainTableGeneratedFixedColumnFacts program table)
    (i : ℕ) (h_idx : i + 1 < table.table.length) :
    (mainOfTable program table).segment_l1 (i + 1) = 0 :=
  h_fixed.segmentL1_nonfirst ⟨i + 1, h_idx⟩ (Nat.succ_pos i)

/-- Derive the Main `SEGMENT_L1` shape from the canonical component-owned
    indexed fixed schema. The table carrier's intrinsic `fixed_domain` rules
    out the periodic wrap before a concrete table row is observed. -/
theorem mainTableGeneratedFixedColumnFacts_of_component_fixedColumns
    {length : Nat} (program : Program length) (table : Table FGL)
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) :
    MainTableGeneratedFixedColumnFacts program table := by
  cases table with
  | mk component rawRows data raw_uniform_width fixed_domain =>
    change component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program at h_component
    subst component
    let table : Table FGL :=
      { component := ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
        rawRows := rawRows
        data := data
        raw_uniform_width := raw_uniform_width
        fixed_domain := fixed_domain }
    change MainTableGeneratedFixedColumnFacts program table
    have h_columns : table.component.fixedColumns = some ZiskFv.AirsClean.Main.mainFixedColumns := by
      rfl
    refine ⟨?_, ?_⟩
    · intro h_nonempty
      rw [mainOfTable_segment_l1]
      change (mainTableRowAtOrZero program table 0).core.segment_l1 = 1
      rw [mainTableRowAtOrZero_segment_l1_eq_fixedAt program table 0 h_nonempty (by rfl)]
      rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
      exact ZiskFv.AirsClean.Main.mainFixedColumns_segment_l1_first
    · intro idx h_positive
      rw [mainOfTable_segment_l1]
      change (mainTableRowAtOrZero program table idx.val).core.segment_l1 = 0
      rw [mainTableRowAtOrZero_segment_l1_eq_fixedAt program table idx.val idx.isLt (by rfl)]
      rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
      have h_raw_index : idx.val < table.length := by
        simpa only [Table.table_length] using idx.isLt
      have h_capacity : idx.val < ZiskFv.AirsClean.Main.mainFixedColumns.capacity :=
        Table.index_lt_fixed_capacity table ZiskFv.AirsClean.Main.mainFixedColumns h_columns
          ⟨idx.val, h_raw_index⟩
      have h_capacity' : idx.val < ZiskFv.AirsClean.Main.mainFixedCapacity := by
        simpa [ZiskFv.AirsClean.Main.mainFixedColumns] using h_capacity
      exact ZiskFv.AirsClean.Main.mainFixedColumns_segment_l1_nonfirst idx.val h_positive h_capacity'

/-- `MainTableGeneratedFixedColumnFacts` for the **derived** Main table, read
    from its component-owned indexed fixed schema. The per-opcode next-PC
    discharges share this derived fact through `trace.mainTable_fixed` rather
    than carrying a per-arm binder. -/
theorem AcceptedZiskTrace.mainTable_fixed (trace : AcceptedZiskTrace n) :
    MainTableGeneratedFixedColumnFacts trace.program trace.mainTable :=
  mainTableGeneratedFixedColumnFacts_of_component_fixedColumns trace.program trace.mainTable
    trace.mainTable_component

end ZiskFv.Compliance
