import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance

/-!
# Derived Main-table accessor

Selecting the Main execution table out of the witness is **derived**, not
assumed: `exists_main_table_of_fullRv64im_witness` already produces one from
`trace.witness` alone. These accessors expose that choice so it no longer needs
to be supplied as `SailTrace` fields. The one genuine external assumption
about the Main table — its row count — lives on `AcceptedZiskTrace.main_height`;
`mainTable_index` below specializes it to the derived `mainTable`.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- The Main execution table selected from the witness. **Non-reducible** so it
    behaves opaquely, exactly like the former `SailTrace.mainTable` struct
    field: proofs that treat the Main table abstractly keep working unchanged. -/
noncomputable def AcceptedZiskTrace.mainTable (trace : AcceptedZiskTrace n) : Air.Flat.Table FGL :=
  (ZiskFv.AirsClean.FullEnsemble.exists_main_table_of_fullRv64im_witness
    trace.witness).choose

/-- The derived Main table really occurs in the witness. -/
theorem AcceptedZiskTrace.mainTable_mem (trace : AcceptedZiskTrace n) :
    trace.mainTable ∈ trace.witness.allTables :=
  (ZiskFv.AirsClean.FullEnsemble.exists_main_table_of_fullRv64im_witness
    trace.witness).choose_spec.1

/-- The derived Main table really is the Main component for this program. -/
theorem AcceptedZiskTrace.mainTable_component (trace : AcceptedZiskTrace n) :
    trace.mainTable.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.programLength trace.program :=
  (ZiskFv.AirsClean.FullEnsemble.exists_main_table_of_fullRv64im_witness
    trace.witness).choose_spec.2

/-- The derived Main table has a row for every executed step — `main_height`
    specialized to `mainTable` via its membership and component facts. -/
theorem AcceptedZiskTrace.mainTable_index (trace : AcceptedZiskTrace n) :
    ∀ i : Fin trace.numInstructions, i.val < trace.mainTable.table.length :=
  trace.main_height trace.mainTable trace.mainTable_mem trace.mainTable_component

/-- An in-range canonical Main row obtains `SEGMENT_L1` from the Main
    component's indexed fixed schema. -/
theorem mainTableRowAtOrZero_segment_l1_eq_fixedAt
    {length : Nat} (program : Program length) (table : Table FGL) (index : Nat)
    (h_index : index < table.table.length)
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) :
    (mainTableRowAtOrZero program table index).core.segment_l1 = table.fixedAt 0 index := by
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
    change (mainTableRowAtOrZero program table index).core.segment_l1 = table.fixedAt 0 index
    have h_columns : table.component.fixedColumns = some ZiskFv.AirsClean.Main.mainFixedColumns := by
      rfl
    have h_raw_index : index < table.rawRows.length := by
      simpa only [Table.table_length] using h_index
    have h_table_get :
        table.table.get ⟨index, by simpa only [Table.table_length] using h_raw_index⟩ =
          ZiskFv.AirsClean.Main.mainFixedColumns.materialize index
            (table.rawRows.get ⟨index, h_raw_index⟩) := by
      simp [Table.table, h_columns, List.mapIdx_eq_ofFn]
    rw [mainTableRowAtOrZero_get program table ⟨index, h_index⟩, h_table_get]
    rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
    exact ZiskFv.AirsClean.Main.eval_mainFixedColumns_segment_l1 index table.data _

/-- An in-range canonical Main row obtains `main_step` from the Main
    component's indexed fixed schema. -/
theorem mainTableRowAtOrZero_main_step_eq_fixedAt
    {length : Nat} (program : Program length) (table : Table FGL) (index : Nat)
    (h_index : index < table.table.length)
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) :
    (mainTableRowAtOrZero program table index).rom.main_step = table.fixedAt 1 index := by
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
    change (mainTableRowAtOrZero program table index).rom.main_step = table.fixedAt 1 index
    have h_columns : table.component.fixedColumns = some ZiskFv.AirsClean.Main.mainFixedColumns := by
      rfl
    have h_raw_index : index < table.rawRows.length := by
      simpa only [Table.table_length] using h_index
    have h_table_get :
        table.table.get ⟨index, by simpa only [Table.table_length] using h_raw_index⟩ =
          ZiskFv.AirsClean.Main.mainFixedColumns.materialize index
            (table.rawRows.get ⟨index, h_raw_index⟩) := by
      simp [Table.table, h_columns, List.mapIdx_eq_ofFn]
    rw [mainTableRowAtOrZero_get program table ⟨index, h_index⟩, h_table_get]
    rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
    exact ZiskFv.AirsClean.Main.eval_mainFixedColumns_main_step index table.data _

/-- Derive the Main row-index and timestamp facts from the canonical indexed
    fixed schema. `Table.index_lt_fixed_capacity` consumes the table's
    intrinsic `fixed_domain`, so the no-wrap bound is not a trace premise. -/
theorem mainStepIndexFixedFacts_of_component_fixedColumns
    {numInstructions programLength : Nat}
    (program : Program programLength) (table : Table FGL)
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus programLength program)
    (h_index : ∀ i : Fin numInstructions, i.val < table.table.length) :
    MainStepIndexFixedFacts numInstructions programLength program table := by
  cases table with
  | mk component rawRows data raw_uniform_width fixed_domain =>
    change component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus programLength program at h_component
    subst component
    let table : Table FGL :=
      { component := ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus programLength program
        rawRows := rawRows
        data := data
        raw_uniform_width := raw_uniform_width
        fixed_domain := fixed_domain }
    change MainStepIndexFixedFacts numInstructions programLength program table
    change ∀ i : Fin numInstructions, i.val < table.table.length at h_index
    have h_columns : table.component.fixedColumns = some ZiskFv.AirsClean.Main.mainFixedColumns := by
      rfl
    have capacity_bound (i : Fin numInstructions) :
        i.val < ZiskFv.AirsClean.Main.mainFixedCapacity := by
      have h_raw_index : i.val < table.length := by
        simpa only [Table.table_length] using h_index i
      have h_capacity : i.val < ZiskFv.AirsClean.Main.mainFixedColumns.capacity :=
        Table.index_lt_fixed_capacity table ZiskFv.AirsClean.Main.mainFixedColumns h_columns
          ⟨i.val, h_raw_index⟩
      simpa [ZiskFv.AirsClean.Main.mainFixedColumns] using h_capacity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [mainTableRowAtOrZero_main_step_eq_fixedAt program table i.val (h_index i) (by rfl)]
      rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
      exact ZiskFv.AirsClean.Main.mainFixedColumns_main_step_eq_index i.val (capacity_bound i)
    · intro i
      have h_capacity := capacity_bound i
      norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
      omega
    · intro i
      rw [mainTableRowAtOrZero_main_step_eq_fixedAt program table i.val (h_index i) (by rfl)]
      rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
      rw [ZiskFv.AirsClean.Main.mainFixedColumns_main_step_eq_index i.val (capacity_bound i)]
      have h_capacity := capacity_bound i
      have h_mul_bound : i.val * 4 < GL_prime := by
        norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
        omega
      have h_load_bound : 2 + i.val * 4 < GL_prime := by
        norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
        omega
      have h_i_bound : i.val < GL_prime := by
        norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
        omega
      change (2 + (i.val : FGL) * 4).val = 2 + 4 * i.val
      rw [Fin.val_add, Fin.val_mul]
      norm_num [Nat.mod_eq_of_lt h_i_bound, Nat.mod_eq_of_lt h_mul_bound,
        Nat.mod_eq_of_lt h_load_bound]
      omega
    · intro i
      rw [mainTableRowAtOrZero_main_step_eq_fixedAt program table i.val (h_index i) (by rfl)]
      rw [Table.fixedAt_of_fixedColumns table ZiskFv.AirsClean.Main.mainFixedColumns h_columns]
      rw [ZiskFv.AirsClean.Main.mainFixedColumns_main_step_eq_index i.val (capacity_bound i)]
      have h_capacity := capacity_bound i
      have h_mul_bound : i.val * 4 < GL_prime := by
        norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
        omega
      have h_store_bound : 3 + i.val * 4 < GL_prime := by
        norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
        omega
      have h_i_bound : i.val < GL_prime := by
        norm_num [ZiskFv.AirsClean.Main.mainFixedCapacity] at h_capacity ⊢
        omega
      change (3 + (i.val : FGL) * 4).val = 3 + 4 * i.val
      rw [Fin.val_add, Fin.val_mul]
      norm_num [Nat.mod_eq_of_lt h_i_bound, Nat.mod_eq_of_lt h_mul_bound,
        Nat.mod_eq_of_lt h_store_bound]
      omega

/-- The accepted trace's Main row-index and timestamp facts are derived from
    its selected Main table's component-owned indexed fixed schema. -/
theorem AcceptedZiskTrace.mainTable_main_step_index_fixed (trace : AcceptedZiskTrace n) :
    MainStepIndexFixedFacts trace.numInstructions trace.programLength trace.program trace.mainTable :=
  mainStepIndexFixedFacts_of_component_fixedColumns trace.program trace.mainTable
    trace.mainTable_component trace.mainTable_index

end ZiskFv.Compliance
