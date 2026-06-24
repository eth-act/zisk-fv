import ZiskFv.Compliance.AcceptedTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance

/-!
# Derived Main-table accessor

Selecting the Main execution table out of the witness is **derived**, not
assumed: `exists_main_table_of_fullRv64im_witness` already produces one from
`trace.witness` alone. These accessors expose that choice so it no longer needs
to be supplied as `ProgramBinding` fields. The one genuine external assumption
about the Main table — its row count — lives on `AcceptedTrace.main_height`;
`mainTable_index` below specializes it to the derived `mainTable`.
-/

namespace ZiskFv.Compliance

/-- The Main execution table selected from the witness. **Non-reducible** so it
    behaves opaquely, exactly like the former `ProgramBinding.mainTable` struct
    field: proofs that treat the Main table abstractly keep working unchanged. -/
noncomputable def AcceptedTrace.mainTable (trace : AcceptedTrace) : Air.Flat.Table FGL :=
  (ZiskFv.AirsClean.FullEnsemble.exists_main_table_of_fullRv64im_witness
    trace.witness).choose

/-- The derived Main table really occurs in the witness. -/
theorem AcceptedTrace.mainTable_mem (trace : AcceptedTrace) :
    trace.mainTable ∈ trace.witness.allTables :=
  (ZiskFv.AirsClean.FullEnsemble.exists_main_table_of_fullRv64im_witness
    trace.witness).choose_spec.1

/-- The derived Main table really is the Main component for this program. -/
theorem AcceptedTrace.mainTable_component (trace : AcceptedTrace) :
    trace.mainTable.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.numInstructions trace.program :=
  (ZiskFv.AirsClean.FullEnsemble.exists_main_table_of_fullRv64im_witness
    trace.witness).choose_spec.2

/-- The derived Main table has a row for every instruction — `main_height`
    specialized to `mainTable` via its membership and component facts. -/
theorem AcceptedTrace.mainTable_index (trace : AcceptedTrace) :
    ∀ i : Fin trace.numInstructions, i.val < trace.mainTable.table.length :=
  trace.main_height trace.mainTable trace.mainTable_mem trace.mainTable_component

end ZiskFv.Compliance
