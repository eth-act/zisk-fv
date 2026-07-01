import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance

/-!
# Derived Mem-table accessor

Selecting the dual-aware mutable Mem table out of the witness is **derived**, not assumed:
`exists_mem_table_of_fullRv64im_witness` already produces one from `trace.witness` alone. These
accessors expose that choice so the memory-timeline derivation (issue #115) can reach the Mem table's
rows from `AcceptedZiskTrace` instead of from a caller-supplied `LoadMemoryTimelineCoherenceEvidence`.
Mirrors `AcceptedZiskTrace.mainTable`.
-/

namespace ZiskFv.Compliance

/-- The dual-aware mutable Mem table selected from the witness. **Non-reducible** so it behaves
    opaquely, exactly like `mainTable`. -/
noncomputable def AcceptedZiskTrace.memTable (trace : AcceptedZiskTrace n) : Air.Flat.Table FGL :=
  (ZiskFv.AirsClean.FullEnsemble.exists_mem_table_of_fullRv64im_witness trace.witness).choose

/-- The derived Mem table really occurs in the witness. -/
theorem AcceptedZiskTrace.memTable_mem (trace : AcceptedZiskTrace n) :
    trace.memTable ∈ trace.witness.allTables :=
  (ZiskFv.AirsClean.FullEnsemble.exists_mem_table_of_fullRv64im_witness trace.witness).choose_spec.1

/-- The derived Mem table really is the dual-aware mutable Mem component. -/
theorem AcceptedZiskTrace.memTable_component (trace : AcceptedZiskTrace n) :
    trace.memTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus :=
  (ZiskFv.AirsClean.FullEnsemble.exists_mem_table_of_fullRv64im_witness trace.witness).choose_spec.2

end ZiskFv.Compliance
