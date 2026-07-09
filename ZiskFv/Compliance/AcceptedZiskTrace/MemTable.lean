import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections

/-!
# Derived Mem-table row-local facts

This file exposes the row-local Mem facts that really follow from an accepted
trace's derived `spec_holds`. It intentionally does not construct generated
Mem replay facts: cross-row constraints, range lookups, and permutation
accumulators remain separate certificate surfaces.
-/

namespace ZiskFv.Compliance

/-- For any concrete dual-Mem table in the accepted witness, the named-column
    `memOfTable` projection satisfies the row-local Clean Mem `Spec` at every
    in-range row. -/
theorem AcceptedZiskTrace.memTableRow_specs
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Air.Flat.Table FGL}
    (gsum im0 im1 : ℕ → FGL)
    (h_table : table ∈ trace.witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.Spec
        (ZiskFv.AirsClean.Mem.rowAt
          (ZiskFv.AirsClean.FullEnsemble.memOfTable table gsum im0 im1)
          idx.val) := by
  exact
    ZiskFv.AirsClean.FullEnsemble.tableRow_specs_of_memOfTable_spec
      table gsum im0 im1 h_component (trace.spec_holds table h_table)

end ZiskFv.Compliance
