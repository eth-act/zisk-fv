import ZiskFv.Compliance.SdLdMemTable

/-!
# SD/LD non-degenerate Mem-prefix constructibility

The #221 constructibility check establishes the first real mutable-Mem prefix used by an
accepted trace: an SD of `42` and an LD of that same word at RAM word address
`0x14000001`.  This hook keeps the full local and generated Mem surfaces in
the semantic trust gate before the root-soundness assembly consumes the table.
-/

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.Compliance

theorem sd_ld_mem_table_constructible :
    sdLdMemTable.Constraints ∧ sdLdMemTable.TransitionConstraints ∧
      ZiskFv.AirsClean.FullEnsemble.MemTableGeneratedConstraintFacts
        sdLdMemTable
        (ZiskFv.AirsClean.FullEnsemble.memOfTableData sdLdMemTable)
        (ZiskFv.AirsClean.FullEnsemble.memSegmentOfTableData sdLdMemTable)
        (ZiskFv.AirsClean.FullEnsemble.memPermutationOfTableData sdLdMemTable) :=
  ⟨sdLdMemTable_constraints, sdLdMemTable_transitions,
    sdLdMemTable_generatedConstraintFacts⟩

#print axioms sd_ld_mem_table_constructible

end ZiskFv.TrustConsistency
