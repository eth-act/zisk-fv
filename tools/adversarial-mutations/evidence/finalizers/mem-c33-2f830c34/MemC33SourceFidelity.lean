import Extraction.LookupWiring

/-! Immutable expected shape from dc7cc4d6d692cf1067af769b1abb84158af0f73f,
Mem.SourceFinalizer.expectedConstraint. Not generated from the input under test.
All normal producer dispositions retain their actual source AST in this probe;
an unrecognized template or missing link identifier is not a rejection. -/
open Extraction.LookupWiring

namespace MemC33SourceFidelity

def expectedConstraint : Expr :=
  .mul (.fixed 1 1)
    (.sub (.sub (.airGroupValue 0) (.witness 2 0 0))
      (.add (.add (.add (.add (.add (.airValue 15) (.airValue 16))
        (.airValue 17)) (.airValue 18)) (.airValue 19)) (.airValue 20)))

def actualCompiledConstraints : List Expr :=
  ((validatedLinks.filter fun entry => entry.air == "Mem" && entry.constraintIndex == 33).map
    fun entry => entry.constraint) ++
  ((validatedFinalRows.filter fun entry => entry.air == "Mem" && entry.constraintIndex == 33).map
    fun entry => entry.constraint) ++
  ((unlinkedMixedConstraints.filter fun entry => entry.air == "Mem" && entry.constraintIndex == 33).map
    fun entry => entry.constraint)

theorem mem_c33_actual_compiled_source_fidelity :
    actualCompiledConstraints = [expectedConstraint] := by
  rfl

end MemC33SourceFidelity
