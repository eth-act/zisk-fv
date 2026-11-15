import ZiskFv.Compliance.SingleAddWitness
import ZiskFv.Compliance.AddSpinWitness
import ZiskFv.Compliance.AddAddiSpinWitness
import ZiskFv.Compliance.AddFaithfulPaddedWitness
import ZiskFv.Compliance.JalrSpinWitness
import ZiskFv.Compliance.SdLdSpinWitness
import ZiskFv.Compliance.DivSpinWitness

/-!
# Seven existing actual source-provider witnesses

These are the seven concrete current Compliance constructions, not frozen-old
accepted witnesses or an oldAccepted → newAccepted transport theorem. Each named
result records existing constraints and full channel balance, an actual nonempty
Main table, and the actual two full-domain packed-source providers in that same
witness. No equivalence of accepted domains is asserted here.
-/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison.SevenWitnesses

open Goldilocks Air.Flat
open ZiskFv.Compliance.Instantiation
open ZiskFv.AirsClean.PackedVirtualTableSources

/-- Evidence about a concrete existing witness, not a new acceptance contract.
The provider equalities retain every canonical source row, including zero
multiplicities; membership ties those providers to the balanced witness. -/
structure ActualEvidence {ensemble : Ensemble FGL Unit}
    (witness : EnsembleWitness ensemble) (main binary extension : Table FGL)
    (physical : Witness FGL) (data : ProverData FGL) : Prop where
  constraints : witness.Constraints
  balanced : witness.BalancedChannels
  main_mem : main ∈ witness.tables
  main_nonempty : main.rawRows ≠ []
  binary_mem : binary ∈ witness.tables
  extension_mem : extension ∈ witness.tables
  binary_full : binary = binaryProviderTable physical data
  extension_full : extension = extensionProviderTable physical data

/-- Full-domain means the complete canonical indexed raw row list, not merely
coverage of requested/nonzero keys. -/
theorem binaryProvider_full_rawRows (physical : Witness FGL) (data : ProverData FGL) :
    (binaryProviderTable physical data).rawRows =
      List.ofFn (fun index : Fin ZiskFv.AirsClean.BinaryTable.tableSize =>
        #[(binaryRow physical index).multiplicity]) := rfl

theorem extensionProvider_full_rawRows (physical : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable physical data).rawRows =
      List.ofFn (fun index : Fin ZiskFv.AirsClean.BinaryExtensionTable.tableSize =>
        #[(extensionRow physical index).multiplicity]) := rfl

section
open ZiskFv.Compliance.SingleAddWitness

/-- The existing actual `singleAddWitness`, with both complete source providers. -/
theorem singleAdd_actual :
    ActualEvidence singleAddWitness (mainSingleRowTable 1 addX1Program addX1Row)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := singleAddWitness_constraints
  balanced := singleAddWitness_balancedChannels
  main_mem := by simp [singleAddWitness, singleAddTables]
  main_nonempty := by decide
  binary_mem := by simp [singleAddWitness, singleAddTables]
  extension_mem := by simp [singleAddWitness, singleAddTables]
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.AddSpinWitness

/-- The existing actual `addSpinWitness`, with both complete source providers. -/
theorem addSpin_actual :
    ActualEvidence addSpinWitness (addSpinMainTable)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := addSpinWitness_constraints
  balanced := addSpinWitness_balancedChannels
  main_mem := by simp [addSpinWitness, addSpinTables]
  main_nonempty := by decide
  binary_mem := by simp [addSpinWitness, addSpinTables]
  extension_mem := by simp [addSpinWitness, addSpinTables]
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.AddAddiSpinWitness

/-- The existing actual `addAddiSpinWitness`, with both complete source providers. -/
theorem addAddiSpin_actual :
    ActualEvidence addAddiSpinWitness (addAddiSpinMainTable)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := addAddiSpinWitness_constraints
  balanced := addAddiSpinWitness_balancedChannels
  main_mem := by simp [addAddiSpinWitness, addAddiSpinTables]
  main_nonempty := by decide
  binary_mem := by simp [addAddiSpinWitness, addAddiSpinTables]
  extension_mem := by simp [addAddiSpinWitness, addAddiSpinTables]
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.AddFaithfulPaddedWitness

/-- The existing actual `addFaithfulWitness`, with both complete source providers. -/
theorem addFaithful_actual :
    ActualEvidence addFaithfulWitness (addFaithfulMainTable)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := addFaithfulWitness_constraints
  balanced := addFaithfulWitness_balancedChannels
  main_mem := by simp [addFaithfulWitness, addFaithfulTables]
  main_nonempty := by decide
  binary_mem := by simp [addFaithfulWitness, addFaithfulTables]
  extension_mem := by simp [addFaithfulWitness, addFaithfulTables]
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.JalrSpinWitness

/-- The existing actual `jalrWitness`, with both complete source providers. -/
theorem jalr_actual :
    ActualEvidence jalrWitness (jalrMainTable)
      jalrBinarySourceTable jalrExtensionSourceTable
      jalrPackedSources emptyData where
  constraints := jalrWitness_constraints
  balanced := jalrWitness_balancedChannels
  main_mem := by simp [jalrWitness, jalrTables]
  main_nonempty := by decide
  binary_mem := by simp [jalrWitness, jalrTables]
  extension_mem := by simp [jalrWitness, jalrTables]
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.SdLdSpinWitness

/-- The existing actual `sdLdWitness`, with both complete source providers. -/
theorem sdLd_actual :
    ActualEvidence sdLdWitness (sdLdMainTable)
      sdLdBinarySourceTable sdLdExtensionSourceTable
      sdLdPackedSources sdLdMemData where
  constraints := sdLdWitness_constraints
  balanced := sdLdWitness_balancedChannels
  main_mem := by simp [sdLdWitness, sdLdTables]
  main_nonempty := by decide
  binary_mem := by simp [sdLdWitness, sdLdTables]
  extension_mem := by simp [sdLdWitness, sdLdTables]
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.DivSpinWitness

/-- The existing actual `divSpinWitness`, with both complete source providers. -/
theorem divSpin_actual :
    ActualEvidence divSpinWitness (divSpinMainTable)
      divSpinBinarySourceTable divSpinExtensionSourceTable
      divSpinPackedSources emptyData where
  constraints := divSpinWitness_constraints
  balanced := divSpinWitness_balancedChannels
  main_mem := by simp [divSpinWitness, divSpinTables]
  main_nonempty := by decide
  binary_mem := by simp [divSpinWitness, divSpinTables]
  extension_mem := by simp [divSpinWitness, divSpinTables]
  binary_full := rfl
  extension_full := rfl

end

end ZiskFv.AirsClean.FullEnsemble.DomainComparison.SevenWitnesses
