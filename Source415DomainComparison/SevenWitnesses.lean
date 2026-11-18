import Source458DomainComparison.ConcreteOldWorlds
import ZiskFv.Compliance.SingleAddWitness
import ZiskFv.Compliance.AddSpinWitness
import ZiskFv.Compliance.AddAddiSpinWitness
import ZiskFv.Compliance.AddFaithfulPaddedWitness
import ZiskFv.Compliance.JalrSpinWitness
import ZiskFv.Compliance.SdLdSpinWitness
import ZiskFv.Compliance.DivSpinWitness

/-!
# Seven existing actual source-provider witnesses

These are genuine historical457 old18 accepted constructions, not casts of
corrected-domain witnesses. Their original raw rows/data and both complete
source providers are retained. ConcreteOldWorlds separately proves the old
scalar Mem D1 on the real Sd/Ld data and preserves the original prefix cases.
The older16↔18 comparison therefore keeps two historical endpoints; the separate
458 transport is only old18→corrected18. No converse accepted domain is claimed.
-/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison.SevenWitnesses

open Goldilocks Air.Flat
open ZiskFv.Compliance.Legacy457
open ZiskFv.Compliance.Instantiation
open ZiskFv.AirsClean.PackedVirtualTableSources
open ZiskFv.Compliance.RegisterMemBusBalance (addX1Program addX1Row)

/-- Evidence about a concrete existing witness, not a new acceptance contract.
The provider equalities retain every canonical source row, including zero
multiplicities; membership ties those providers to the balanced witness. -/
structure ActualEvidence {ensemble : Ensemble FGL unit}
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
        #[(binaryRow physical index).multiplicity]) := by
  simp only [binaryProviderTable]

theorem extensionProvider_full_rawRows (physical : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable physical data).rawRows =
      List.ofFn (fun index : Fin ZiskFv.AirsClean.BinaryExtensionTable.tableSize =>
        #[(extensionRow physical index).multiplicity]) := by
  simp only [extensionProviderTable]

section
open ZiskFv.Compliance.SingleAddWitness

/-- The genuine historical `singleAddWitness` carrier, with both complete original source providers. -/
theorem singleAdd_actual :
    ActualEvidence ConcreteOldWorlds.singleAddAcceptedTrace.witness (mainSingleRowTable 1 addX1Program addX1Row)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := ConcreteOldWorlds.singleAddAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.singleAddAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .singleAdd
    · change _ ∈ singleAddWitness.tables
      simp [singleAddWitness, singleAddTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .singleAdd
    · change _ ∈ singleAddWitness.tables
      simp [singleAddWitness, singleAddTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .singleAdd
    · change _ ∈ singleAddWitness.tables
      simp [singleAddWitness, singleAddTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.AddSpinWitness

/-- The genuine historical `addSpinWitness` carrier, with both complete original source providers. -/
theorem addSpin_actual :
    ActualEvidence ConcreteOldWorlds.addSpinAcceptedTrace.witness (addSpinMainTable)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := ConcreteOldWorlds.addSpinAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.addSpinAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addSpin
    · change _ ∈ addSpinWitness.tables
      simp [addSpinWitness, addSpinTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addSpin
    · change _ ∈ addSpinWitness.tables
      simp [addSpinWitness, addSpinTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addSpin
    · change _ ∈ addSpinWitness.tables
      simp [addSpinWitness, addSpinTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.AddAddiSpinWitness

/-- The genuine historical `addAddiSpinWitness` carrier, with both complete original source providers. -/
theorem addAddiSpin_actual :
    ActualEvidence ConcreteOldWorlds.addAddiSpinAcceptedTrace.witness (addAddiSpinMainTable)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := ConcreteOldWorlds.addAddiSpinAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.addAddiSpinAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addAddiSpin
    · change _ ∈ addAddiSpinWitness.tables
      simp [addAddiSpinWitness, addAddiSpinTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addAddiSpin
    · change _ ∈ addAddiSpinWitness.tables
      simp [addAddiSpinWitness, addAddiSpinTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addAddiSpin
    · change _ ∈ addAddiSpinWitness.tables
      simp [addAddiSpinWitness, addAddiSpinTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.AddFaithfulPaddedWitness

/-- The genuine historical `addFaithfulWitness` carrier, with both complete original source providers. -/
theorem addFaithful_actual :
    ActualEvidence ConcreteOldWorlds.addFaithfulAcceptedTrace.witness (addFaithfulMainTable)
      noRequestBinarySourceTable noRequestExtensionSourceTable
      ZiskFv.AirsClean.FullEnsemble.noRequestPackedSources emptyData where
  constraints := ConcreteOldWorlds.addFaithfulAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.addFaithfulAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addFaithful
    · change _ ∈ addFaithfulWitness.tables
      simp [addFaithfulWitness, addFaithfulTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addFaithful
    · change _ ∈ addFaithfulWitness.tables
      simp [addFaithfulWitness, addFaithfulTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .addFaithful
    · change _ ∈ addFaithfulWitness.tables
      simp [addFaithfulWitness, addFaithfulTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.JalrSpinWitness

/-- The genuine historical `jalrWitness` carrier, with both complete original source providers. -/
theorem jalr_actual :
    ActualEvidence ConcreteOldWorlds.jalrAcceptedTrace.witness (jalrMainTable)
      jalrBinarySourceTable jalrExtensionSourceTable
      jalrPackedSources emptyData where
  constraints := ConcreteOldWorlds.jalrAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.jalrAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .jalr
    · change _ ∈ jalrWitness.tables
      simp [jalrWitness, jalrTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .jalr
    · change _ ∈ jalrWitness.tables
      simp [jalrWitness, jalrTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .jalr
    · change _ ∈ jalrWitness.tables
      simp [jalrWitness, jalrTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.SdLdSpinWitness

/-- The genuine historical `sdLdWitness` carrier, with both complete original source providers. -/
theorem sdLd_actual :
    ActualEvidence ConcreteOldWorlds.sdLdAcceptedTrace.witness (sdLdTableWithData sdLdMainTable)
      sdLdBinarySourceTable sdLdExtensionSourceTable
      sdLdPackedSources ZiskFv.Compliance.sdLdMemData where
  constraints := ConcreteOldWorlds.sdLdAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.sdLdAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .sdLd
    · change _ ∈ sdLdWitness.tables
      simp [sdLdWitness, sdLdTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .sdLd
    · change _ ∈ sdLdWitness.tables
      simp [sdLdWitness, sdLdTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .sdLd
    · change _ ∈ sdLdWitness.tables
      simp [sdLdWitness, sdLdTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

section
open ZiskFv.Compliance.DivSpinWitness

/-- The genuine historical `divSpinWitness` carrier, with both complete original source providers. -/
theorem divSpin_actual :
    ActualEvidence ConcreteOldWorlds.divSpinAcceptedTrace.witness (divSpinMainTable)
      divSpinBinarySourceTable divSpinExtensionSourceTable
      divSpinPackedSources emptyData where
  constraints := ConcreteOldWorlds.divSpinAcceptedTrace.constraints_hold
  balanced := ConcreteOldWorlds.divSpinAcceptedTrace.channels_balanced
  main_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .divSpin
    · change _ ∈ divSpinWitness.tables
      simp [divSpinWitness, divSpinTables]
    · decide
  main_nonempty := by decide
  binary_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .divSpin
    · change _ ∈ divSpinWitness.tables
      simp [divSpinWitness, divSpinTables]
    · decide
  extension_mem := by
    apply ConcreteOldWorlds.sourceTable_preserved .divSpin
    · change _ ∈ divSpinWitness.tables
      simp [divSpinWitness, divSpinTables]
    · decide
  binary_full := rfl
  extension_full := rfl

end

end ZiskFv.AirsClean.FullEnsemble.DomainComparison.SevenWitnesses
