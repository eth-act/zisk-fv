import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.Compliance.RegisterMemBusBalance

/-!
# Single-ADD forward witness skeleton (#219)

This file assembles the concrete table rows for the `add x1,x1,x1` witness against the full
RV64IM Clean ensemble.  The first milestone is structural: the witness has the real table list in
ensemble order.  Constraint and whole-channel balance proofs are layered on top of this skeleton.
-/

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.SingleAddWitness

def emptyComponentTable (component : Component FGL) : Table FGL where
  component := component
  width := component.width
  table := []
  data := emptyData
  uniform_width := by
    intro row h_row
    cases h_row

def binaryAddRowArray (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) : Array FGL :=
  (toElements row).toArray

def binaryAddSingleRowTable (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    Table FGL where
  component := ZiskFv.AirsClean.BinaryAdd.component
  width := size ZiskFv.AirsClean.BinaryAdd.BinaryAddRow
  table := [binaryAddRowArray row]
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [binaryAddRowArray] at h_arr
    subst arr
    simp

def addX1BinaryAddRow : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL :=
  ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 0

def singleAddBoundaryRows : List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  boundaryRowX1 :: (List.range 30).map (fun i => boundaryRowIdle ((i + 2 : Nat) : FGL))

def registerBoundaryRowsTable : Table FGL where
  component := ZiskFv.AirsClean.RegisterBoundary.component
  width := size ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow
  table := singleAddBoundaryRows.map registerBoundaryRowArray
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [singleAddBoundaryRows, registerBoundaryRowArray] at h_arr
    rcases h_arr with h_arr | h_arr
    · subst arr
      simp
    · rcases h_arr with ⟨row, _h_row, rfl⟩
      simp

def singleAddTables : List (Table FGL) :=
  [ registerBoundaryRowsTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , emptyComponentTable ZiskFv.AirsClean.ArithMul.componentWithArithTable
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , emptyComponentTable ZiskFv.AirsClean.Binary.staticLookupComponent
  , binaryAddSingleRowTable addX1BinaryAddRow
  , mainSingleRowTable 1 addX1Program addX1Row ]

def singleAddEnsemble : Ensemble FGL unit :=
  (fullRv64imEnsemble 1 addX1Program).ensemble

def singleAddWitness : EnsembleWitness singleAddEnsemble where
  tables := singleAddTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, singleAddTables,
      SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
      SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have hi' : i < 11 := by
      simpa [singleAddTables] using hi
    interval_cases i <;>
      simp [singleAddEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble, singleAddTables,
        SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable,
        SoundEnsemble.empty_tables, Ensemble.addTable, registerBoundaryRowsTable,
        emptyComponentTable, binaryAddSingleRowTable, mainSingleRowTable]
  same_data := by
    intro table h_table
    simp [singleAddTables, registerBoundaryRowsTable, emptyComponentTable, binaryAddSingleRowTable,
      mainSingleRowTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl

end ZiskFv.Compliance.SingleAddWitness
