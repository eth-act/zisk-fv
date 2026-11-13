import Extraction.PackedVirtualTables
import ZiskFv.AirsClean.BinaryTableSlice
import ZiskFv.AirsClean.BinaryExtensionTableSlice

/-!
# Intrinsic projections of the actual packed virtual-table witness

The generated map is observed from production `virtual_table_data`, all target
fixed cells, the converse UID ownership scan, and the actual dynamic producer's
raw multiplicity operands. Its locations are not supplied by a caller.
Unrelated packed data is not modeled here. Unselected raw witness cells are
preserved, not interpreted as zero.
-/

namespace ZiskFv.AirsClean.PackedVirtualTableSources

open Goldilocks Air.Flat
open Extraction.PackedVirtualTables

/-- The two physical packed AIRs each have eight stage-1 multiplicity columns
and `2^21` physical rows. These are raw witness values, not semantic facts. -/
abbrev Witness (F : Type) := Location → F

/-- Logical source views of those raw cells, with the production domains from
actual compiler metadata. -/
structure LogicalWitness (F : Type) where
  bus88 : Fin source88.rows → F
  bus124 : Fin source124.rows → F
  bus125 : Fin source125.rows → F
  bus330 : Fin source330.rows → F
  bus331 : Fin source331.rows → F

def project (raw : Witness F) (source : Source) : Fin source.rows → F :=
  fun index => raw (source.location index)

/-- Embed arbitrary target-source multiplicities into the actual eight-column
physical witness, preserving every unrelated raw cell. Bounds and ownership
are checked by the intrinsic production map, never a caller equality promise. -/
def physicalOfLogical (base : Witness F) (logical : LogicalWitness F) : Witness F :=
  fun location =>
    match sourceAt location with
    | none => base location
    | some (table, index) =>
      if table = source88.tableId then
        if hi : index < source88.rows then logical.bus88 ⟨index, hi⟩ else base location
      else if table = source124.tableId then
        if hi : index < source124.rows then logical.bus124 ⟨index, hi⟩ else base location
      else if table = source125.tableId then
        if hi : index < source125.rows then logical.bus125 ⟨index, hi⟩ else base location
      else if table = source330.tableId then
        if hi : index < source330.rows then logical.bus330 ⟨index, hi⟩ else base location
      else if table = source331.tableId then
        if hi : index < source331.rows then logical.bus331 ⟨index, hi⟩ else base location
      else base location

theorem project88_physicalOfLogical (base : Witness F) (logical : LogicalWitness F) :
    project (physicalOfLogical base logical) source88 = logical.bus88 := by
  funext index
  simp [project, physicalOfLogical, source88_at, source88, index.isLt]

theorem project124_physicalOfLogical (base : Witness F) (logical : LogicalWitness F) :
    project (physicalOfLogical base logical) source124 = logical.bus124 := by
  funext index
  simp [project, physicalOfLogical, source124_at, source88, source124, index.isLt]

theorem project125_physicalOfLogical (base : Witness F) (logical : LogicalWitness F) :
    project (physicalOfLogical base logical) source125 = logical.bus125 := by
  funext index
  simp [project, physicalOfLogical, source125_at, source88, source124, source125, index.isLt]

theorem project330_physicalOfLogical (base : Witness F) (logical : LogicalWitness F) :
    project (physicalOfLogical base logical) source330 = logical.bus330 := by
  funext index
  simp [project, physicalOfLogical, source330_at,
    source88, source124, source125, source330, index.isLt]

theorem project331_physicalOfLogical (base : Witness F) (logical : LogicalWitness F) :
    project (physicalOfLogical base logical) source331 = logical.bus331 := by
  funext index
  simp [project, physicalOfLogical, source331_at,
    source88, source124, source125, source330, source331, index.isLt]

/-- Source indices cannot alias a different table's physical multiplicity cell. -/
theorem binary_source_locations_disjoint
    (left : Fin source125.rows) (right : Fin source124.rows) :
    source125.location left ≠ source124.location right := by
  intro h
  have he := congrArg sourceAt h
  rw [source125_at, source124_at] at he
  norm_num [source125, source124] at he

def binaryIndex (index : Fin BinaryTable.tableSize) : Fin source125.rows :=
  ⟨index.val, by simpa only [source125, BinaryTable.tableSize] using index.isLt⟩

def extensionIndex (index : Fin BinaryExtensionTable.tableSize) : Fin source124.rows :=
  ⟨index.val, by
    simpa only [source124, BinaryExtensionTable.tableSize,
      BinaryExtensionTable.shiftBlockSize, BinaryExtensionTable.sextBlockSize] using index.isLt⟩

/-- The actual bus-125 producer row: exact source tuple and the physical raw
witness cell selected by the compiled production packing. -/
def binaryRow (raw : Witness FGL) (index : Fin BinaryTable.tableSize) :
    BinaryTableSlice.SourceRow FGL :=
  { message := BinaryTable.rowOfIndex index.val
    multiplicity := project raw source125 (binaryIndex index) }

def extensionRow (raw : Witness FGL) (index : Fin BinaryExtensionTable.tableSize) :
    BinaryExtensionTableSlice.SourceRow FGL :=
  { message := BinaryExtensionTable.rowOfIndex index.val
    multiplicity := project raw source124 (extensionIndex index) }

theorem binaryRow_constructible (raw : Witness FGL) (index : Fin BinaryTable.tableSize)
    (data : ProverData FGL) :
    BinaryTableSlice.sourceCircuit.ProverAssumptions (binaryRow raw index) () data := by
  exact BinaryTableSlice.sourceRow_constructible index _ data

theorem extensionRow_constructible (raw : Witness FGL)
    (index : Fin BinaryExtensionTable.tableSize) (data : ProverData FGL) :
    BinaryExtensionTableSlice.sourceCircuit.ProverAssumptions (extensionRow raw index) () data := by
  exact BinaryExtensionTableSlice.sourceRow_constructible index _ data

/-- Canonical full-domain raw rows for the projected provider table. The only
witness cell comes from the actual packed multiplicity lane, without a copy of
or a caller premise about any fixed column. -/
def binaryProviderTable (raw : Witness FGL) (data : ProverData FGL) : Table FGL where
  component := BinaryTableSlice.sourceComponent
  rawRows := List.ofFn fun index : Fin BinaryTable.tableSize => #[(binaryRow raw index).multiplicity]
  data := data
  raw_uniform_width := by
    intro row hr
    simp only [List.mem_ofFn] at hr
    obtain ⟨index, rfl⟩ := hr
    rfl
  fixed_domain := by
    intro columns hcolumns
    have he : columns = BinaryTableSlice.sourceFixedColumns := Option.some.inj hcolumns.symm
    subst columns
    simp [BinaryTableSlice.sourceFixedColumns]

def extensionProviderTable (raw : Witness FGL) (data : ProverData FGL) : Table FGL where
  component := BinaryExtensionTableSlice.sourceComponent
  rawRows := List.ofFn fun index : Fin BinaryExtensionTable.tableSize => #[(extensionRow raw index).multiplicity]
  data := data
  raw_uniform_width := by
    intro row hr
    simp only [List.mem_ofFn] at hr
    obtain ⟨index, rfl⟩ := hr
    rfl
  fixed_domain := by
    intro columns hcolumns
    have he : columns = BinaryExtensionTableSlice.sourceFixedColumns := Option.some.inj hcolumns.symm
    subst columns
    simp [BinaryExtensionTableSlice.sourceFixedColumns]

end ZiskFv.AirsClean.PackedVirtualTableSources
