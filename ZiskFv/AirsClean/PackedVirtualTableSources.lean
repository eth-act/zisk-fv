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

variable {F : Type}

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
    (data : ProverData FGL) (hint : ProverHint FGL) :
    BinaryTableSlice.sourceCircuit.ProverAssumptions (binaryRow raw index) data hint := by
  exact BinaryTableSlice.sourceRow_constructible index _ data hint

theorem extensionRow_constructible (raw : Witness FGL)
    (index : Fin BinaryExtensionTable.tableSize) (data : ProverData FGL)
    (hint : ProverHint FGL) :
    BinaryExtensionTableSlice.sourceCircuit.ProverAssumptions (extensionRow raw index) data hint := by
  exact BinaryExtensionTableSlice.sourceRow_constructible index _ data hint

private theorem table_of_fixedColumns (t : Table FGL)
    (columns : IndexedFixedColumns FGL t.component.rawWidth)
    (h : t.component.fixedColumns = some columns) :
    t.table = t.rawRows.mapIdx (fun index row => columns.materialize index row) := by
  unfold Table.table
  rewrite [h]
  rfl

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
    exact Nat.le_of_eq List.length_ofFn

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
    exact Nat.le_of_eq List.length_ofFn

open ZiskFv.Channels.BinaryTable (BinaryTableChannel)
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableChannel)

theorem binaryProviderTable_materialized (raw : Witness FGL) (data : ProverData FGL) :
    (binaryProviderTable raw data).table =
      List.ofFn (fun index : Fin BinaryTable.tableSize =>
        (toElements (binaryRow raw index)).toArray) := by
  rewrite [table_of_fixedColumns (binaryProviderTable raw data)
    BinaryTableSlice.sourceFixedColumns rfl]
  dsimp only [binaryProviderTable]
  apply List.ext_getElem
  · simp only [List.length_mapIdx, List.length_ofFn]
  · intro index hi hi'
    have hindex : index < BinaryTable.tableSize := by
      simpa only [List.length_mapIdx, List.length_ofFn] using hi
    simp only [List.getElem_mapIdx, List.getElem_ofFn]
    exact BinaryTableSlice.sourceFixedColumns_materialize
      ⟨index, hindex⟩ (binaryRow raw ⟨index, hindex⟩).multiplicity

theorem extensionProviderTable_materialized (raw : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable raw data).table =
      List.ofFn (fun index : Fin BinaryExtensionTable.tableSize =>
        (toElements (extensionRow raw index)).toArray) := by
  rewrite [table_of_fixedColumns (extensionProviderTable raw data)
    BinaryExtensionTableSlice.sourceFixedColumns rfl]
  dsimp only [extensionProviderTable]
  apply List.ext_getElem
  · simp only [List.length_mapIdx, List.length_ofFn]
  · intro index hi hi'
    have hindex : index < BinaryExtensionTable.tableSize := by
      simpa only [List.length_mapIdx, List.length_ofFn] using hi
    simp only [List.getElem_mapIdx, List.getElem_ofFn]
    exact BinaryExtensionTableSlice.sourceFixedColumns_materialize
      ⟨index, hindex⟩ (extensionRow raw ⟨index, hindex⟩).multiplicity

/-- All provider constraints hold for every physical raw witness. Membership
    is constructed from the source index, not added to the caller's premises. -/
theorem binaryProviderTable_constraints (raw : Witness FGL) (data : ProverData FGL) :
    (binaryProviderTable raw data).Constraints := by
  intro row hr
  rw [binaryProviderTable_materialized] at hr
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hr
  exact BinaryTableSlice.source_constraints_fromInput (binaryRow raw index) data ⟨index, rfl⟩

theorem extensionProviderTable_constraints (raw : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable raw data).Constraints := by
  intro row hr
  rw [extensionProviderTable_materialized] at hr
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hr
  exact BinaryExtensionTableSlice.source_constraints_fromInput
    (extensionRow raw index) data ⟨index, rfl⟩

def binaryInteractions (raw : Witness FGL) : List (Interaction FGL) :=
  List.ofFn fun index : Fin BinaryTable.tableSize =>
    BinaryTableChannel.pushedIfValue (binaryRow raw index).multiplicity
      (binaryRow raw index).message

def extensionInteractions (raw : Witness FGL) : List (Interaction FGL) :=
  List.ofFn fun index : Fin BinaryExtensionTable.tableSize =>
    BinaryExtensionTableChannel.pushedIfValue (extensionRow raw index).multiplicity
      (extensionRow raw index).message

theorem binaryProviderTable_interactionsWith (raw : Witness FGL) (data : ProverData FGL) :
    (binaryProviderTable raw data).interactionsWith BinaryTableChannel.toRaw =
      binaryInteractions raw := by
  have hops := BinaryTableSlice.sourceComponent_interactionsWith
  change (binaryProviderTable raw data).component.operations.interactionsWith
    BinaryTableChannel.toRaw = _ at hops
  simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    hops, List.map_singleton, ← List.map_eq_flatMap]
  rw [binaryProviderTable_materialized, List.map_ofFn]
  apply congrArg (fun f : Fin BinaryTable.tableSize → Interaction FGL => List.ofFn f)
  funext index
  exact BinaryTableSlice.source_interaction_fromInput (binaryRow raw index) data

theorem extensionProviderTable_interactionsWith (raw : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable raw data).interactionsWith BinaryExtensionTableChannel.toRaw =
      extensionInteractions raw := by
  have hops := BinaryExtensionTableSlice.sourceComponent_interactionsWith
  change (extensionProviderTable raw data).component.operations.interactionsWith
    BinaryExtensionTableChannel.toRaw = _ at hops
  simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    hops, List.map_singleton, ← List.map_eq_flatMap]
  rw [extensionProviderTable_materialized, List.map_ofFn]
  apply congrArg (fun f : Fin BinaryExtensionTable.tableSize → Interaction FGL => List.ofFn f)
  funext index
  exact BinaryExtensionTableSlice.source_interaction_fromInput (extensionRow raw index) data

end ZiskFv.AirsClean.PackedVirtualTableSources
