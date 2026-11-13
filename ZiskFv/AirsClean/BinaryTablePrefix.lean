import ZiskFv.AirsClean.PackedVirtualTableSources
import Clean.Air.Balance

/-!
# Reifying accepted source prefixes in one actual packed raw witness

An accepted source component intrinsically owns its fixed tuple and bounds its
raw prefix. Absent source rows are extended with zero MULTIPLICITY, never with
invented fixed data. The generated disjoint location map embeds both prefixes
in the same physical witness, preserving all unrelated raw cells.

Normalization preserves every message's balance sum. It deliberately does not
claim the separate `BalancedInteractions` interaction-count bound is invariant
under adding zero interactions; integration must establish that bound from its
actual trace dimensions.
-/

namespace ZiskFv.AirsClean.PackedVirtualTableSources

open Goldilocks Air.Flat
open Extraction.PackedVirtualTables
open ZiskFv.Channels.BinaryTable (BinaryTableChannel)
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableChannel)

/-- Read the sole raw witness cell with its intrinsic width proof. Zero beyond
an absent prefix constructs an inactive source witness row; it is not a
fallback for malformed rows or an interpreter for unknown fixed data. -/
def rawMultiplicity (table : Table FGL) (hwidth : table.component.rawWidth = 1)
    (index : Nat) : FGL :=
  if hi : index < table.length then
    (table.rawRows[index]'hi)[0]'(by
      have hw := table.raw_uniform_width _ (List.getElem_mem hi)
      rw [hwidth] at hw
      omega)
  else 0

theorem rawRow_singleton (table : Table FGL) (hwidth : table.component.rawWidth = 1)
    (index : Fin table.length) :
    table.rawRows[index.val] = #[rawMultiplicity table hwidth index.val] := by
  have hw := table.raw_uniform_width _ (List.getElem_mem index.isLt)
  rw [hwidth] at hw
  simp only [rawMultiplicity, dif_pos index.isLt]
  apply Array.ext
  · simp [hw]
  · intro cell hcell hcell'
    have hzero : cell = 0 := by omega
    subst cell
    rfl

theorem binaryWidth (table : Table FGL)
    (hc : table.component = BinaryTableSlice.sourceComponent) :
    table.component.rawWidth = 1 := by
  rw [hc]
  rfl

theorem extensionWidth (table : Table FGL)
    (hc : table.component = BinaryExtensionTableSlice.sourceComponent) :
    table.component.rawWidth = 1 := by
  rw [hc]
  rfl

theorem binaryPrefix_bound (table : Table FGL)
    (hc : table.component = BinaryTableSlice.sourceComponent) :
    table.length ≤ BinaryTable.tableSize := by
  have hfixed : table.component.fixedColumns = some BinaryTableSlice.sourceFixedColumns := by
    rw [hc]
    rfl
  exact table.fixed_domain _ hfixed

theorem extensionPrefix_bound (table : Table FGL)
    (hc : table.component = BinaryExtensionTableSlice.sourceComponent) :
    table.length ≤ BinaryExtensionTable.tableSize := by
  have hfixed : table.component.fixedColumns = some BinaryExtensionTableSlice.sourceFixedColumns := by
    rw [hc]
    rfl
  exact table.fixed_domain _ hfixed

/-- Both target sources use one physical witness. The other three target
sources and every unrelated physical raw cell retain their base values. -/
def reifyPrefixes (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent) : Witness FGL :=
  physicalOfLogical base
    { bus88 := project base source88
      bus124 := fun index => rawMultiplicity extension (extensionWidth extension he) index.val
      bus125 := fun index => rawMultiplicity binary (binaryWidth binary hb) index.val
      bus330 := project base source330
      bus331 := project base source331 }

theorem binaryRow_reified (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    (index : Fin BinaryTable.tableSize) :
    binaryRow (reifyPrefixes base binary extension hb he) index =
      { message := BinaryTable.rowOfIndex index.val
        multiplicity := rawMultiplicity binary (binaryWidth binary hb) index.val } := by
  simp only [binaryRow, reifyPrefixes, project125_physicalOfLogical, binaryIndex]

theorem extensionRow_reified (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    (index : Fin BinaryExtensionTable.tableSize) :
    extensionRow (reifyPrefixes base binary extension hb he) index =
      { message := BinaryExtensionTable.rowOfIndex index.val
        multiplicity := rawMultiplicity extension (extensionWidth extension he) index.val } := by
  simp only [extensionRow, reifyPrefixes, project124_physicalOfLogical, extensionIndex]

theorem binaryPrefix_materialized_row (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    (index : Fin binary.length) :
    BinaryTableSlice.sourceFixedColumns.materialize index.val binary.rawRows[index.val] =
      (toElements (binaryRow (reifyPrefixes base binary extension hb he)
        ⟨index.val, lt_of_lt_of_le index.isLt (binaryPrefix_bound binary hb)⟩)).toArray := by
  rw [binaryRow_reified, rawRow_singleton binary (binaryWidth binary hb) index]
  exact BinaryTableSlice.sourceFixedColumns_materialize
    ⟨index.val, lt_of_lt_of_le index.isLt (binaryPrefix_bound binary hb)⟩ _

theorem extensionPrefix_materialized_row (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    (index : Fin extension.length) :
    BinaryExtensionTableSlice.sourceFixedColumns.materialize index.val extension.rawRows[index.val] =
      (toElements (extensionRow (reifyPrefixes base binary extension hb he)
        ⟨index.val, lt_of_lt_of_le index.isLt (extensionPrefix_bound extension he)⟩)).toArray := by
  rw [extensionRow_reified, rawRow_singleton extension (extensionWidth extension he) index]
  exact BinaryExtensionTableSlice.sourceFixedColumns_materialize
    ⟨index.val, lt_of_lt_of_le index.isLt (extensionPrefix_bound extension he)⟩ _

theorem binaryPrefix_materialized (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent) :
    binary.table = (binaryProviderTable (reifyPrefixes base binary extension hb he)
      binary.data).table.take binary.length := by
  have hfixed : binary.component.fixedColumns = some BinaryTableSlice.sourceFixedColumns := by
    rw [hb]
    rfl
  rw [Table.table, hfixed, binaryProviderTable_materialized]
  apply List.ext_getElem
  · simp [Nat.min_eq_left (binaryPrefix_bound binary hb)]
  · intro index hi hi'
    have hindex : index < binary.length := by simpa only [List.length_mapIdx] using hi
    simpa only [List.getElem_mapIdx, List.getElem_take, List.getElem_ofFn] using
      binaryPrefix_materialized_row base binary extension hb he ⟨index, hindex⟩

theorem extensionPrefix_materialized (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent) :
    extension.table = (extensionProviderTable (reifyPrefixes base binary extension hb he)
      extension.data).table.take extension.length := by
  have hfixed : extension.component.fixedColumns = some BinaryExtensionTableSlice.sourceFixedColumns := by
    rw [he]
    rfl
  rw [Table.table, hfixed, extensionProviderTable_materialized]
  apply List.ext_getElem
  · simp [Nat.min_eq_left (extensionPrefix_bound extension he)]
  · intro index hi hi'
    have hindex : index < extension.length := by simpa only [List.length_mapIdx] using hi
    simpa only [List.getElem_mapIdx, List.getElem_take, List.getElem_ofFn] using
      extensionPrefix_materialized_row base binary extension hb he ⟨index, hindex⟩

theorem binaryPrefix_interactionsWith (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent) :
    binary.interactionsWith BinaryTableChannel.toRaw =
      (binaryInteractions (reifyPrefixes base binary extension hb he)).take binary.length := by
  have hp := BinaryTableSlice.sourceComponent_interactionsWith
  have hprefix : binary.component.operations.interactionsWith BinaryTableChannel.toRaw = _ := by
    simpa only [hb] using hp
  have hfull := hp
  change (binaryProviderTable (reifyPrefixes base binary extension hb he) binary.data).component.operations.interactionsWith
    BinaryTableChannel.toRaw = _ at hfull
  rw [← binaryProviderTable_interactionsWith _ binary.data]
  simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    hprefix, hfull, List.map_singleton, ← List.map_eq_flatMap]
  rw [binaryPrefix_materialized base binary extension hb he, List.map_take]

theorem extensionPrefix_interactionsWith (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent) :
    extension.interactionsWith BinaryExtensionTableChannel.toRaw =
      (extensionInteractions (reifyPrefixes base binary extension hb he)).take extension.length := by
  have hp := BinaryExtensionTableSlice.sourceComponent_interactionsWith
  have hprefix : extension.component.operations.interactionsWith BinaryExtensionTableChannel.toRaw = _ := by
    simpa only [he] using hp
  have hfull := hp
  change (extensionProviderTable (reifyPrefixes base binary extension hb he) extension.data).component.operations.interactionsWith
    BinaryExtensionTableChannel.toRaw = _ at hfull
  rw [← extensionProviderTable_interactionsWith _ extension.data]
  simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    hprefix, hfull, List.map_singleton, ← List.map_eq_flatMap]
  rw [extensionPrefix_materialized base binary extension hb he, List.map_take]

theorem binaryReified_suffix_zero (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    {interaction : Interaction FGL}
    (hi : interaction ∈ (binaryInteractions (reifyPrefixes base binary extension hb he)).drop binary.length) :
    interaction.mult = 0 := by
  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hi
  have hbound := binaryPrefix_bound binary hb
  have hsource : binary.length + index < BinaryTable.tableSize := by
    simp only [binaryInteractions, List.length_drop, List.length_ofFn] at hindex
    omega
  simp only [binaryInteractions, List.getElem_drop, List.getElem_ofFn,
    Channel.pushedIfValue]
  rw [binaryRow_reified]
  simp only [rawMultiplicity, dif_neg (by omega : ¬ binary.length + index < binary.length)]

theorem extensionReified_suffix_zero (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    {interaction : Interaction FGL}
    (hi : interaction ∈ (extensionInteractions (reifyPrefixes base binary extension hb he)).drop extension.length) :
    interaction.mult = 0 := by
  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hi
  have hbound := extensionPrefix_bound extension he
  have hsource : extension.length + index < BinaryExtensionTable.tableSize := by
    simp only [extensionInteractions, List.length_drop, List.length_ofFn] at hindex
    omega
  simp only [extensionInteractions, List.getElem_drop, List.getElem_ofFn,
    Channel.pushedIfValue]
  rw [extensionRow_reified]
  simp only [rawMultiplicity, dif_neg (by omega : ¬ extension.length + index < extension.length)]

/-- Exact per-message balance sum preservation. Adding inactive source rows
changes no algebraic balance and introduces no caller semantic premise. -/
theorem binaryPrefix_balanceOf (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    (message : Array FGL) :
    balanceOf (binaryInteractions (reifyPrefixes base binary extension hb he)) message =
      balanceOf (binary.interactionsWith BinaryTableChannel.toRaw) message := by
  let full := binaryInteractions (reifyPrefixes base binary extension hb he)
  have hz : balanceOf (full.drop binary.length) message = 0 :=
    balanceOf_eq_of_const_zero (fun _ hi => binaryReified_suffix_zero base binary extension hb he hi)
  calc
    balanceOf full message = balanceOf (full.take binary.length ++ full.drop binary.length) message :=
      congrArg (fun xs => balanceOf xs message) (List.take_append_drop binary.length full).symm
    _ = balanceOf (binary.interactionsWith BinaryTableChannel.toRaw) message := by
      rw [balanceOf_append, ← binaryPrefix_interactionsWith base binary extension hb he, hz, add_zero]

theorem extensionPrefix_balanceOf (base : Witness FGL) (binary extension : Table FGL)
    (hb : binary.component = BinaryTableSlice.sourceComponent)
    (he : extension.component = BinaryExtensionTableSlice.sourceComponent)
    (message : Array FGL) :
    balanceOf (extensionInteractions (reifyPrefixes base binary extension hb he)) message =
      balanceOf (extension.interactionsWith BinaryExtensionTableChannel.toRaw) message := by
  let full := extensionInteractions (reifyPrefixes base binary extension hb he)
  have hz : balanceOf (full.drop extension.length) message = 0 :=
    balanceOf_eq_of_const_zero (fun _ hi => extensionReified_suffix_zero base binary extension hb he hi)
  calc
    balanceOf full message = balanceOf (full.take extension.length ++ full.drop extension.length) message :=
      congrArg (fun xs => balanceOf xs message) (List.take_append_drop extension.length full).symm
    _ = balanceOf (extension.interactionsWith BinaryExtensionTableChannel.toRaw) message := by
      rw [balanceOf_append, ← extensionPrefix_interactionsWith base binary extension hb he, hz, add_zero]

end ZiskFv.AirsClean.PackedVirtualTableSources
