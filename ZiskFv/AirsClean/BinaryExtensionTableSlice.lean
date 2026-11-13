import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.BinaryExtensionTable
import ZiskFv.Channels.BinaryExtensionTable

/-!
# `BinaryExtensionTable` static provider slice

The BinaryExtensionTable channel provider is backed by the exact decoded-row
`binaryExtensionTable` model. It owns table membership; BinaryExtension
consumers only emit negative messages, and a finished channel transports this
fact.

## Trust note

No axioms. Soundness derives exact `binaryExtensionTable.Spec` membership from
the static lookup. The identical completeness-side membership premise supplies
a constructible static-table index and is not a soundness assumption.
-/

namespace ZiskFv.AirsClean.BinaryExtensionTableSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.BinaryExtensionTable
open ZiskFv.Channels.BinaryExtensionTable

@[circuit_norm]
def main (message : BinaryExtensionTableMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic binaryExtensionTable) message
  BinaryExtensionTableChannel.push message


def circuit : GeneralFormalCircuit FGL BinaryExtensionTableMessage unit  where
  name := "BinaryExtensionTableSlice124"
  main := main
  channelsWithRequirements := [BinaryExtensionTableChannel.toRaw]
  exposedChannels message _ :=
    expose BinaryExtensionTableChannel [BinaryExtensionTableChannel.pushed message]
  Assumptions := fun _ _ => True
  Spec := fun message _ _ => binaryExtensionTable.Spec message
  ProverAssumptions := fun message _ _ => binaryExtensionTable.Spec message
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [BinaryExtensionTableChannel]
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

def component : Component FGL := { circuit }

theorem component_interactionsWith_binaryExtensionTableChannel :
    component.operations.interactionsWith BinaryExtensionTableChannel.toRaw =
      [((BinaryExtensionTableChannel.pushed component.rowInputVar).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryExtensionTableChannel.toRaw,
      [((BinaryExtensionTableChannel.pushed component.rowInputVar).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

/-- The table tuple is collected by virtual `lookup_proves`; the actual
    packed producer uses `VirtualTable.multiplicity[lane]` unchanged
    (`std_virtual_table.pil:435,530`). This is its target-bus projection. -/
structure SourceRow (F : Type) where
  message : BinaryExtensionTableMessage F
  multiplicity : F
deriving ProvableStruct

theorem eval_source_message (env : Environment FGL) (row : SourceRow (Expression FGL)) :
    (eval env row : SourceRow FGL).message = eval env row.message := by
  rw [ProvableStruct.eval_eq_eval (α := SourceRow)]
  rfl

theorem eval_source_multiplicity (env : Environment FGL) (row : SourceRow (Expression FGL)) :
    (eval env row : SourceRow FGL).multiplicity = eval env row.multiplicity := by
  rw [ProvableStruct.eval_eq_eval (α := SourceRow)]
  rfl

@[circuit_norm]
def sourceMain (row : SourceRow (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic binaryExtensionTable) row.message
  BinaryExtensionTableChannel.emit row.multiplicity row.message

def sourceCircuit : GeneralFormalCircuit FGL SourceRow unit where
  name := "BinaryExtensionTableSource124"
  main := sourceMain
  channelsWithRequirements := [BinaryExtensionTableChannel.toRaw]
  exposedChannels row _ :=
    expose BinaryExtensionTableChannel
      [BinaryExtensionTableChannel.emitted row.multiplicity row.message]
  Assumptions := fun _ _ => True
  Spec := fun row _ _ => binaryExtensionTable.Spec row.message
  ProverAssumptions := fun row _ _ => binaryExtensionTable.Spec row.message
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [BinaryExtensionTableChannel]
  completeness := by
    circuit_proof_start [Lookup.completeness_def, BinaryExtensionTableChannel]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

/-- Production uses `virtual BinaryExtensionTable(BINARY_EXTENSION_TABLE_SIZE)`
    (`zisk/pil/zisk.pil:123`), not the template's default `2^22`. -/
def sourceFixedColumns : IndexedFixedColumns FGL 1 where
  capacity := tableSize
  capacity_pos := by norm_num [tableSize, shiftBlockSize, sextBlockSize]
  effectiveWidth := 8
  fixedWidth := 7
  layout slot :=
    if h : slot.val < 7 then .inr ⟨slot.val, h⟩ else .inl 0
  values slot index := (toElements (rowOfIndex index.val))[slot.val]

def sourceComponent : Component FGL :=
  { circuit := sourceCircuit, rawWidth := 1, fixedColumns := some sourceFixedColumns }

theorem sourceFixedColumns_materialize (index : Fin tableSize) (multiplicity : FGL) :
    sourceFixedColumns.materialize index.val #[multiplicity] =
      (toElements ({ message := rowOfIndex index.val, multiplicity } :
        SourceRow FGL)).toArray := by
  apply Array.ext
  · rfl
  · intro i hi hi'
    have h_i : i < 8 := by simpa only [IndexedFixedColumns.materialize_size] using hi
    interval_cases i <;>
      simp [IndexedFixedColumns.materialize, IndexedFixedColumns.fixedAt,
        sourceFixedColumns, Nat.mod_eq_of_lt index.isLt, toElements,
        ProvableType.fromStruct, ProvableStruct.componentsToElements,
        ProvableStruct.toComponents, ProvableStruct.components]

theorem eval_sourceFixedColumns (index : Fin tableSize) (multiplicity : FGL)
    (data : ProverData FGL) :
    eval (Environment.fromArray
      (sourceFixedColumns.materialize index.val #[multiplicity]) data)
      sourceComponent.rowInputVar =
        ({ message := rowOfIndex index.val, multiplicity } : SourceRow FGL) := by
  rw [sourceFixedColumns_materialize]
  exact ProvableType.eval_fromInput_varFromOffset_zero _ _

theorem sourceComponent_interactionsWith :
    sourceComponent.operations.interactionsWith BinaryExtensionTableChannel.toRaw =
      [((BinaryExtensionTableChannel.emitted sourceComponent.rowInputVar.multiplicity
          sourceComponent.rowInputVar.message).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryExtensionTableChannel.toRaw,
      [((BinaryExtensionTableChannel.emitted sourceComponent.rowInputVar.multiplicity
          sourceComponent.rowInputVar.message).toRaw)]⟩ ∈ sourceComponent.exposedChannels
  simp only [sourceComponent, sourceCircuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

theorem sourceComponent_constraints :
    sourceComponent.operations.constraints = [] := by
  rw [Component.constraints_eq]
  rfl

theorem sourceComponent_lookups :
    sourceComponent.operations.lookups =
      [{ table := (Table.fromStatic binaryExtensionTable).toRaw
         entry := toElements sourceComponent.rowInputVar.message }] := by
  rw [Component.lookups_eq]
  rfl

/-- Every production source row, with any source multiplicity, supplies
    its own completeness index. This is not a soundness-side premise. -/
theorem sourceRow_constructible (index : Fin tableSize) (multiplicity : FGL)
    (data : ProverData FGL) (hint : ProverHint FGL) :
    sourceCircuit.ProverAssumptions
      { message := rowOfIndex index.val, multiplicity } data hint := by
  exact ⟨index, rfl⟩

theorem sourceComponent_spec_of_constraints (env : Environment FGL)
    (h : sourceComponent.operations.ConstraintsHold env) :
    binaryExtensionTable.Spec (eval env sourceComponent.rowInputVar.message) := by
  let query : Lookup FGL :=
    { table := (Table.fromStatic binaryExtensionTable).toRaw
      entry := toElements sourceComponent.rowInputVar.message }
  have hquery : query.Contains env :=
    h.2 query (by
      rw [sourceComponent_lookups]
      exact List.mem_singleton_self _)
  change ∃ index : Fin tableSize,
    fromElements ((toElements sourceComponent.rowInputVar.message).map env) =
      rowOfIndex index.val at hquery
  rw [ProvableType.fromElements_eval_toElements] at hquery
  exact hquery

theorem sourceInteraction_mem_spec
    {table : Table FGL} (h_component : table.component = sourceComponent)
    (h_constraints : table.Constraints) {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith BinaryExtensionTableChannel.toRaw) :
    ∃ message : BinaryExtensionTableMessage FGL,
      binaryExtensionTable.Spec message ∧
        interaction.msg = (toElements message).toArray := by
  have h_ops :
      table.component.operations.interactionsWith BinaryExtensionTableChannel.toRaw =
        [((BinaryExtensionTableChannel.emitted sourceComponent.rowInputVar.multiplicity
          sourceComponent.rowInputVar.message).toRaw)] := by
    simpa only [h_component] using sourceComponent_interactionsWith
  simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_ops, List.map_singleton, List.mem_flatMap, List.mem_singleton] at h_mem
  obtain ⟨row, h_row, rfl⟩ := h_mem
  refine ⟨eval (table.environment row) sourceComponent.rowInputVar.message,
    sourceComponent_spec_of_constraints _ (by
      simpa only [h_component] using h_constraints row h_row), ?_⟩
  change ((toElements sourceComponent.rowInputVar.message).map
    (table.environment row)).toArray = _
  rw [← ProvableType.toElements_eval]

theorem source_input_message (row : SourceRow FGL) (data : ProverData FGL) :
    eval (Environment.fromInput row data) sourceComponent.rowInputVar.message = row.message := by
  rw [← eval_source_message]
  exact congrArg SourceRow.message (ProvableType.eval_fromInput_varFromOffset_zero row data)

theorem source_input_multiplicity (row : SourceRow FGL) (data : ProverData FGL) :
    eval (Environment.fromInput row data)
      sourceComponent.rowInputVar.multiplicity = row.multiplicity := by
  rw [← eval_source_multiplicity]
  exact congrArg SourceRow.multiplicity (ProvableType.eval_fromInput_varFromOffset_zero row data)

theorem source_constraints_fromInput (row : SourceRow FGL) (data : ProverData FGL)
    (h : binaryExtensionTable.Spec row.message) :
    sourceComponent.operations.ConstraintsHold (Environment.fromInput row data) := by
  refine ⟨?_, ?_⟩
  · intro expression hmem
    rw [sourceComponent_constraints] at hmem
    exact False.elim (List.not_mem_nil _ hmem)
  · intro query hmem
    rw [sourceComponent_lookups] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    change ∃ index : Fin tableSize,
      fromElements ((toElements sourceComponent.rowInputVar.message).map
        (Environment.fromInput row data)) = rowOfIndex index.val
    rw [ProvableType.fromElements_eval_toElements, source_input_message]
    exact h

theorem source_interaction_fromInput (row : SourceRow FGL) (data : ProverData FGL) :
    ((BinaryExtensionTableChannel.emitted sourceComponent.rowInputVar.multiplicity
      sourceComponent.rowInputVar.message).toRaw).eval (Environment.fromInput row data) =
        BinaryExtensionTableChannel.pushedIfValue row.multiplicity row.message := by
  change ((BinaryExtensionTableChannel.pushedIf sourceComponent.rowInputVar.multiplicity
    sourceComponent.rowInputVar.message).toRaw).eval _ = _
  rw [Channel.eval_pushedIf, source_input_message, source_input_multiplicity]

end ZiskFv.AirsClean.BinaryExtensionTableSlice
