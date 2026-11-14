import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.BinaryTable
import ZiskFv.Channels.BinaryTable

/-!
# `BinaryTable` static provider slice

The BinaryTable channel provider is backed by the exact decoded-row
`binaryTable` model. It owns table membership; Binary consumers only emit
negative messages, and a finished channel transports this fact.

## Trust note

No axioms. Soundness derives exact `binaryTable.Spec` membership from the
static lookup. The identical completeness-side membership premise supplies a
constructible static-table index and is not a soundness assumption.
-/

namespace ZiskFv.AirsClean.BinaryTableSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.BinaryTable
open ZiskFv.Channels.BinaryTable

@[circuit_norm]
def main (message : BinaryTableMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic binaryTable) message
  BinaryTableChannel.push message

def circuit : GeneralFormalCircuit FGL BinaryTableMessage unit where
  name := "BinaryTableSlice125"
  main := main
  channelsWithRequirements := [BinaryTableChannel.toRaw]
  exposedChannels message _ :=
    expose BinaryTableChannel [BinaryTableChannel.pushed message]
  Assumptions := fun _ _ => True
  Spec := fun message _ _ => binaryTable.Spec message
  ProverAssumptions := fun message _ _ => binaryTable.Spec message
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [BinaryTableChannel]
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

def component : Component FGL := { circuit }

theorem component_interactionsWith_binaryTableChannel :
    component.operations.interactionsWith BinaryTableChannel.toRaw =
      [((BinaryTableChannel.pushed component.rowInputVar).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryTableChannel.toRaw,
      [((BinaryTableChannel.pushed component.rowInputVar).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

/-- Virtual `lookup_proves` collects the fixed tuple; the actual packed
    producer emits `VirtualTable.multiplicity[lane]` unchanged
    (`std_virtual_table.pil:435,530`). This is its target-bus projection. -/
structure SourceRow (F : Type) where
  message : BinaryTableMessage F
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
  lookup (Table.fromStatic binaryTable) row.message
  BinaryTableChannel.emit row.multiplicity row.message

/-- Exact source tuple membership is checked before emitting the source's
    unrestricted multiplicity. In particular zero and `-1` are not silently
    replaced by `1`; balance, not a new validator, identifies useful providers. -/
def sourceCircuit : GeneralFormalCircuit FGL SourceRow unit where
  name := "BinaryTableSource125"
  main := sourceMain
  channelsWithRequirements := [BinaryTableChannel.toRaw]
  exposedChannels row _ :=
    expose BinaryTableChannel
      [BinaryTableChannel.emitted row.multiplicity row.message]
  Assumptions := fun _ _ => True
  Spec := fun row _ _ => binaryTable.Spec row.message
  ProverAssumptions := fun row _ _ => binaryTable.Spec row.message
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [BinaryTableChannel]
  completeness := by
    circuit_proof_start [Lookup.completeness_def, BinaryTableChannel]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

/-- Production uses `virtual BinaryTable(BINARY_TABLE_SIZE)`
    (`zisk/pil/zisk.pil:121`), not the template's default `2^23`.
    Only the source multiplicity column is writable. -/
def sourceFixedColumns : IndexedFixedColumns FGL 1 where
  capacity := tableSize
  capacity_pos := by norm_num [tableSize]
  effectiveWidth := 8
  fixedWidth := 7
  layout slot :=
    if h : slot.val < 7 then .inr ⟨slot.val, h⟩ else .inl 0
  values slot index := (toElements (rowOfIndex index.val))[slot.val]

def sourceComponent : Component FGL :=
  { circuit := sourceCircuit, rawWidth := 1, fixedColumns := some sourceFixedColumns }

private theorem sourceRow_toArray (message : BinaryTableMessage FGL)
    (multiplicity : FGL) :
    (toElements ({ message, multiplicity } : SourceRow FGL)).toArray =
      (toElements message).toArray ++ #[multiplicity] := by
  cases message
  rfl

private theorem sourceFixedColumns_multiplicity_layout :
    sourceFixedColumns.layout (⟨7, by decide⟩ : Fin 8) = .inl 0 := by
  rfl

/-- The materialized row is the exact production tuple with unchanged raw
    multiplicity, for every production index and every field value. -/
theorem sourceFixedColumns_materialize (index : Fin tableSize) (multiplicity : FGL) :
    sourceFixedColumns.materialize index.val #[multiplicity] =
      (toElements ({ message := rowOfIndex index.val, multiplicity } :
        SourceRow FGL)).toArray := by
  rw [sourceRow_toArray]
  have hsize : (toElements (rowOfIndex index.val)).toArray.size = 7 :=
    Vector.size_toArray _
  apply Array.ext
  · rw [IndexedFixedColumns.materialize_size, Array.size_append, hsize]
    rfl
  · intro i hi hi'
    have h_i : i < 8 := by simpa only [IndexedFixedColumns.materialize_size] using hi
    by_cases hslot : i < 7
    · rw [Array.getElem_append_left (by simpa only [hsize] using hslot)]
      simp only [IndexedFixedColumns.materialize, Array.getElem_ofFn,
        sourceFixedColumns, IndexedFixedColumns.fixedAt, dif_pos hslot,
        Nat.mod_eq_of_lt index.isLt, Vector.getElem_toArray]
    · have hi7 : i = 7 := by omega
      subst i
      rw [Array.getElem_append_right (by simpa only [hsize] using (Nat.le_refl 7))]
      simp only [hsize, Nat.sub_self]
      rewrite [IndexedFixedColumns.materialize]
      rewrite [Array.getElem_ofFn]
      rewrite [sourceFixedColumns_multiplicity_layout]
      rfl

theorem eval_sourceFixedColumns (index : Fin tableSize) (multiplicity : FGL)
    (data : ProverData FGL) :
    eval (Environment.fromArray
      (sourceFixedColumns.materialize index.val #[multiplicity]) data)
      sourceComponent.rowInputVar =
        ({ message := rowOfIndex index.val, multiplicity } : SourceRow FGL) := by
  rw [sourceFixedColumns_materialize]
  exact ProvableType.eval_fromInput_varFromOffset_zero _ _

theorem sourceComponent_interactionsWith :
    sourceComponent.operations.interactionsWith BinaryTableChannel.toRaw =
      [((BinaryTableChannel.emitted sourceComponent.rowInputVar.multiplicity
          sourceComponent.rowInputVar.message).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryTableChannel.toRaw,
      [((BinaryTableChannel.emitted sourceComponent.rowInputVar.multiplicity
          sourceComponent.rowInputVar.message).toRaw)]⟩ ∈ sourceComponent.exposedChannels
  simp only [sourceComponent, sourceCircuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

theorem sourceComponent_constraints :
    sourceComponent.operations.constraints = [] := by
  rw [Component.constraints_eq]
  rfl

theorem sourceComponent_lookups :
    sourceComponent.operations.lookups =
      [{ table := (Table.fromStatic binaryTable).toRaw
         entry := toElements sourceComponent.rowInputVar.message }] := by
  rw [Component.lookups_eq]
  rfl

theorem sourceComponent_interactions :
    sourceComponent.operations.interactions =
      [((BinaryTableChannel.emitted sourceComponent.rowInputVar.multiplicity
          sourceComponent.rowInputVar.message).toRaw)] := by
  rw [Component.interactions_eq]
  rfl

/-- Every meaningful source row, with any source multiplicity, has a
    constructive completeness witness. No membership premise is requested. -/
theorem sourceRow_constructible (index : Fin tableSize) (multiplicity : FGL)
    (data : ProverData FGL) (hint : ProverHint FGL) :
    sourceCircuit.ProverAssumptions
      { message := rowOfIndex index.val, multiplicity } data hint := by
  exact ⟨index, rfl⟩

/-- Provider membership follows from the actual checked lookup operations,
    independently of channel soundness (whose guarantees remain `True`). -/
theorem sourceComponent_spec_of_constraints (env : Environment FGL)
    (h : sourceComponent.operations.ConstraintsHold env) :
    binaryTable.Spec (eval env sourceComponent.rowInputVar.message) := by
  have hg : sourceComponent.operations.FullGuarantees env := by
    intro interaction hmem
    rw [sourceComponent_interactions] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    simp [AbstractInteraction.Guarantees, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
  have hs := (Component.weakSoundness (component := sourceComponent) (env := env)
    (by trivial) h hg).1
  change binaryTable.Spec (sourceComponent.rowInput env).message at hs
  have he : eval env sourceComponent.rowInputVar.message =
      (sourceComponent.rowInput env).message := by
    rw [← eval_source_message]
    exact congrArg SourceRow.message
      (eval_varFromOffset_valueFromOffset SourceRow 0 env)
  rw [he]
  exact hs

/-- Exact concrete producer tuple, retaining the actual source multiplicity. -/
theorem sourceInteraction_mem_spec
    {table : Table FGL} (h_component : table.component = sourceComponent)
    (h_constraints : table.Constraints) {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith BinaryTableChannel.toRaw) :
    ∃ message : BinaryTableMessage FGL,
      binaryTable.Spec message ∧ interaction.msg = (toElements message).toArray := by
  have h_ops :
      table.component.operations.interactionsWith BinaryTableChannel.toRaw =
        [((BinaryTableChannel.emitted sourceComponent.rowInputVar.multiplicity
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

/-- The actual source lookup constraints are constructible from an exact
    source row, without assumptions about channel soundness or prover data. -/
theorem source_constraints_fromInput (row : SourceRow FGL) (data : ProverData FGL)
    (h : binaryTable.Spec row.message) :
    sourceComponent.operations.ConstraintsHold (Environment.fromInput row data) := by
  refine ⟨?_, ?_⟩
  · intro expression hmem
    rw [sourceComponent_constraints] at hmem
    cases hmem
  · intro query hmem
    rw [sourceComponent_lookups] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    apply (Table.fromStatic binaryTable).toRaw.implied_by_completeness
    change Lookup.Completeness
      { table := (Table.fromStatic binaryTable).toRaw
        entry := toElements sourceComponent.rowInputVar.message }
      (Environment.fromInput row data)
    apply (Lookup.completeness_def (Table.fromStatic binaryTable)
      (Environment.fromInput row data) sourceComponent.rowInputVar.message).mpr
    change binaryTable.Spec
      (eval (Environment.fromInput row data) sourceComponent.rowInputVar.message)
    rw [source_input_message]
    exact h

theorem source_interaction_fromInput (row : SourceRow FGL) (data : ProverData FGL) :
    ((BinaryTableChannel.emitted sourceComponent.rowInputVar.multiplicity
      sourceComponent.rowInputVar.message).toRaw).eval (Environment.fromInput row data) =
        BinaryTableChannel.pushedIfValue row.multiplicity row.message := by
  change ((BinaryTableChannel.pushedIf sourceComponent.rowInputVar.multiplicity
    sourceComponent.rowInputVar.message).toRaw).eval _ = _
  rw [Channel.eval_pushedIf, source_input_message, source_input_multiplicity]

end ZiskFv.AirsClean.BinaryTableSlice
