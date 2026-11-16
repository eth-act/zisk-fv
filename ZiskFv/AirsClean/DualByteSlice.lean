import ZiskFv.AirsClean.DualByteTable
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

namespace ZiskFv.AirsClean.DualByteSlice
open Goldilocks
open Air.Flat
open ZiskFv.Channels.DualByte

/-- `multiplicity` is the real unconstrained witness from dual_range.pil:15,
not an always-one surrogate for the virtual table's lookup count. -/
structure ProviderRow (F : Type) where
  byte_a : F
  byte_b : F
  multiplicity : F
deriving ProvableStruct

@[reducible]
def messageExpr (row : Var ProviderRow FGL) : DualByteMessage (Expression FGL) :=
  ⟨row.byte_a, row.byte_b⟩

theorem eval_messageExpr (env : Environment FGL) (row : ProviderRow (Expression FGL)) :
    eval env (messageExpr row) =
      (⟨(eval env row : ProviderRow FGL).byte_a,
        (eval env row : ProviderRow FGL).byte_b⟩ : DualByteMessage FGL) := by
  simp only [ProvableStruct.eval_eq_eval (α := ProviderRow),
    ProvableStruct.eval_eq_eval (α := DualByteMessage)]
  rfl

theorem eval_multiplicity (env : Environment FGL) (row : ProviderRow (Expression FGL)) :
    (eval env row : ProviderRow FGL).multiplicity = eval env row.multiplicity := by
  rw [ProvableStruct.eval_eq_eval (α := ProviderRow)]
  rfl

@[circuit_norm]
def main (row : Var ProviderRow FGL) : Circuit FGL Unit := do
  Circuit.lookup (Table.fromStatic DualByteTable.table) (messageExpr row)
  DualByteChannel.emit row.multiplicity (messageExpr row)

def circuit : GeneralFormalCircuit FGL ProviderRow unit where
  name := "DualByte88Provider"
  main := main
  channelsWithRequirements := [DualByteChannel.toRaw]
  exposedChannels row _ :=
    expose DualByteChannel [DualByteChannel.emitted row.multiplicity (messageExpr row)]
  Assumptions := fun _ _ => True
  Spec := fun row _ _ => DualByteTable.table.Spec ⟨row.byte_a, row.byte_b⟩
  ProverAssumptions := fun row _ _ => DualByteTable.table.Spec ⟨row.byte_a, row.byte_b⟩
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [DualByteChannel]
  completeness := by
    circuit_proof_start [DualByteChannel, Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

def component : Component FGL := { circuit }

theorem component_interactionsWith_dualByte :
    component.operations.interactionsWith DualByteChannel.toRaw =
      [(DualByteChannel.emitted component.rowInputVar.multiplicity
        (messageExpr component.rowInputVar)).toRaw] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨DualByteChannel.toRaw, _⟩ ∈ component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

/-- Exactly the fixed source rows in physical order, with one free witness
multiplicity per source row. The ensemble must supply the actual count witness;
this constructor does not claim arbitrary counts balance consumer traces. -/
def sourceRows (multiplicity : Fin 65536 → FGL) (i : Fin 65536) : ProviderRow FGL :=
  { byte_a := (DualByteTable.sourceRow i).byte_a
    byte_b := (DualByteTable.sourceRow i).byte_b
    multiplicity := multiplicity i }

theorem sourceRows_membership (multiplicity : Fin 65536 → FGL) (i : Fin 65536) :
    DualByteTable.table.Spec
      ⟨(sourceRows multiplicity i).byte_a, (sourceRows multiplicity i).byte_b⟩ := by
  apply (DualByteTable.table.contains_iff _).mp
  exact ⟨i, rfl⟩

theorem sourceRows_multiplicity (multiplicity : Fin 65536 → FGL) (i : Fin 65536) :
    (sourceRows multiplicity i).multiplicity = multiplicity i := rfl

/-- Actual source provider layout: A and B are fixed, and only multiplicity is
writable. The production packed source observer supplies their physical
locations; this component is the bus88 target projection, not a new table. -/
def sourceFixedColumns : IndexedFixedColumns FGL 1 where
  capacity := 65536
  capacity_pos := by decide
  effectiveWidth := 3
  fixedWidth := 2
  layout slot :=
    if h : slot.val < 2 then .inr ⟨slot.val, h⟩ else .inl 0
  values slot index := (toElements (DualByteTable.sourceRow index))[slot.val]

def sourceComponent : Component FGL :=
  { circuit, rawWidth := 1, fixedColumns := some sourceFixedColumns }

private theorem providerRow_toArray (byte_a byte_b multiplicity : FGL) :
    (toElements ({ byte_a, byte_b, multiplicity } : ProviderRow FGL)).toArray =
      (toElements (⟨byte_a, byte_b⟩ : DualByteMessage FGL)).toArray ++ #[multiplicity] := rfl

private theorem sourceFixedColumns_multiplicity_layout :
    sourceFixedColumns.layout (⟨2, by decide⟩ : Fin 3) = .inl 0 := rfl

theorem sourceFixedColumns_materialize (index : Fin 65536) (multiplicity : FGL) :
    sourceFixedColumns.materialize index.val #[multiplicity] =
      (toElements (sourceRows (fun _ => multiplicity) index)).toArray := by
  rw [providerRow_toArray]
  have hsize : (toElements (DualByteTable.sourceRow index)).toArray.size = 2 :=
    Vector.size_toArray _
  apply Array.ext
  · rw [IndexedFixedColumns.materialize_size, Array.size_append, hsize]
    rfl
  · intro i hi hi'
    have h_i : i < 3 := by simpa only [IndexedFixedColumns.materialize_size] using hi
    by_cases hslot : i < 2
    · rw [Array.getElem_append_left (by simpa only [hsize] using hslot)]
      simp only [IndexedFixedColumns.materialize, Array.getElem_ofFn,
        sourceFixedColumns, IndexedFixedColumns.fixedAt, dif_pos hslot,
        Nat.mod_eq_of_lt index.isLt, Vector.getElem_toArray]
    · have hi2 : i = 2 := by omega
      subst i
      rw [Array.getElem_append_right (by simpa only [hsize] using (Nat.le_refl 2))]
      simp only [hsize, Nat.sub_self]
      unfold IndexedFixedColumns.materialize
      rewrite [Array.getElem_ofFn]
      rewrite [sourceFixedColumns_multiplicity_layout]
      rfl

theorem eval_sourceFixedColumns (index : Fin 65536) (multiplicity : FGL)
    (data : ProverData FGL) :
    eval (Environment.fromArray
      (sourceFixedColumns.materialize index.val #[multiplicity]) data)
      sourceComponent.rowInputVar = sourceRows (fun _ => multiplicity) index := by
  rw [sourceFixedColumns_materialize]
  exact ProvableType.eval_fromInput_varFromOffset_zero _ _

theorem sourceComponent_interactionsWith :
    sourceComponent.operations.interactionsWith DualByteChannel.toRaw =
      [(DualByteChannel.emitted sourceComponent.rowInputVar.multiplicity
        (messageExpr sourceComponent.rowInputVar)).toRaw] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨DualByteChannel.toRaw, _⟩ ∈ sourceComponent.exposedChannels
  simp only [sourceComponent, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

theorem sourceComponent_constraints :
    sourceComponent.operations.constraints = [] := by
  rw [Component.constraints_eq]
  rfl

theorem sourceComponent_lookups :
    sourceComponent.operations.lookups =
      [{ table := (Table.fromStatic DualByteTable.table).toRaw
         entry := toElements (messageExpr sourceComponent.rowInputVar) }] := by
  rw [Component.lookups_eq]
  rfl

theorem sourceComponent_interactions :
    sourceComponent.operations.interactions =
      [(DualByteChannel.emitted sourceComponent.rowInputVar.multiplicity
        (messageExpr sourceComponent.rowInputVar)).toRaw] := by
  rw [Component.interactions_eq]
  rfl

theorem sourceRow_constructible (index : Fin 65536) (multiplicity : FGL)
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions (sourceRows (fun _ => multiplicity) index) data hint := by
  exact sourceRows_membership (fun _ => multiplicity) index

/-- Every source index and every raw witness multiplicity are constructible;
soundness membership is obtained from actual checked operations. -/
theorem sourceComponent_spec_of_constraints (env : Environment FGL)
    (h : sourceComponent.operations.ConstraintsHold env) :
    DualByteTable.table.Spec
      (eval env (messageExpr sourceComponent.rowInputVar)) := by
  have hg : sourceComponent.operations.FullGuarantees env := by
    intro interaction hmem
    rw [sourceComponent_interactions] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    simp [AbstractInteraction.Guarantees, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
  have hs := (Component.weakSoundness (component := sourceComponent) (env := env)
    (by trivial) h hg).1
  change DualByteTable.table.Spec
    ⟨(sourceComponent.rowInput env).byte_a, (sourceComponent.rowInput env).byte_b⟩ at hs
  have he : (eval env sourceComponent.rowInputVar : ProviderRow FGL) =
      sourceComponent.rowInput env :=
    eval_varFromOffset_valueFromOffset ProviderRow 0 env
  rw [eval_messageExpr, he]
  exact hs

theorem sourceInteraction_mem_spec
    {table : Table FGL} (h_component : table.component = sourceComponent)
    (h_constraints : table.Constraints) {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith DualByteChannel.toRaw) :
    ∃ message : DualByteMessage FGL,
      DualByteTable.table.Spec message ∧ interaction.msg = (toElements message).toArray := by
  have h_ops :
      table.component.operations.interactionsWith DualByteChannel.toRaw =
        [(DualByteChannel.emitted sourceComponent.rowInputVar.multiplicity
          (messageExpr sourceComponent.rowInputVar)).toRaw] := by
    simpa only [h_component] using sourceComponent_interactionsWith
  simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_ops, List.map_singleton, List.mem_flatMap, List.mem_singleton] at h_mem
  obtain ⟨row, h_row, rfl⟩ := h_mem
  refine ⟨eval (table.environment row) (messageExpr sourceComponent.rowInputVar),
    sourceComponent_spec_of_constraints _ (by
      simpa only [h_component] using h_constraints row h_row), ?_⟩
  change ((toElements (messageExpr sourceComponent.rowInputVar)).map
    (table.environment row)).toArray = _
  rw [← ProvableType.toElements_eval]

theorem source_input_message (row : ProviderRow FGL) (data : ProverData FGL) :
    eval (Environment.fromInput row data) (messageExpr sourceComponent.rowInputVar) =
      (⟨row.byte_a, row.byte_b⟩ : DualByteMessage FGL) := by
  rw [eval_messageExpr, ProvableType.eval_fromInput_varFromOffset_zero]

theorem source_input_multiplicity (row : ProviderRow FGL) (data : ProverData FGL) :
    eval (Environment.fromInput row data)
      sourceComponent.rowInputVar.multiplicity = row.multiplicity := by
  rw [← eval_multiplicity]
  exact congrArg ProviderRow.multiplicity (ProvableType.eval_fromInput_varFromOffset_zero row data)

theorem source_constraints_fromInput (row : ProviderRow FGL) (data : ProverData FGL)
    (h : DualByteTable.table.Spec (⟨row.byte_a, row.byte_b⟩ : DualByteMessage FGL)) :
    sourceComponent.operations.ConstraintsHold (Environment.fromInput row data) := by
  refine ⟨?_, ?_⟩
  · intro expression hmem
    rw [sourceComponent_constraints] at hmem
    cases hmem
  · intro query hmem
    rw [sourceComponent_lookups] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    apply (Table.fromStatic DualByteTable.table).toRaw.implied_by_completeness
    change Lookup.Completeness
      { table := (Table.fromStatic DualByteTable.table).toRaw
        entry := toElements (messageExpr sourceComponent.rowInputVar) }
      (Environment.fromInput row data)
    apply (Lookup.completeness_def (Table.fromStatic DualByteTable.table)
      (Environment.fromInput row data) (messageExpr sourceComponent.rowInputVar)).mpr
    change DualByteTable.table.Spec
      (eval (Environment.fromInput row data) (messageExpr sourceComponent.rowInputVar))
    rw [source_input_message]
    exact h

theorem source_interaction_fromInput (row : ProviderRow FGL) (data : ProverData FGL) :
    ((DualByteChannel.emitted sourceComponent.rowInputVar.multiplicity
      (messageExpr sourceComponent.rowInputVar)).toRaw).eval (Environment.fromInput row data) =
        DualByteChannel.pushedIfValue row.multiplicity ⟨row.byte_a, row.byte_b⟩ := by
  change ((DualByteChannel.pushedIf sourceComponent.rowInputVar.multiplicity
    (messageExpr sourceComponent.rowInputVar)).toRaw).eval _ = _
  rw [Channel.eval_pushedIf, source_input_message, source_input_multiplicity]

end ZiskFv.AirsClean.DualByteSlice
