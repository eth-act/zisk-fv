import ZiskFv.Compliance.TraceLevelExport.RawProgramDecode
import ZiskFv.Compliance.TraceLevelExport.SailRetireChain
import ZiskFv.Compliance.JalrSpinRootSoundness

/-!
# Physical endpoints on the existing supported execution domain

These results consume the existing `RowDecode`/`StepRowsAligned` evidence, not a
new parser-success, whole-program-support, or Main-height premise. In particular,
`programDecode_of_rawProgramDecode` followed by `rowDecode_of_programDecode`
provides exactly the decode input used here from the existing raw-program API.

An architectural step starts at its old index. Its producer is that index or,
only for a two-row JALR, the next index. `StepRowsAligned` excludes the latter
case only for nonfinal steps. Thus the exclusive physical endpoint is the last
producer plus one, not necessarily `trace.numInstructions`. The actual Main
table also contains the producer's successor; it is not the physical endpoint.

The final section reuses the existing accepted ADDI/JALR fixture. It makes no
claim that this fixture supplies a `RawProgramDecode` family or that the old
ROM-image binding entails successful parsing of every raw program word.
-/

namespace ZiskFv.Compliance.ExecutionSpanLegacy

variable {numInstructions : Nat} {trace : AcceptedZiskTrace numInstructions}

/-- The old JALR placement permits exactly one or two physical producer rows. -/
theorem jalr_finish_eq_index_or_succ
    {i : Fin trace.numInstructions} {imm : BitVec 12} {rs1 : regidx}
    {offset : BitVec 64} (rows : JalrLoweringRows trace i imm rs1 offset) :
    rows.finish.val = i.val ∨ rows.finish.val = i.val + 1 := by
  have hstart := rows.architectural_start
  rcases rows.lowering with ⟨heq, _⟩ | ⟨hsucc, _⟩
  · left
    exact (congrArg Fin.val heq).symm.trans hstart
  · right
    exact hsucc.symm.trans (congrArg (fun k : Nat => k + 1) hstart)

/-- All old dispatch arms have a producer at their start or its immediate successor. -/
theorem producer_eq_index_or_succ
    (i : Fin trace.numInstructions) (zs : ZiskStep trace i)
    (rd : RowDecode trace i zs) :
    stepProducerRow i zs rd = i.val ∨ stepProducerRow i zs rd = i.val + 1 := by
  cases zs <;> first
    | exact Or.inl rfl
    | exact jalr_finish_eq_index_or_succ rd.rows

/-- Successor availability comes from the existing decode fields, not `main_height`. -/
theorem producer_has_successor
    (i : Fin trace.numInstructions) (zs : ZiskStep trace i)
    (rd : RowDecode trace i zs) :
    stepProducerRow i zs rd + 1 < trace.mainTable.table.length := by
  cases zs <;> exact rd.h_idx

/-- The old alignment condition says nothing about the final producer. -/
theorem rowsAligned_iff_nonfinal_producer
    (zs : ∀ i : Fin trace.numInstructions, ZiskStep trace i)
    (rd : ∀ i : Fin trace.numInstructions, RowDecode trace i (zs i)) :
    StepRowsAligned trace zs rd ↔
      ∀ i : Fin trace.numInstructions, i.val + 1 < trace.numInstructions →
        stepProducerRow i (zs i) (rd i) = i.val := by
  constructor
  · intro aligned i hi
    exact aligned i.val hi
  · intro aligned j hj
    exact aligned ⟨j, Nat.lt_of_succ_lt hj⟩ hj

/-- The exclusive physical endpoint of a final old-supported step is `n` or `n+1`. -/
theorem final_producer_end
    (i : Fin trace.numInstructions) (zs : ZiskStep trace i)
    (rd : RowDecode trace i zs) (hfinal : i.val + 1 = trace.numInstructions) :
    (stepProducerRow i zs rd + 1 = trace.numInstructions ∨
      stepProducerRow i zs rd + 1 = trace.numInstructions + 1) ∧
      stepProducerRow i zs rd + 1 < trace.mainTable.table.length := by
  refine ⟨?_, producer_has_successor i zs rd⟩
  rcases producer_eq_index_or_succ i zs rd with h | h
  · left
    omega
  · right
    omega

/-- Every old step's producer lies strictly before the last producer's endpoint. -/
theorem producer_before_final_end
    (zs : ∀ i : Fin trace.numInstructions, ZiskStep trace i)
    (rd : ∀ i : Fin trace.numInstructions, RowDecode trace i (zs i))
    (aligned : StepRowsAligned trace zs rd)
    (last : Fin trace.numInstructions)
    (hfinal : last.val + 1 = trace.numInstructions)
    (i : Fin trace.numInstructions) :
    stepProducerRow i (zs i) (rd i) < stepProducerRow last (zs last) (rd last) + 1 := by
  by_cases hi : i.val + 1 < trace.numInstructions
  · have hproducer := (rowsAligned_iff_nonfinal_producer zs rd).mp aligned i hi
    have hlast := producer_eq_index_or_succ last (zs last) (rd last)
    omega
  · have hilast : i = last := Fin.ext (by have := i.isLt; omega)
    subst i
    omega

/-- No physical row below the last producer's endpoint is skipped by the old spans.

The span of step `i` is the inclusive interval from `i.val` to its producer.
This is a placement fact only; it does not assert a parser domain for those rows.
-/
theorem physical_prefix_covered
    (zs : ∀ i : Fin trace.numInstructions, ZiskStep trace i)
    (rd : ∀ i : Fin trace.numInstructions, RowDecode trace i (zs i))
    (last : Fin trace.numInstructions)
    (hfinal : last.val + 1 = trace.numInstructions)
    (p : Nat) (hp : p < stepProducerRow last (zs last) (rd last) + 1) :
    ∃ i : Fin trace.numInstructions,
      i.val ≤ p ∧ p ≤ stepProducerRow i (zs i) (rd i) := by
  by_cases hpn : p < trace.numInstructions
  · let i : Fin trace.numInstructions := ⟨p, hpn⟩
    refine ⟨i, Nat.le_refl _, ?_⟩
    have hproducer := producer_eq_index_or_succ i (zs i) (rd i)
    change p ≤ stepProducerRow i (zs i) (rd i)
    change stepProducerRow i (zs i) (rd i) = p ∨
      stepProducerRow i (zs i) (rd i) = p + 1 at hproducer
    omega
  · exact ⟨last, by omega, by omega⟩

/-- Nonfinal alignment makes the old physical spans disjoint. -/
theorem physical_spans_disjoint
    (zs : ∀ i : Fin trace.numInstructions, ZiskStep trace i)
    (rd : ∀ i : Fin trace.numInstructions, RowDecode trace i (zs i))
    (aligned : StepRowsAligned trace zs rd)
    (i j : Fin trace.numInstructions) (hij : i.val < j.val) :
    stepProducerRow i (zs i) (rd i) < j.val := by
  have hi : i.val + 1 < trace.numInstructions := by have := j.isLt; omega
  rw [(rowsAligned_iff_nonfinal_producer zs rd).mp aligned i hi]
  exact hij

section ExistingAcceptedFinalJalr

open JalrSpinWitness JalrSpinRootSoundness

/-- The existing accepted final JALR produces at physical row 2, outside `Fin 2`. -/
theorem jalrSpin_final_producer :
    stepProducerRow jalrIndex (jalrSpinZiskStep jalrIndex)
      (rowDecode_of_programDecode jalrAcceptedTrace jalrIndex
        (programDecodes jalrIndex)) = 2 := by
  rfl

/-- The existing Main table contains the three lowering rows and one successor row. -/
theorem jalrSpin_main_height : jalrAcceptedTrace.mainTable.table.length = 4 := by
  rw [jalrAcceptedTrace_mainTable_eq]
  norm_num [jalrMainTable, AddSpinWitness.mainRowsTable, jalrMainRows]

/-- The old accepted/aligned domain does not bound final producers by the
architectural count. This is the pre-existing witness, not a new construction. -/
theorem jalrSpin_numInstructions_not_physical_boundary :
    StepRowsAligned jalrAcceptedTrace jalrSpinZiskStep
      (fun i => rowDecode_of_programDecode jalrAcceptedTrace i (programDecodes i)) ∧
      ¬ (∀ i : Fin jalrAcceptedTrace.numInstructions,
        stepProducerRow i (jalrSpinZiskStep i)
          (rowDecode_of_programDecode jalrAcceptedTrace i (programDecodes i)) <
            jalrAcceptedTrace.numInstructions) := by
  refine ⟨jalrRowsAligned, ?_⟩
  intro h
  have hlast := h jalrIndex
  rw [jalrSpin_final_producer] at hlast
  change 2 < 2 at hlast
  omega

/-- Exact endpoint comparison: architectural count 2, physical endpoint 3,
Main height 4. The last Main row is a successor, not an extra architectural step. -/
theorem jalrSpin_exact_physical_end :
    jalrAcceptedTrace.numInstructions = 2 ∧
      stepProducerRow jalrIndex (jalrSpinZiskStep jalrIndex)
        (rowDecode_of_programDecode jalrAcceptedTrace jalrIndex
          (programDecodes jalrIndex)) + 1 = 3 ∧
      jalrAcceptedTrace.mainTable.table.length = 4 := by
  exact ⟨rfl, congrArg (fun p : Nat => p + 1) jalrSpin_final_producer,
    jalrSpin_main_height⟩

end ExistingAcceptedFinalJalr

open Air.Flat ZiskFv.AirsClean.FullEnsemble

/-- The full ensemble has no repeated component identifier. The identifier is
used only to prove component-list uniqueness; it is not an acceptance premise.
The raw width separates the empty verifier from any equally named circuit. -/
private theorem full_component_identifiers_nodup
    (length : Nat) (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length) :
    (((fullRv64imEnsemble length program).ensemble.allTables).map
      (fun component => (component.circuit.name, component.rawWidth))).Nodup := by
  simp only [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
    Ensemble.allTables, SoundEnsemble.addTable_tables,
    SoundEnsemble.addFinishedChannel_tables]
  decide

/-- Positional component correspondence and the concrete ensemble's unique
component identifiers force all Main tables to be the selected Main table. -/
theorem all_main_tables_eq_selected
    (table : Table FGL) (hmem : table ∈ trace.witness.allTables)
    (hcomponent : table.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program) :
    table = trace.mainTable := by
  have hnodup :
      (trace.witness.allTables.map (fun table => table.component)).Nodup := by
    rw [trace.witness.allTables_map_component]
    exact List.Nodup.of_map
      (fun component : Component FGL => (component.circuit.name, component.rawWidth))
      (full_component_identifiers_nodup trace.programLength trace.program)
  exact List.inj_on_of_nodup_map hnodup hmem trace.mainTable_mem
    (hcomponent.trans trace.mainTable_component.symm)

/-- Recount the unchanged accepted witness up to a decode-supported producer.

For the final architectural step this count is the exact exclusive physical
endpoint. Global `main_height` is derived for every Main table by uniqueness,
not supplied as a new root promise. All other acceptance evidence is reused.
-/
noncomputable def recountAtProducer
    (i : Fin trace.numInstructions) (zs : ZiskStep trace i)
    (rd : RowDecode trace i zs) :
    AcceptedZiskTrace (stepProducerRow i zs rd + 1) where
  programLength := trace.programLength
  program := trace.program
  witness := trace.witness
  constraints_hold := trace.constraints_hold
  channels_balanced := trace.channels_balanced
  mem_replay_table := trace.mem_replay_table
  mem_replay_source_covers := trace.mem_replay_source_covers
  transitions_hold := trace.transitions_hold
  cyclic_successor_transitions_hold := trace.cyclic_successor_transitions_hold
  main_height := by
    intro table hmem hcomponent k
    rw [all_main_tables_eq_selected table hmem hcomponent]
    exact Nat.lt_trans k.isLt (producer_has_successor i zs rd)

/-- Recounting changes neither the committed raw witness nor its selected Main table. -/
theorem recountAtProducer_mainTable
    (i : Fin trace.numInstructions) (zs : ZiskStep trace i)
    (rd : RowDecode trace i zs) :
    (recountAtProducer i zs rd).mainTable = trace.mainTable := by
  rfl

end ZiskFv.Compliance.ExecutionSpanLegacy
