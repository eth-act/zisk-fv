import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- The lookup-aware ArithMul provider component used by the full ensemble. -/
@[reducible]
def arithMulProviderComponent : Component FGL :=
  ZiskFv.AirsClean.ArithMul.componentWithArithTable

/-- Concrete component classification for the row-coherent full Clean
    ensemble. Components appear newest-first after the empty verifier table,
    matching Clean's `SoundEnsemble.addTable` list discipline. -/
theorem component_mem_fullRv64im_cases
    {length : ℕ} {program : Program length}
    {component : Component FGL}
    (h_mem : component ∈ (fullRv64imEnsemble length program).ensemble.allTables) :
    component = (fullRv64imEnsemble length program).ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.MemAlignReadByte.component
      ∨ component = ZiskFv.AirsClean.MemAlignByte.component
      ∨ component = ZiskFv.AirsClean.MemAlign.component
      ∨ component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
      ∨ component = ZiskFv.AirsClean.ArithDiv.component
      ∨ component = arithMulProviderComponent
      ∨ component = shiftStaticLookupComponent
      ∨ component = ZiskFv.AirsClean.Binary.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program := by
  simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
    at h_mem
  rcases h_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_memAlign)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_mem))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithDiv)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithMul))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binExt)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binary))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binaryAdd)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main)))))))))
  · cases h_empty

/-- Every concrete witness for the full RV64IM ensemble contains a table for
    the dual-aware mutable Mem component. This is only table selection: it
    does not assert chronological embedding of that table's projected rows
    into an accepted memory trace. -/
theorem exists_mem_table_of_fullRv64im_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    ∃ table ∈ witness.allTables,
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus := by
  have h_component_mem :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ∈
        (fullRv64imEnsemble length program).ensemble.allTables := by
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
  have h_in_map :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ∈
        witness.allTables.map (·.component) := by
    rw [witness.allTables_map_component]
    exact h_component_mem
  rcases List.mem_map.mp h_in_map with ⟨table, h_table, h_component⟩
  exact ⟨table, h_table, h_component⟩

/-- Every concrete witness for the full RV64IM ensemble contains the unified
    Main table. This is only table selection; row-level decode/provenance is
    supplied separately by `SailTrace`. -/
theorem exists_main_table_of_fullRv64im_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    ∃ table ∈ witness.allTables,
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program := by
  have h_component_mem :
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program ∈
        (fullRv64imEnsemble length program).ensemble.allTables := by
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
  have h_in_map :
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program ∈
        witness.allTables.map (·.component) := by
    rw [witness.allTables_map_component]
    exact h_component_mem
  rcases List.mem_map.mp h_in_map with ⟨table, h_table, h_component⟩
  exact ⟨table, h_table, h_component⟩

/-- Every concrete witness for the full RV64IM ensemble contains the
    lookup-aware Binary provider table. This is only table selection; opcode
    construction still resolves provider matches from channel balance. -/
theorem exists_binary_table_of_fullRv64im_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    ∃ table ∈ witness.allTables,
      table.component = ZiskFv.AirsClean.Binary.staticLookupComponent := by
  have h_component_mem :
      ZiskFv.AirsClean.Binary.staticLookupComponent ∈
        (fullRv64imEnsemble length program).ensemble.allTables := by
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
  have h_in_map :
      ZiskFv.AirsClean.Binary.staticLookupComponent ∈
        witness.allTables.map (·.component) := by
    rw [witness.allTables_map_component]
    exact h_component_mem
  rcases List.mem_map.mp h_in_map with ⟨table, h_table, h_component⟩
  exact ⟨table, h_table, h_component⟩

/-- Every concrete witness for the full RV64IM ensemble contains the
    lookup-aware BinaryExtension provider table. This is only table selection;
    opcode construction still resolves provider matches from channel balance. -/
theorem exists_binaryExtension_table_of_fullRv64im_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    ∃ table ∈ witness.allTables,
      table.component =
        shiftStaticLookupComponent := by
  have h_component_mem :
      shiftStaticLookupComponent ∈
        (fullRv64imEnsemble length program).ensemble.allTables := by
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
  have h_in_map :
      shiftStaticLookupComponent ∈
        witness.allTables.map (·.component) := by
    rw [witness.allTables_map_component]
    exact h_component_mem
  rcases List.mem_map.mp h_in_map with ⟨table, h_table, h_component⟩
  exact ⟨table, h_table, h_component⟩

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute operation-bus interactions. -/
theorem verifierTable_interactionsWith_opBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      OpBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute memory-bus interactions. -/
theorem verifierTable_interactionsWith_memBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      MemBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- Project the full ensemble's `BalancedChannels` hypothesis to the
    concrete operation-bus interaction list. -/
theorem opBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith OpBusChannel.toRaw) := by
  have h := h_balanced OpBusChannel.toRaw (by
    change OpBusChannel.toRaw ∈ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Project the full ensemble's `BalancedChannels` hypothesis to the
    concrete memory-bus interaction list. -/
theorem memBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith MemBusChannel.toRaw) := by
  have h := h_balanced MemBusChannel.toRaw (by
    change MemBusChannel.toRaw ∈ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-! ## Empty operation-bus surfaces inside the full ensemble -/

/-- A table whose component is MemAlignReadByte has no operation-bus
    interactions. -/
theorem memAlignReadByte_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.MemAlignReadByte.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
      ZiskFv.AirsClean.MemAlignReadByte.circuit,
      ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is MemAlignByte has no operation-bus
    interactions. -/
theorem memAlignByte_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.MemAlignByte.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
      ZiskFv.AirsClean.MemAlignByte.circuit,
      ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is MemAlign has no operation-bus interactions. -/
theorem memAlign_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.MemAlign.component.circuit.channels := by
    change OpBusChannel.toRaw ∉ [MemBusChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, MemBusChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is Mem has no operation-bus interactions. -/
theorem mem_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
      ZiskFv.AirsClean.Mem.circuitWithDualMemBus,
      ZiskFv.AirsClean.Mem.memWithDualMemBusElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is the current ArithDiv carry-chain component has
    no operation-bus interactions. DIV/REM op-bus surfaces are still bridged
    by the dedicated primary/secondary components outside the full ensemble. -/
theorem arithDiv_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithDiv.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.ArithDiv.component.circuit.channels := by
    change OpBusChannel.toRaw ∉ ([] : List (RawChannel FGL))
    simp
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-! ## Empty memory-bus surfaces inside the full ensemble -/

/-- A table whose component is BinaryAdd has no memory-bus interactions. -/
theorem binaryAdd_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.BinaryAdd.component.circuit.channels := by
    change MemBusChannel.toRaw ∉ [OpBusChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, MemBusChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is lookup-aware Binary has no memory-bus
    interactions. -/
theorem staticBinary_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Binary.staticLookupComponent) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.channels := by
    change MemBusChannel.toRaw ∉ [OpBusChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, MemBusChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is lookup-aware BinaryExtension has no memory-bus
    interactions. -/
theorem staticBinaryExtension_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component :
      table.component =
        shiftStaticLookupComponent) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        shiftStaticLookupComponent.circuit.channels := by
    change MemBusChannel.toRaw ∉ [OpBusChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, MemBusChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is ArithMul has no memory-bus interactions. -/
theorem arithMul_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = arithMulProviderComponent) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        arithMulProviderComponent.circuit.channels := by
    rw [arithMulProviderComponent,
      ZiskFv.AirsClean.ArithMul.componentWithArithTable_channels]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, MemBusChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is the current ArithDiv carry-chain component has
    no memory-bus interactions. -/
theorem arithDiv_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithDiv.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.ArithDiv.component.circuit.channels := by
    change MemBusChannel.toRaw ∉ ([] : List (RawChannel FGL))
    simp
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not


end ZiskFv.AirsClean.FullEnsemble
