import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.SpecifiedRangesSlice
import ZiskFv.AirsClean.RegisterStepRangeSlice

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- The lookup-aware ArithMul provider component used by the full ensemble. -/
@[reducible]
def arithMulProviderComponent : Component FGL :=
  ZiskFv.AirsClean.ArithMul.componentComplete

/-- Concrete component classification for the row-coherent full Clean
    ensemble. Components appear newest-first after the empty verifier table,
    matching Clean's `SoundEnsemble.addTable` list discipline. -/
theorem component_mem_fullRv64im_cases
    {length : ℕ} {program : Program length}
    {component : Component FGL}
    (h_mem : component ∈ (fullRv64imEnsemble length program).ensemble.allTables) :
    component = (fullRv64imEnsemble length program).ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.RegisterBoundary.component
      ∨ component = ZiskFv.AirsClean.MemAlignReadByte.component
      ∨ component = ZiskFv.AirsClean.MemAlignByte.component
      ∨ component = ZiskFv.AirsClean.MemAlign.component
      ∨ component = ZiskFv.AirsClean.MemAlignRangeSlice.component
      ∨ component = ZiskFv.AirsClean.MemAlignRomSlice.component
      ∨ component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
      ∨ component = ZiskFv.AirsClean.SpecifiedRangesSlice.component
      ∨ component = ZiskFv.AirsClean.RegisterStepRangeSlice.component
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
  -- `h_mem` is the `allTables`-ordered disjunction (verifier :: newest-first tables); `tauto`
  -- reorders it into the conclusion's ordering, which is robust to the added RegisterBoundary arm.
  tauto

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
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
      SoundEnsemble.addFinishedChannel_channels, SoundEnsemble.addTable_channels,
      SoundEnsemble.empty_channels])
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
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
      SoundEnsemble.addFinishedChannel_channels, SoundEnsemble.addTable_channels,
      SoundEnsemble.empty_channels])
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
    change OpBusChannel.toRaw ∉ [MemBusChannel.toRaw, MemAlignRomChannel.toRaw,
      MemAlignRangeChannel.toRaw]
    intro h
    have h' : OpBusChannel.toRaw = MemBusChannel.toRaw ∨
        OpBusChannel.toRaw = MemAlignRomChannel.toRaw ∨
        OpBusChannel.toRaw = MemAlignRangeChannel.toRaw := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
    rcases h' with h | h | h
    · have h_name := congrArg (fun c : RawChannel FGL => c.name) h
      simp [OpBusChannel, MemBusChannel, Channel.toRaw] at h_name
    · have h_name := congrArg (fun c : RawChannel FGL => c.name) h
      simp [OpBusChannel, MemAlignRomChannel, Channel.toRaw] at h_name
    · have h_name := congrArg (fun c : RawChannel FGL => c.name) h
      simp [OpBusChannel, MemAlignRangeChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The bus-133 static slice owns no operation-bus interaction. -/
theorem memAlignRangeSlice_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRangeSlice.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignRangeSlice.component.circuit.channels := by
    change OpBusChannel.toRaw ∉ [MemAlignRangeChannel.toRaw]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name)
      (by simpa only [List.mem_singleton] using h :
        OpBusChannel.toRaw = MemAlignRangeChannel.toRaw)
    simp [OpBusChannel, MemAlignRangeChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The bus-133 static slice owns no operation-bus interaction. -/
theorem memAlignRomSlice_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRomSlice.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignRomSlice.component.circuit.channels := by
    change OpBusChannel.toRaw ∉ [MemAlignRomChannel.toRaw]
    intro h
    have h' : OpBusChannel.toRaw = MemAlignRomChannel.toRaw := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h'
    simp [OpBusChannel, MemAlignRomChannel, Channel.toRaw] at h_name
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
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is RegisterBoundary has no operation-bus interactions
    (it emits only on the memory bus). -/
theorem registerBoundary_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.RegisterBoundary.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.RegisterBoundary.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.RegisterBoundary.component,
      ZiskFv.AirsClean.RegisterBoundary.circuit,
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

/-- The static 16-bit range-slice provider owns only bus 103, so it cannot
    contribute an operation-bus interaction. -/
theorem specifiedRangesSlice_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.SpecifiedRangesSlice.component.circuit.channels := by
    change OpBusChannel.toRaw ∉ [SpecifiedRangesSliceChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, SpecifiedRangesSliceChannel, Channel.toRaw] at h_name
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
      ZiskFv.AirsClean.ArithMul.componentComplete_channels]
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

/-- The static 16-bit range-slice provider owns only bus 103, so it cannot
    contribute a memory-bus interaction. -/
theorem specifiedRangesSlice_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.SpecifiedRangesSlice.component.circuit.channels := by
    change MemBusChannel.toRaw ∉ [SpecifiedRangesSliceChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemBusChannel, SpecifiedRangesSliceChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The bus-133 static slice owns no memory-bus interaction. -/
theorem memAlignRangeSlice_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRangeSlice.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignRangeSlice.component.circuit.channels := by
    change MemBusChannel.toRaw ∉ [MemAlignRangeChannel.toRaw]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name)
      (by simpa only [List.mem_singleton] using h :
        MemBusChannel.toRaw = MemAlignRangeChannel.toRaw)
    simp [MemBusChannel, MemAlignRangeChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The bus-133 static slice owns no memory-bus interaction. -/
theorem memAlignRomSlice_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRomSlice.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignRomSlice.component.circuit.channels := by
    change MemBusChannel.toRaw ∉ [MemAlignRomChannel.toRaw]
    intro h
    have h' : MemBusChannel.toRaw = MemAlignRomChannel.toRaw := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h'
    simp [MemBusChannel, MemAlignRomChannel, Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-! ## Empty bus-133 surfaces inside the full ensemble -/

private theorem memAlignRomChannel_ne_memBus :
    MemAlignRomChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun c : RawChannel FGL => c.name) h
  simp [MemAlignRomChannel, MemBusChannel, Channel.toRaw] at h_name

private theorem memAlignRomChannel_ne_opBus :
    MemAlignRomChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun c : RawChannel FGL => c.name) h
  simp [MemAlignRomChannel, OpBusChannel, Channel.toRaw] at h_name

private theorem memAlignRomChannel_ne_ranges :
    MemAlignRomChannel.toRaw ≠ SpecifiedRangesSliceChannel.toRaw := by
  intro h
  have h_name := congrArg (fun c : RawChannel FGL => c.name) h
  simp [MemAlignRomChannel, SpecifiedRangesSliceChannel, Channel.toRaw] at h_name

private theorem memAlignRomChannel_ne_memAlignRange :
    MemAlignRomChannel.toRaw ≠ MemAlignRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun c : RawChannel FGL => c.name) h
  simp [MemAlignRomChannel, MemAlignRangeChannel, Channel.toRaw] at h_name

theorem memAlignRangeSlice_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRangeSlice.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [MemAlignRangeChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_memAlignRange

private theorem specifiedRangesSliceChannel_ne_memAlignRange :
    SpecifiedRangesSliceChannel.toRaw ≠ MemAlignRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun c : RawChannel FGL => c.name) h
  simp [SpecifiedRangesSliceChannel, MemAlignRangeChannel, Channel.toRaw] at h_name

theorem memAlignRangeSlice_table_interactionsWith_specifiedRanges_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRangeSlice.component) :
    table.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change SpecifiedRangesSliceChannel.toRaw ∉ [MemAlignRangeChannel.toRaw]
  simp only [List.mem_singleton]
  exact specifiedRangesSliceChannel_ne_memAlignRange

theorem registerBoundary_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.RegisterBoundary.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_memBus

theorem memAlignReadByte_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_memBus

theorem memAlignByte_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_memBus

theorem mem_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [MemBusChannel.toRaw, SpecifiedRangesSliceChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact memAlignRomChannel_ne_memBus h
  · rcases h with h | h
    · exact memAlignRomChannel_ne_ranges h
    · simp at h

theorem specifiedRangesSlice_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [SpecifiedRangesSliceChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_ranges

theorem arithDiv_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithDiv.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ ([] : List (RawChannel FGL))
  simp

theorem arithMul_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = arithMulProviderComponent) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component, arithMulProviderComponent,
    ZiskFv.AirsClean.ArithMul.componentComplete_channels]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_opBus

theorem staticBinaryExtension_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = shiftStaticLookupComponent) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_opBus

theorem staticBinary_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_opBus

theorem binaryAdd_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  exact memAlignRomChannel_ne_opBus

theorem main_table_interactionsWith_memAlignRom_nil
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉
    [MemBusChannel.toRaw, OpBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
  intro h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact memAlignRomChannel_ne_memBus h
  · rcases h with h | h
    · exact memAlignRomChannel_ne_opBus h
    · rcases h with h | h
      · have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
        change "MemAlignRom133" = "SpecifiedRangesSlice102" at h_name
        simp at h_name
      · simp at h


/-- The bus-102 register-step slice exposes only its own channel. -/
theorem registerStepRangeSlice_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.RegisterStepRangeSlice.component.circuit.channels := by
    change OpBusChannel.toRaw ∉
      [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [OpBusChannel, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel,
      Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The bus-102 register-step slice exposes only its own channel. -/
theorem registerStepRangeSlice_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.RegisterStepRangeSlice.component.circuit.channels := by
    change MemBusChannel.toRaw ∉
      [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    simp [MemBusChannel, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel,
      Channel.toRaw] at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The bus-102 register-step slice exposes only its own channel. -/
theorem registerStepRangeSlice_table_interactionsWith_memAlignRom_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component) :
    table.interactionsWith MemAlignRomChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change MemAlignRomChannel.toRaw ∉
    [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
  simp only [List.mem_singleton]
  intro h
  have h_name := congrArg (fun c : RawChannel FGL => c.name) h
  simp [MemAlignRomChannel, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel,
    Channel.toRaw] at h_name

/-- `RegisterBoundary` carries no bus-102 interactions. -/
theorem registerBoundary_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.RegisterBoundary.component) :
    table.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉
        ZiskFv.AirsClean.RegisterBoundary.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.RegisterBoundary.component,
      ZiskFv.AirsClean.RegisterBoundary.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The static `Binary` lookup table carries no bus-102 interactions: it exposes only the
    operation bus. -/
theorem staticBinary_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent) :
    table.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice102" = "OperationBus" at h_name
  simp at h_name

/-- `MemAlignReadByte` carries no bus-102 interactions. -/
theorem memAlignReadByte_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignReadByte.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component, ZiskFv.AirsClean.MemAlignReadByte.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `MemAlignByte` carries no bus-102 interactions. -/
theorem memAlignByte_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignByte.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component, ZiskFv.AirsClean.MemAlignByte.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `MemAlign` carries no bus-102 interactions. -/
theorem memAlign_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.MemAlign.component.circuit.channels := by
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [MemBusChannel.toRaw, MemAlignRomChannel.toRaw,
      MemAlignRangeChannel.toRaw]
    intro h
    have h' : ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = MemBusChannel.toRaw ∨
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = MemAlignRomChannel.toRaw ∨
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = MemAlignRangeChannel.toRaw := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
    rcases h' with h' | h' | h'
    · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
      change "SpecifiedRangesSlice102" = "MemoryBus" at h_name
      simp at h_name
    · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
      change "SpecifiedRangesSlice102" = "MemAlignRom133" at h_name
      simp at h_name
    · have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h'
      change "SpecifiedRangesSlice102" = "MemAlignRange107" at h_name
      simp at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `MemAlignRangeSlice` carries no bus-102 interactions. -/
theorem memAlignRangeSlice_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRangeSlice.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignRangeSlice.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignRangeSlice.component, ZiskFv.AirsClean.MemAlignRangeSlice.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel,
      ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `MemAlignRomSlice` carries no bus-102 interactions. -/
theorem memAlignRomSlice_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRomSlice.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.MemAlignRomSlice.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignRomSlice.component, ZiskFv.AirsClean.MemAlignRomSlice.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel,
      ZiskFv.Channels.MemAlignRom.MemAlignRomChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `SpecifiedRangesSlice` carries no bus-102 interactions. -/
theorem specifiedRangesSlice_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.SpecifiedRangesSlice.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.SpecifiedRangesSlice.component, ZiskFv.AirsClean.SpecifiedRangesSlice.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel,
      ZiskFv.Channels.SpecifiedRanges.SpecifiedRangesSliceChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `ArithDiv` carries no bus-102 interactions. -/
theorem arithDiv_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithDiv.component) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ ZiskFv.AirsClean.ArithDiv.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.ArithDiv.component, ZiskFv.AirsClean.ArithDiv.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `ArithMul`'s provider carries no bus-102 interactions: it exposes only the operation bus. -/
theorem arithMul_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = arithMulProviderComponent) :
    table.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ arithMulProviderComponent.circuit.channels := by
    rw [arithMulProviderComponent,
      ZiskFv.AirsClean.ArithMul.componentComplete_channels]
    simp only [List.mem_singleton]
    intro h
    have h_name := congrArg (fun c : RawChannel FGL => c.name) h
    change "SpecifiedRangesSlice102" = "OperationBus" at h_name
    simp at h_name
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- `Mem` carries no bus-102 interactions: it uses the memory bus and the 16-bit range slice. -/
theorem mem_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
      ZiskFv.AirsClean.Mem.circuitWithDualMemBus,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, MemBusChannel,
      ZiskFv.Channels.SpecifiedRanges.SpecifiedRangesSliceChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- The static `BinaryExtension` shift table carries no bus-102 interactions. -/
theorem staticBinaryExtension_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent) :
    table.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
  simp only [List.mem_singleton]
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice102" = "OperationBus" at h_name
  simp at h_name

/-- `BinaryAdd` carries no bus-102 interactions. -/
theorem binaryAdd_table_interactionsWith_registerStepRange_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component) :
    table.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
  have h_not :
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉
        ZiskFv.AirsClean.BinaryAdd.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.BinaryAdd.component,
      ZiskFv.AirsClean.BinaryAdd.circuit,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel, OpBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

end ZiskFv.AirsClean.FullEnsemble
