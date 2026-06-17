import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec

/-!
# Full Clean ensemble balance projections

T7 needs canonical proofs to consume the full Clean ensemble directly,
rather than family-local ensembles.  This module exposes the first reusable
structural facts from `FullEnsemble.fullRv64imEnsemble`: the concrete table
classification and the balanced operation/memory channel projections.

## Trust note

No axioms.  These lemmas only unpack `EnsembleWitness.BalancedChannels` and
the `fullRv64imEnsemble` table list.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.SegmentContinuation (SeamContChannel)
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
      ∨ component = ZiskFv.AirsClean.Mem.bootComp
      ∨ component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
      ∨ component = ZiskFv.AirsClean.ArithDiv.component
      ∨ component = arithMulProviderComponent
      ∨ component = shiftStaticLookupComponent
      ∨ component = ZiskFv.AirsClean.Binary.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables]
    at h_mem
  rcases h_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_boot | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_memAlign)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_boot))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_mem)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithDiv))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithMul)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binExt))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binary)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binaryAdd))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main))))))))))
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
    simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables]
  have h_in_map :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ∈
        witness.allTables.map (·.component) := by
    rw [witness.allTables_map_component]
    exact h_component_mem
  rcases List.mem_map.mp h_in_map with ⟨table, h_table, h_component⟩
  exact ⟨table, h_table, h_component⟩

/-- Every concrete witness for the full RV64IM ensemble contains the unified
    Main table. This is only table selection; row-level decode/provenance is
    supplied separately by `ProgramBinding`. -/
theorem exists_main_table_of_fullRv64im_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    ∃ table ∈ witness.allTables,
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program := by
  have h_component_mem :
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program ∈
        (fullRv64imEnsemble length program).ensemble.allTables := by
    simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables]
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
    simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables]
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
    simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables]
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
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute memory-bus interactions. -/
theorem verifierTable_interactionsWith_memBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      MemBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal,
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
    change OpBusChannel.toRaw ∈
      [SeamContChannel.toRaw, MemBusChannel.toRaw, OpBusChannel.toRaw]
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
    change MemBusChannel.toRaw ∈
      [SeamContChannel.toRaw, MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Project the full ensemble's `BalancedChannels` hypothesis to the concrete
    cross-segment continuation seam interaction list (XCAP #103, route (b)).

    The seam channel is in `fullRv64imEnsemble.ensemble.channels` (the
    `addChannel` position), so `BalancedChannels` carries its balance as a
    conjunct — the SAME channel-balance trust class as the OpBus/MemBus
    projections above. This is the prerequisite that feeds the channel-level
    tag-chain derivation (`ZiskFv.Channels.SeamTagChain`) on the REAL ensemble.
    The seam channel is consumed only for its BALANCE; nothing consumes its
    guarantees (`SeamContChannel.Guarantees := True`). -/
theorem seam_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith SeamContChannel.toRaw) := by
  have h := h_balanced SeamContChannel.toRaw (by
    change SeamContChannel.toRaw ∈
      [SeamContChannel.toRaw, MemBusChannel.toRaw, OpBusChannel.toRaw]
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

/-- A table whose component is the seam BOOT endpoint (XCAP #103, route (b),
    L4.6) has no operation-bus interactions: it emits only the seam channel. -/
theorem bootComp_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.bootComp) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.Mem.bootComp.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Mem.bootComp,
      ZiskFv.AirsClean.Mem.bootCircuit, OpBusChannel, SeamContChannel,
      Channel.toRaw, RawChannel.mk.injEq]
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

/-- A table whose component is the seam BOOT endpoint (XCAP #103, route (b),
    L4.6) has no memory-bus interactions: it emits only the seam channel. -/
theorem bootComp_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.bootComp) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.Mem.bootComp.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Mem.bootComp,
      ZiskFv.AirsClean.Mem.bootCircuit, MemBusChannel, SeamContChannel,
      Channel.toRaw, RawChannel.mk.injEq]
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

/-! ## Full-ensemble op-bus counterpart classification -/

/-- Clean balance replacement shape for the full ensemble: an active Main
    operation-bus interaction has a same-message counterpart whose
    multiplicity is neither another pull nor zero. -/
theorem exists_matching_nonzero_nonpull_of_active_main_op_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith OpBusChannel.toRaw)
    (opBus_balanced_of_witness witness h_balanced)
    mainInteraction h_mem h_active

/-- A constrained unified Main table can only contribute operation-bus
    interactions with multiplicity `-1` (active row) or `0` (inactive row). -/
theorem main_table_opBus_mult_neg_one_or_zero_of_constraints
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_constraints : table.Constraints)
    (h_main :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) :
    ∀ {interaction : Interaction FGL},
      interaction ∈ table.interactionsWith OpBusChannel.toRaw →
      interaction.mult = -1 ∨ interaction.mult = 0 := by
  intro interaction h_interaction
  refine ((Table.forall_interactionsWith_iff table OpBusChannel.toRaw
    (fun interaction => interaction.mult = -1 ∨ interaction.mult = 0)).mpr ?_)
    interaction h_interaction
  intro row h_row abstractInteraction h_abs h_channel
  have h_abs_with :
      abstractInteraction ∈ table.component.operations.interactionsWith
        OpBusChannel.toRaw := by
    simp [Operations.interactionsWith, h_abs, h_channel]
  have h_main_interactions :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw)] := by
    simpa [h_main] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  have h_abs_eq :
      abstractInteraction =
        ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw) := by
    simpa [h_main_interactions] using h_abs_with
  subst abstractInteraction
  have h_bool :=
    ZiskFv.AirsClean.Main.is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints
      length program (table.environment row)
      (by simpa [h_main] using h_constraints row h_row)
  let x := (table.environment row)
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
      length program).rowInputVar.core.is_external_op
  have h_mul_raw : x * (1 + -1 * x) = 0 := by
    simpa [Expression.eval, x] using h_bool
  have h_mul : x * (1 - x) = 0 := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h_mul_raw
  rcases mul_eq_zero.mp h_mul with h_zero | h_one_sub
  · right
    change Expression.eval (table.environment row)
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar.core.is_external_op) = 0
    simp [Expression.eval, x, h_zero]
  · left
    have h_one : x = 1 := (sub_eq_zero.mp h_one_sub).symm
    change Expression.eval (table.environment row)
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar.core.is_external_op) = -1
    simp [Expression.eval, x, h_one]

/-- Classify the balanced same-message operation-bus counterpart in the full
    ensemble after excluding verifier and components that expose no op-bus
    interactions.

The unified Main case is intentionally left explicit. Excluding it requires
    the row-local Main multiplicity lemma in a cheap full-ensemble form; this
    theorem avoids hiding that remaining proof obligation. -/
theorem exists_matching_op_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith OpBusChannel.toRaw
            ∧ (table.component = arithMulProviderComponent
              ∨ table.component = shiftStaticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.Binary.staticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.BinaryAdd.component
              ∨ table.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_op_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_component_mem :
      table.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_boot | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith OpBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_opBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact memAlignReadByte_table_interactionsWith_opBus_nil h_marb
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact memAlignByte_table_interactionsWith_opBus_nil h_mab
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact memAlign_table_interactionsWith_opBus_nil h_memAlign
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact bootComp_table_interactionsWith_opBus_nil h_boot
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact mem_table_interactionsWith_opBus_nil h_mem
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact arithDiv_table_interactionsWith_opBus_nil h_arithDiv
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inl h_arithMul⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inl h_binExt)⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inl h_binary))⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inl h_binaryAdd)))⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inr h_main)))⟩

/-- Classify the balanced same-message operation-bus counterpart as a
    provider table in the full ensemble. The unified Main self-provider case
    is ruled out from `witness.Constraints`, using the row-local
    `is_external_op` boolean assertion from the unified Main component. -/
theorem exists_matching_provider_op_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith OpBusChannel.toRaw
            ∧ (table.component = arithMulProviderComponent
              ∨ table.component = shiftStaticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.Binary.staticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.BinaryAdd.component) := by
  obtain ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, h_component⟩ :=
    exists_matching_op_component_of_active_main_interaction
      witness h_balanced h_mem h_active
  rcases h_component with h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inl h_arithMul⟩
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inl h_binExt)⟩
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inr (Or.inl h_binary))⟩
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inr (Or.inr h_binaryAdd))⟩
  · have h_mult := main_table_opBus_mult_neg_one_or_zero_of_constraints
      (h_constraints table h_table) h_main h_mem_table
    rcases h_mult with h_neg | h_zero
    · exact False.elim (h_nonpull h_neg)
    · exact False.elim (h_nonzero h_zero)

/-! ## Full-ensemble memory-bus counterpart classification -/

/-- Clean balance replacement shape for full-ensemble memory interactions:
    an active Main memory-bus interaction has a same-message counterpart
    whose multiplicity is neither another pull nor zero. -/
theorem exists_matching_nonzero_nonpull_of_active_main_mem_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith MemBusChannel.toRaw)
    (memBus_balanced_of_witness witness h_balanced)
    mainInteraction h_mem h_active

/-- Classify the balanced same-message memory-bus counterpart in the full
    ensemble after excluding verifier and components that expose no
    memory-bus interactions.

The unified Main case is intentionally explicit, matching the Mem-family
    bridge: excluding it requires selector legality beyond the current
    Main row soundness, and keeping it visible avoids laundering that missing
    proof into a provider theorem. -/
theorem exists_matching_mem_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith MemBusChannel.toRaw
            ∧ (table.component = ZiskFv.AirsClean.MemAlignReadByte.component
              ∨ table.component = ZiskFv.AirsClean.MemAlignByte.component
              ∨ table.component = ZiskFv.AirsClean.MemAlign.component
              ∨ table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
              ∨ table.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_mem_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_component_mem :
      table.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_boot | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith MemBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_memBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inl h_marb⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inl h_mab)⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inl h_memAlign))⟩
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact bootComp_table_interactionsWith_memBus_nil h_boot
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inl h_mem)))⟩
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact arithDiv_table_interactionsWith_memBus_nil h_arithDiv
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact arithMul_table_interactionsWith_memBus_nil h_arithMul
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact staticBinaryExtension_table_interactionsWith_memBus_nil h_binExt
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact staticBinary_table_interactionsWith_memBus_nil h_binary
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact binaryAdd_table_interactionsWith_memBus_nil h_binaryAdd
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inr h_main)))⟩

/-! ## Row extraction from full-ensemble channel interactions -/

/-- If a table's operation-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_opBus_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- If a table's memory-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_memBus_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- If a table's memory-bus abstract interactions are exactly two entries,
    any concrete table-level interaction on that channel is one of those two
    entries evaluated at some row. -/
theorem exists_memBus_row_eval_of_pair_interactionsWith
    {table : Table FGL} {left right : AbstractInteraction FGL}
    (h_pair :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [left, right])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    (∃ row ∈ table.table,
      interaction = left.eval (table.environment row))
    ∨ (∃ row ∈ table.table,
      interaction = right.eval (table.environment row)) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_pair] at h_mem
  obtain ⟨row, h_row, h_eval⟩ := h_mem
  rcases h_eval with h_left | h_right
  · exact Or.inl ⟨row, h_row, h_left⟩
  · exact Or.inr ⟨row, h_row, h_right⟩

/-- Row extraction for the unified Main operation-bus interaction in the full
    ensemble. The extracted row is a `MainRowWithRom`; its `.core` is the same
    row that emits Main's memory-bus interactions. -/
theorem exists_main_op_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  · exact h_mem

/-- The concrete unified Main operation-bus interaction for any row of the
    selected Main table is a member of that table's op-bus interactions. -/
theorem main_op_row_eval_mem_interactionsWith
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {row : Array FGL}
    (h_row : row ∈ table.table) :
    ((OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core)).toRaw).eval
      (table.environment row) ∈ table.interactionsWith OpBusChannel.toRaw := by
  have h_singleton :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton]
  exact ⟨row, h_row, rfl⟩

/-- Row extraction for the unified Main memory-bus interactions in the full
    ensemble. Main exposes three memory interactions (`a`, `b`, and
    `c/store`), so the result keeps that side disjunction explicit. -/
theorem exists_main_mem_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg))
            (ZiskFv.AirsClean.Main.aMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg))
            (ZiskFv.AirsClean.Main.bMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg))
            (ZiskFv.AirsClean.Main.cMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row) := by
  have h_interactions :=
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_memBus
      length program
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_component, h_interactions] at h_mem
  rcases h_mem with ⟨row, h_row, h_eq | h_eq | h_eq⟩
  · exact ⟨row, h_row, Or.inl h_eq⟩
  · exact ⟨row, h_row, Or.inr (Or.inl h_eq)⟩
  · exact ⟨row, h_row, Or.inr (Or.inr h_eq)⟩

/-- Row extraction for a BinaryAdd operation-bus provider interaction in the
    full ensemble. -/
theorem exists_binaryAdd_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a lookup-aware Binary operation-bus provider
    interaction in the full ensemble. -/
theorem exists_staticBinary_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.Binary.opBusMessageExpr
            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Binary.staticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a lookup-aware BinaryExtension operation-bus provider
    interaction in the full ensemble. -/
theorem exists_staticBinaryExtension_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component :
      table.component = shiftStaticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            shiftStaticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for an ArithMul operation-bus provider interaction in the
    full ensemble. -/
theorem exists_arithMul_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = arithMulProviderComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
            arithMulProviderComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.ArithMul.componentWithArithTable_interactionsWith_opBus
  · exact h_mem

/-- Project the lookup-aware ArithMul provider branch's generic component
    `Spec` to the concrete `FullSpec`. -/
theorem arithMul_fullSpec_of_component_spec
    {table : Table FGL} {row : Array FGL}
    (h_component : table.component = arithMulProviderComponent)
    (h_spec : table.component.Spec (table.environment row)) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (arithMulProviderComponent.rowInput
        (table.environment row)) := by
  rw [h_component] at h_spec
  simpa [arithMulProviderComponent,
    ZiskFv.AirsClean.ArithMul.componentWithArithTable_spec] using h_spec

/-- A lookup-aware ArithMul provider branch can only match Main rows whose
    operation-bus opcode lies in the Arith ROM opcode range. -/
theorem arithMul_primary_provider_match_main_op_val_ge_176
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec row)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage row) 1)) :
    176 <= (m.op r_main).val := by
  have h_provider_ge :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.op_val_ge_176 row h_full.2
  have h_op_match : m.op r_main = row.flags.op := by
    simpa [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.ArithMul.primaryOpBusMessage] using h_match.2.1
  simpa [h_op_match] using h_provider_ge

/-- Full-ensemble version of
    `arithMul_primary_provider_match_main_op_val_ge_176`, projecting the
    generic component `Spec` to ArithMul `FullSpec` first. -/
theorem arithMul_provider_branch_main_op_val_ge_176
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1)) :
    176 <= (m.op r_main).val := by
  have h_full := arithMul_fullSpec_of_component_spec h_component h_providerSpec
  let env := providerTable.environment providerRow
  let row := eval env arithMulProviderComponent.rowInputVar
  have h_row_eq : row = arithMulProviderComponent.rowInput env := by
    dsimp [row]
    simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
      (eval_varFromOffset_valueFromOffset arithMulProviderComponent.Input 0 env)
  have h_full_row :
      ZiskFv.AirsClean.ArithMul.FullSpec row := by
    simpa [h_row_eq] using h_full
  have h_provider_ge :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.op_val_ge_176
      row h_full_row.2
  have h_op_match : m.op r_main = row.flags.op := by
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr_toEntry_op] at h_op
    simpa [row, env, ZiskFv.Airs.OperationBus.opBus_row_Main] using h_op
  simpa [h_op_match] using h_provider_ge

/-- The lookup-aware ArithMul branch cannot be the provider for a Main XOR
    operation.  This is the first Binary-family branch exclusion used by the
    P4 provider-match discharge. -/
theorem arithMul_provider_branch_ne_xor
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_XOR] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main XOR operation. -/
theorem staticBinaryExtension_provider_branch_ne_xor
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_bitwise_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.2.2 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_XOR])

/-- The BinaryAdd provider branch cannot be the provider for a Main XOR
    operation. -/
theorem binaryAdd_provider_branch_ne_xor
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rw [h_main_op] at h_provider_op
  norm_num [ZiskFv.Trusted.OP_XOR] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main logical
    Binary operation (`AND`, `OR`, or `XOR`). -/
theorem arithMul_provider_branch_ne_staticBinaryLogic
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_and | h_or | h_xor
  · rw [h_and] at h_ge
    norm_num [ZiskFv.Trusted.OP_AND] at h_ge
  · rw [h_or] at h_ge
    norm_num [ZiskFv.Trusted.OP_OR] at h_ge
  · rw [h_xor] at h_ge
    norm_num [ZiskFv.Trusted.OP_XOR] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main logical Binary operation (`AND`, `OR`, or `XOR`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryLogic
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_bitwise_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  rcases h_main_op with h_and | h_or | h_xor
  · exact h_ne.1 (by
      rw [← h_provider_op, h_and]
      norm_num [ZiskFv.Trusted.OP_AND])
  · exact h_ne.2.1 (by
      rw [← h_provider_op, h_or]
      norm_num [ZiskFv.Trusted.OP_OR])
  · exact h_ne.2.2 (by
      rw [← h_provider_op, h_xor]
      norm_num [ZiskFv.Trusted.OP_XOR])

/-- The BinaryAdd provider branch cannot be the provider for a Main logical
    Binary operation (`AND`, `OR`, or `XOR`). -/
theorem binaryAdd_provider_branch_ne_staticBinaryLogic
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_and | h_or | h_xor
  · rw [h_and] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_AND] at h_provider_op
  · rw [h_or] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_OR] at h_provider_op
  · rw [h_xor] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_XOR] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    comparison operation (`LT` or `LTU`). -/
theorem arithMul_provider_branch_ne_staticBinaryCompare
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_lt | h_ltu
  · rw [h_lt] at h_ge
    norm_num [ZiskFv.Trusted.OP_LT] at h_ge
  · rw [h_ltu] at h_ge
    norm_num [ZiskFv.Trusted.OP_LTU] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary comparison operation (`LT` or `LTU`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryCompare
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_compare_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  rcases h_main_op with h_lt | h_ltu
  · exact h_ne.2 (by
      rw [← h_provider_op, h_lt]
      norm_num [ZiskFv.Trusted.OP_LT])
  · exact h_ne.1 (by
      rw [← h_provider_op, h_ltu]
      norm_num [ZiskFv.Trusted.OP_LTU])

/-- The BinaryAdd provider branch cannot be the provider for a Main Binary
    comparison operation (`LT` or `LTU`). -/
theorem binaryAdd_provider_branch_ne_staticBinaryCompare
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_lt | h_ltu
  · rw [h_lt] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_LT] at h_provider_op
  · rw [h_ltu] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_LTU] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    `SUB` operation. -/
theorem arithMul_provider_branch_ne_staticBinarySub
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_SUB] at h_ge

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    `ADD` operation. -/
theorem arithMul_provider_branch_ne_staticBinaryAdd
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_ADD) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_ADD] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary `SUB` operation. -/
theorem staticBinaryExtension_provider_branch_ne_staticBinarySub
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_add_sub_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.2 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_SUB])

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary `ADD` operation. -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryAdd
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_ADD) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_add_sub_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.1 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_ADD])

/-- The BinaryAdd provider branch cannot be the provider for a Main Binary
    `SUB` operation. -/
theorem binaryAdd_provider_branch_ne_staticBinarySub
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rw [h_main_op] at h_provider_op
  norm_num [ZiskFv.Trusted.OP_SUB] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main W-mode
    Binary ADD/SUB operation (`ADDW` or `SUBW`). -/
theorem arithMul_provider_branch_ne_staticBinaryW
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_addw | h_subw
  · rw [h_addw] at h_ge
    norm_num [ZiskFv.Trusted.OP_ADD_W] at h_ge
  · rw [h_subw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SUB_W] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main W-mode Binary ADD/SUB operation (`ADDW` or `SUBW`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryW
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_W_add_sub_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  rcases h_main_op with h_addw | h_subw
  · exact h_ne.1 (by
      rw [← h_provider_op, h_addw]
      norm_num [ZiskFv.Trusted.OP_ADD_W])
  · exact h_ne.2 (by
      rw [← h_provider_op, h_subw]
      norm_num [ZiskFv.Trusted.OP_SUB_W])

/-- The BinaryAdd provider branch cannot be the provider for a Main W-mode
    Binary ADD/SUB operation (`ADDW` or `SUBW`). -/
theorem binaryAdd_provider_branch_ne_staticBinaryW
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_addw | h_subw
  · rw [h_addw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_ADD_W] at h_provider_op
  · rw [h_subw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SUB_W] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main
    BinaryExtension shift operation. -/
theorem arithMul_provider_branch_ne_staticBinaryExtensionShift
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_sll | h_srl | h_sra | h_sllw | h_srlw | h_sraw
  · rw [h_sll] at h_ge
    norm_num [ZiskFv.Trusted.OP_SLL] at h_ge
  · rw [h_srl] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRL] at h_ge
  · rw [h_sra] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRA] at h_ge
  · rw [h_sllw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SLL_W] at h_ge
  · rw [h_srlw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRL_W] at h_ge
  · rw [h_sraw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRA_W] at h_ge

/-- A lookup-aware static Binary provider branch cannot be the provider for a
    Main BinaryExtension shift operation. -/
theorem staticBinary_provider_branch_ne_staticBinaryExtensionShift
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Binary.opBusMessageExpr
              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    False := by
  let env := providerTable.environment providerRow
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput env
  have h_componentSpec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_componentSpec
  have h_provider_op :
      m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := by
    have h_op := h_match.2.1
    simpa [env, row, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_op
  have h_contra
      (op_val : ℕ)
      (h_shift :
        op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W)
      (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL)) :
      False :=
    ZiskFv.AirsClean.Binary.static_table_op_val_ne_binaryExtension_shift_of_emit
      row h_componentSpec.1 h_componentSpec.2 op_val h_shift h_emit
  rcases h_main_op with h_sll | h_srl | h_sra | h_sllw | h_srlw | h_sraw
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL
      (Or.inl rfl)
      (by
        rw [← h_provider_op, h_sll]
        norm_num [ZiskFv.Trusted.OP_SLL,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL
      (Or.inr (Or.inl rfl))
      (by
        rw [← h_provider_op, h_srl]
        norm_num [ZiskFv.Trusted.OP_SRL,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA
      (Or.inr (Or.inr (Or.inl rfl)))
      (by
        rw [← h_provider_op, h_sra]
        norm_num [ZiskFv.Trusted.OP_SRA,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (by
        rw [← h_provider_op, h_sllw]
        norm_num [ZiskFv.Trusted.OP_SLL_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (by
        rw [← h_provider_op, h_srlw]
        norm_num [ZiskFv.Trusted.OP_SRL_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (by
        rw [← h_provider_op, h_sraw]
        norm_num [ZiskFv.Trusted.OP_SRA_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W])

/-- The BinaryAdd provider branch cannot be the provider for a Main
    BinaryExtension shift operation. -/
theorem binaryAdd_provider_branch_ne_staticBinaryExtensionShift
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_sll | h_srl | h_sra | h_sllw | h_srlw | h_sraw
  · rw [h_sll] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SLL] at h_provider_op
  · rw [h_srl] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRL] at h_provider_op
  · rw [h_sra] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRA] at h_provider_op
  · rw [h_sllw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SLL_W] at h_provider_op
  · rw [h_srlw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRL_W] at h_provider_op
  · rw [h_sraw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRA_W] at h_provider_op

/-! ## Full-ensemble operation-bus row bridges -/

/-- Spec-carrying full-ensemble operation-bus projection: an active
    unified-Main operation-bus interaction has a balanced same-message
    provider counterpart, and the Binary-family provider branches are
    resolved to concrete table rows carrying `witness.Spec`.
    The ArithMul provider branch is also resolved to a concrete row. -/
theorem exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧ mainInteraction =
          ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw).eval
            (mainTable.environment mainRow)
        ∧ ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = arithMulProviderComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                            arithMulProviderComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        shiftStaticLookupComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                            shiftStaticLookupComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Binary.staticLookupComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.Binary.opBusMessageExpr
                            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))) := by
  have h_main_witness :
      mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_op_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_provider_op_component_of_active_main_interaction
      witness h_constraints h_balanced h_main_witness h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_arithMul_row_eval_of_interaction_mem
        h_arithMul h_providerInteraction
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_arithMul, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinaryExtension_row_eval_of_interaction_mem
        h_binExt h_providerInteraction
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binExt, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinary_row_eval_of_interaction_mem
        h_binary h_providerInteraction
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binary, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binaryAdd_row_eval_of_interaction_mem
        h_binaryAdd h_providerInteraction
    right
    right
    right
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binaryAdd, h_providerEval⟩

/-- Legacy-entry view of the full-ensemble operation-bus bridge.

    Clean balance proves equality of raw operation-bus message arrays.  This
    adapter keeps the full-ensemble provider row/spec information while
    translating each provider branch into the `OperationBus.matches_entry`
    shape consumed by the existing opcode proofs. -/
theorem exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧ mainInteraction =
          ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw).eval
            (mainTable.environment mainRow)
        ∧ ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = arithMulProviderComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                              arithMulProviderComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        shiftStaticLookupComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                              shiftStaticLookupComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Binary.staticLookupComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Binary.opBusMessageExpr
                              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))) := by
  obtain ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
      h_providerTable, h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_arithMul
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binExt
    right
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binary
    right
    right
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binaryAdd
    right
    right
    right
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg

/-- Legacy-Main view of the full-ensemble operation-bus bridge.

    This specializes the selected unified Clean Main row back to the existing
    `Valid_Main` row used by opcode proofs.  It deliberately preserves all
    full-ensemble provider alternatives: later opcode-specific adapters may
    rule out branches only from provider-local facts, not by caller promise. -/
theorem exists_op_provider_row_matches_legacy_main_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_main_row :
      ∀ mainRow ∈ mainTable.table,
        eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.core =
          ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ providerTable ∈ witness.allTables,
          providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
            ∧
            ((∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component = arithMulProviderComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                          arithMulProviderComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component =
                    shiftStaticLookupComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                          shiftStaticLookupComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component =
                    ZiskFv.AirsClean.Binary.staticLookupComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Binary.opBusMessageExpr
                          ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                          ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))) := by
  obtain ⟨mainRow, h_mainRow, _h_mainSpec, _h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
      h_providerTable, h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row mainRow h_mainRow]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  refine ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
    h_nonzero, providerTable, h_providerTable, h_providerInteraction, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_arithMul
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binExt
    right
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binary
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binaryAdd
    right
    right
    right
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩

/-- XOR specialization of the full-ensemble operation-bus provider bridge.

    For an active legacy Main row whose opcode is `OP_XOR`, balanced operation-bus
    coverage cannot use ArithMul, BinaryExtension, or BinaryAdd.  The remaining
    branch is the lookup-aware Binary provider row, with the provider table's
    full `Spec` retained for wrapper construction. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_main_row :
      ∀ mainRow ∈ mainTable.table,
        eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.core =
          ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  obtain ⟨providerInteraction, _h_provider_witness, _h_msg, _h_nonpull,
      _h_nonzero, providerTable, h_providerTable, _h_providerInteraction,
      h_providerBranches⟩ :=
    exists_op_provider_row_matches_legacy_main_spec_of_active_main_table_interaction
      m r_main witness h_constraints h_balanced h_specs h_mainTable
      h_mainComponent h_main_row h_main_active h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component, h_match⟩ :=
      h_arithMul
    exact False.elim
      (arithMul_provider_branch_ne_xor h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component, h_match⟩ :=
      h_binExt
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_xor h_component h_providerSpec
        h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component, h_match⟩ :=
      h_binary
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component, h_match⟩ :=
      h_binaryAdd
    exact False.elim (binaryAdd_provider_branch_ne_xor h_match h_main_op)

/-- Row-indexed XOR specialization of the full-ensemble operation-bus provider
    bridge.

Unlike `exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_table_interaction`,
this adapter rewrites only the concrete Main table row that emitted the selected
interaction.  It is the construction-facing form: callers identify row `i` in
the selected Main table, and balance supplies the Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_xor h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_xor h_component h_providerSpec
        h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_xor h_match h_main_op)

/-- Row-indexed logical-Binary specialization of the full-ensemble operation-bus
    provider bridge.

For a concrete active Main row whose opcode is `AND`, `OR`, or `XOR`, balance
cannot use ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryLogic
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryLogic
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryLogic h_match h_main_op)

/-- Row-indexed comparison-Binary specialization of the full-ensemble
    operation-bus provider bridge.

For a concrete active Main row whose opcode is `LT` or `LTU`, balance cannot
use ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_compare_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryCompare
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryCompare
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryCompare h_match h_main_op)

/-- Row-indexed `SUB` Binary specialization of the full-ensemble operation-bus
    provider bridge.

For a concrete active Main row whose opcode is `SUB`, balance cannot use
ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_sub_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinarySub
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinarySub
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinarySub h_match h_main_op)

/-- Row-indexed ADD provider specialization of the full-ensemble operation-bus
    provider bridge.

For a concrete active Main row whose opcode is `ADD`, balance cannot use
ArithMul or BinaryExtension. The remaining honest providers are lookup-aware
Binary and BinaryAdd, so the result preserves that disjunction for callers. -/
theorem exists_add_provider_row_matches_legacy_main_of_add_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_ADD) :
    (∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1))
    ∨
    (∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryAdd.opBusMessage
                (ZiskFv.AirsClean.BinaryAdd.component.rowInput
                  (providerTable.environment providerRow))) 1)) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryAdd
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryAdd
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact Or.inl ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.BinaryAdd.opBusMessage
              (ZiskFv.AirsClean.BinaryAdd.component.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.BinaryAdd.component_eval_opBusMessageExpr]
        using h_match
    exact Or.inr ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩

/-- Row-indexed W-mode ADD/SUB Binary specialization of the full-ensemble
    operation-bus provider bridge.

For a concrete active Main row whose opcode is `ADDW` or `SUBW`, balance cannot
use ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_w_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryW
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryW
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryW h_match h_main_op)

/-- Row-indexed BinaryExtension shift specialization of the full-ensemble
    operation-bus provider bridge.

For a concrete active Main row whose opcode is one of the BinaryExtension shift
opcodes, balance cannot use ArithMul, static Binary, or BinaryAdd.  The
remaining branch is the lookup-aware BinaryExtension provider row. -/
theorem exists_binaryExtension_provider_row_matches_legacy_main_of_shift_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = shiftStaticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryExtension.opBusMessage
                (shiftStaticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryExtensionShift
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.BinaryExtension.opBusMessage
              (shiftStaticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinary_provider_branch_ne_staticBinaryExtensionShift
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (binaryAdd_provider_branch_ne_staticBinaryExtensionShift h_match h_main_op)

/-- Row extraction for a Mem memory-bus provider interaction in the full
    ensemble. -/
theorem exists_mem_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithMemBus_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a dual-aware Mem memory-bus provider interaction in
    the full ensemble. The selected interaction is either the primary Mem
    provider emission or the pinned `dual_mem = 1` read emission. -/
theorem exists_mem_dual_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    (∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (table.environment row))
    ∨ (∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (table.environment row)) := by
  apply exists_memBus_row_eval_of_pair_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlign memory-bus interaction in the full ensemble. -/
theorem exists_memAlign_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
            - ZiskFv.AirsClean.MemAlign.selAssumeExpr
              ZiskFv.AirsClean.MemAlign.component.rowInputVar)
          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlignByte memory-bus provider interaction in the
    full ensemble. -/
theorem exists_memAlignByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlignReadByte memory-bus provider interaction in
    the full ensemble. -/
theorem exists_memAlignReadByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus
  · exact h_mem

/-! ## Full-ensemble Mem read-replay row projections -/

/-- Public replay-row view of a primary Mem provider row when it is selected
    as a read. The Clean provider interaction carries selector multiplicity,
    but chronological memory replay uses legacy read multiplicity `-1`. -/
@[reducible]
def memPrimaryReadReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusMessage row) (-1) 2

/-- Public replay-row view of a dual Mem provider row. Dual Mem emissions are
    pinned reads, so the replay multiplicity is the legacy read `-1`. -/
@[reducible]
def memDualReadReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusDualMessage row) (-1) 2

/-- Public replay-row view of a primary Mem provider row, preserving the
    read/write polarity carried by `wr`. For boolean `wr`, this maps
    `wr = 0` to legacy read multiplicity `-1` and `wr = 1` to write
    multiplicity `1`. -/
@[reducible]
def memPrimaryReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusMessage row) (2 * row.wr - 1) 2

/-- Replay seed entry carrying the previous segment's final memory state into a
    continuation Mem segment. -/
@[reducible]
def memPreviousSegmentReplayEntry
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) :
    Interaction.MemoryBusEntry FGL :=
  { multiplicity := 1
    as := 2
    ptr := segment.previous_segment_addr * 8
    value_0 := segment.previous_segment_value_0
    value_1 := segment.previous_segment_value_1
    timestamp := segment.previous_segment_step }

/-- Read-replay events contributed by one dual-aware Mem provider row, in
    provider emission order. -/
@[reducible]
def memReadReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row]

/-- Read/write replay events contributed by one dual-aware Mem provider row,
    in provider emission order. The primary event preserves `wr`, while the
    dual event is a pinned read. -/
@[reducible]
def memReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row]

/-- Active read-replay events contributed by one dual-aware Mem provider row.
    Inactive primary/dual emissions do not contribute chronological memory
    replay events. -/
@[reducible]
def activeMemReadReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  (if row.sel = 1 then [memPrimaryReadReplayEntryOfRow row] else [])
    ++
  (if row.sel_dual = 1 then [memDualReadReplayEntryOfRow row] else [])

/-- Active read/write replay events contributed by one dual-aware Mem
    provider row. The primary event preserves `wr`, while the dual event is a
    pinned read. -/
@[reducible]
def activeMemReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  (if row.sel = 1 then [memPrimaryReplayEntryOfRow row] else [])
    ++
  (if row.sel_dual = 1 then [memDualReadReplayEntryOfRow row] else [])

/-- If neither selector is active, a Mem row contributes no active read-replay
    entries. -/
theorem activeMemReadReplayEntriesOfRow_eq_nil_of_inactive
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReadReplayEntriesOfRow row = [] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- If neither selector is active, a Mem row contributes no active
    read/write replay entries. -/
theorem activeMemReplayEntriesOfRow_eq_nil_of_inactive
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReplayEntriesOfRow row = [] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A primary-only selected row contributes exactly its primary read entry to
    the active read-replay surface. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A primary-only selected row contributes exactly its primary
    polarity-preserving entry to the active read/write replay surface. -/
theorem activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A dual-only selected row contributes exactly its dual read entry to the
    active read-replay surface. -/
theorem activeMemReadReplayEntriesOfRow_eq_dual_of_not_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memDualReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A dual-only selected row contributes exactly its dual read entry to the
    active read/write replay surface. -/
theorem activeMemReplayEntriesOfRow_eq_dual_of_not_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memDualReadReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- When both selectors are active, active read-replay emission is primary
    first and then dual. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- When both selectors are active, active read/write replay emission is
    primary first and then dual. -/
theorem activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- Under the generated per-row Mem spec, selecting the dual read emission
    forces the primary selector too, so active read-replay emission is
    primary first and then the pinned dual read. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_dual_of_spec_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  exact activeMemReadReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual

/-- Under the generated per-row Mem spec, selecting the dual read emission
    forces the primary selector too, so active read/write replay emission is
    primary first and then the pinned dual read. -/
theorem activeMemReplayEntriesOfRow_eq_primary_dual_of_spec_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  exact activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual

/-- Any active read/write replay entry from a Mem row is either that row's
    primary polarity-preserving entry or its pinned dual-read entry. -/
theorem activeMemReplayEntriesOfRow_mem_eq_primary_or_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_entry : entry ∈ activeMemReplayEntriesOfRow row) :
    entry = memPrimaryReplayEntryOfRow row
      ∨ entry = memDualReadReplayEntryOfRow row := by
  unfold activeMemReplayEntriesOfRow at h_entry
  by_cases h_sel : row.sel = 1
  · by_cases h_sel_dual : row.sel_dual = 1
    · simp [h_sel, h_sel_dual] at h_entry
      exact h_entry
    · simp [h_sel, h_sel_dual] at h_entry
      exact Or.inl h_entry
  · by_cases h_sel_dual : row.sel_dual = 1
    · simp [h_sel, h_sel_dual] at h_entry
      exact Or.inr h_entry
    · simp [h_sel, h_sel_dual] at h_entry

/-- A selected primary+dual row is chronologically ordered when the primary
    timestamp is no later than the pinned dual-read timestamp. -/
theorem activeMemReplayEntriesOfRow_chronological_of_sel_of_sel_dual_of_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_le : row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    h_sel h_sel_dual]
  simpa [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological,
    memPrimaryReplayEntryOfRow, memDualReadReplayEntryOfRow,
    ZiskFv.AirsClean.Mem.memBusMessage,
    ZiskFv.AirsClean.Mem.memBusDualMessage] using h_step_le

/-- Under the generated per-row Mem spec, a selected dual row is locally
    chronological when the generated dual-step range check supplies
    `step <= step_dual`. -/
theorem activeMemReplayEntriesOfRow_chronological_of_spec_of_sel_dual_of_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_le : row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  exact activeMemReplayEntriesOfRow_chronological_of_sel_of_sel_dual_of_step_le
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual h_step_le

/-- Under the generated per-row Mem spec, local active replay emissions are
    chronological once any selected dual emission is known to have
    `step <= step_dual`. Rows with no selected dual emit zero or one active
    replay entry, so they are chronological without a timestamp comparison. -/
theorem activeMemReplayEntriesOfRow_chronological_of_spec_of_dual_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_step_le_of_dual :
      row.sel_dual = 1 → row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec row h_spec with
    h_sel_dual_zero | h_sel_dual_one
  · rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec row h_spec with
      h_sel_zero | h_sel_one
    · have h_sel_ne : row.sel ≠ 1 := by
        simp [h_sel_zero]
      have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
        h_sel_ne h_sel_dual_ne]
      simp [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological]
    · have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
        h_sel_one h_sel_dual_ne]
      simp [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological]
  · exact activeMemReplayEntriesOfRow_chronological_of_spec_of_sel_dual_of_step_le
      h_spec h_sel_dual_one (h_step_le_of_dual h_sel_dual_one)

/-- A selected primary+dual row has no duplicate replay entries when its
    primary and dual timestamps are distinct. PIL allows equality for
    read-read dual rows, so this lemma intentionally records the extra
    condition rather than hiding it. -/
theorem activeMemReplayEntriesOfRow_nodup_of_sel_of_sel_dual_of_step_ne
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_ne : row.step ≠ row.step_dual) :
    (activeMemReplayEntriesOfRow row).Nodup := by
  rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    h_sel h_sel_dual]
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false,
    not_false_eq_true]
  constructor
  · intro h_eq
    have h_ts :
        (memPrimaryReplayEntryOfRow row).timestamp =
          (memDualReadReplayEntryOfRow row).timestamp := by
      rw [h_eq]
    simp at h_ts
    exact h_step_ne h_ts
  · simp

/-- Primary replay entries from different 29-bit internal Mem addresses have
    disjoint eight-byte byte-address ranges after the provider `addr * 8`
    pointer conversion. -/
theorem memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
    {left right : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_left_range : left.addr.val < 2 ^ 29)
    (h_right_range : right.addr.val < 2 ^ 29)
    (h_addr_ne : left.addr ≠ right.addr) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow left) (memPrimaryReplayEntryOfRow right) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
  intro i j hi hj h_eq
  have h_left_ptr :
      (memPrimaryReplayEntryOfRow left).ptr.toNat = left.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_left_range]
  have h_right_ptr :
      (memPrimaryReplayEntryOfRow right).ptr.toNat = right.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_right_range]
  rw [h_left_ptr, h_right_ptr] at h_eq
  have h_addr_val_ne : left.addr.val ≠ right.addr.val := by
    intro h_val
    exact h_addr_ne (Fin.ext h_val)
  rcases lt_trichotomy left.addr.val right.addr.val with h_lt | h_eq_addr | h_gt
  · have h_le : left.addr.val + 1 ≤ right.addr.val := Nat.succ_le_of_lt h_lt
    have h_bound_left : left.addr.val * 8 + i < right.addr.val * 8 := by
      have hi_le : i ≤ 7 := by omega
      nlinarith
    have h_bound_right : right.addr.val * 8 ≤ right.addr.val * 8 + j := by
      omega
    omega
  · exact h_addr_val_ne h_eq_addr
  · have h_le : right.addr.val + 1 ≤ left.addr.val := Nat.succ_le_of_lt h_gt
    have h_bound_right : right.addr.val * 8 + j < left.addr.val * 8 := by
      have hj_le : j ≤ 7 := by omega
      nlinarith
    have h_bound_left : left.addr.val * 8 ≤ left.addr.val * 8 + i := by
      omega
    omega

/-- A selected primary entry is byte-disjoint from another row's dual read
    entry when their internal Mem addresses differ. -/
theorem memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
    {left right : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_left_range : left.addr.val < 2 ^ 29)
    (h_right_range : right.addr.val < 2 ^ 29)
    (h_addr_ne : left.addr ≠ right.addr) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow left) (memDualReadReplayEntryOfRow right) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
  intro i j hi hj h_eq
  have h_left_ptr :
      (memPrimaryReplayEntryOfRow left).ptr.toNat = left.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_left_range]
  have h_right_ptr :
      (memDualReadReplayEntryOfRow right).ptr.toNat = right.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_right_range]
  rw [h_left_ptr, h_right_ptr] at h_eq
  have h_addr_val_ne : left.addr.val ≠ right.addr.val := by
    intro h_val
    exact h_addr_ne (Fin.ext h_val)
  rcases lt_trichotomy left.addr.val right.addr.val with h_lt | h_eq_addr | h_gt
  · have h_le : left.addr.val + 1 ≤ right.addr.val := Nat.succ_le_of_lt h_lt
    have h_bound_left : left.addr.val * 8 + i < right.addr.val * 8 := by
      have hi_le : i ≤ 7 := by omega
      nlinarith
    have h_bound_right : right.addr.val * 8 ≤ right.addr.val * 8 + j := by
      omega
    omega
  · exact h_addr_val_ne h_eq_addr
  · have h_le : right.addr.val + 1 ≤ left.addr.val := Nat.succ_le_of_lt h_gt
    have h_bound_right : right.addr.val * 8 + j < left.addr.val * 8 := by
      have hj_le : j ≤ 7 := by omega
      nlinarith
    have h_bound_left : left.addr.val * 8 ≤ left.addr.val * 8 + i := by
      omega
    omega

/-- A selected primary entry is byte-disjoint from the previous-segment seed
    entry when their internal Mem addresses differ. -/
theorem memoryBusEntryByteDisjoint_primary_previousSegment_of_addr_ne
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    (h_row_range : row.addr.val < 2 ^ 29)
    (h_segment_range : segment.previous_segment_addr.val < 2 ^ 29)
    (h_addr_ne : row.addr ≠ segment.previous_segment_addr) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow row) (memPreviousSegmentReplayEntry segment) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
  intro i j hi hj h_eq
  have h_row_ptr :
      (memPrimaryReplayEntryOfRow row).ptr.toNat = row.addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_row_range]
  have h_segment_ptr :
      (memPreviousSegmentReplayEntry segment).ptr.toNat =
        segment.previous_segment_addr.val * 8 := by
    simp [ZiskFv.Airs.Mem.field_addr_times_eight_val_eq_of_lt h_segment_range]
  rw [h_row_ptr, h_segment_ptr] at h_eq
  have h_addr_val_ne : row.addr.val ≠ segment.previous_segment_addr.val := by
    intro h_val
    exact h_addr_ne (Fin.ext h_val)
  rcases lt_trichotomy row.addr.val segment.previous_segment_addr.val with
    h_lt | h_eq_addr | h_gt
  · have h_le : row.addr.val + 1 ≤ segment.previous_segment_addr.val :=
      Nat.succ_le_of_lt h_lt
    have h_bound_left : row.addr.val * 8 + i < segment.previous_segment_addr.val * 8 := by
      have hi_le : i ≤ 7 := by omega
      nlinarith
    have h_bound_right :
        segment.previous_segment_addr.val * 8 ≤
          segment.previous_segment_addr.val * 8 + j := by
      omega
    omega
  · exact h_addr_val_ne h_eq_addr
  · have h_le : segment.previous_segment_addr.val + 1 ≤ row.addr.val :=
      Nat.succ_le_of_lt h_gt
    have h_bound_right :
        segment.previous_segment_addr.val * 8 + j < row.addr.val * 8 := by
      have hj_le : j ≤ 7 := by omega
      nlinarith
    have h_bound_left : row.addr.val * 8 ≤ row.addr.val * 8 + i := by
      omega
    omega

/-- Primary-read replay rows projected from every row of a Mem table. -/
@[reducible]
def memPrimaryReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Dual-read replay rows projected from every row of a Mem table. -/
@[reducible]
def memDualReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Read-replay row surface exposed by a dual-aware Mem table.

    Unlike the legacy compatibility projections above, this list is shaped in
    provider emission order: for each concrete Mem table row, primary comes
    before dual. Chronological ordering and read/write soundness remain
    separate global trace obligations. -/
@[reducible]
def memReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    memReadReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Primary replay rows projected from every Mem table row, preserving
    read/write polarity. -/
@[reducible]
def memPrimaryReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Full replay-row surface exposed by a dual-aware Mem table.

    Events are projected in provider emission order: primary first, preserving
    read/write polarity, then the pinned dual read for the same provider row. -/
@[reducible]
def memReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    memReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Active read-replay rows projected from selected emissions of a Mem table.
    This is the replay surface accepted-trace extraction should use when
    proving chronological memory soundness from concrete Mem rows. -/
@[reducible]
def activeMemReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    activeMemReadReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Active read/write replay rows projected from selected emissions of a Mem
    table. Inactive rows are omitted instead of replayed as spurious memory
    events. -/
@[reducible]
def activeMemReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    activeMemReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- If the active replay projection is nonempty, then the underlying concrete
    Mem table is nonempty. -/
theorem table_nonempty_of_activeMemReplayRowsOfTable_nonempty
    {table : Table FGL}
    (h_rows : 0 < (activeMemReplayRowsOfTable table).length) :
    0 < table.table.length := by
  cases h_table : table.table with
  | nil =>
      simp [activeMemReplayRowsOfTable, h_table] at h_rows
  | cons _ _ =>
      simp

/-- The selected-entry split used by timeline evidence proves that the active
    replay projection is nonempty. -/
theorem activeMemReplayRowsOfTable_nonempty_of_split
    {table : Table FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_split :
      activeMemReplayRowsOfTable table = priorRows ++ entry :: laterRows) :
    0 < (activeMemReplayRowsOfTable table).length := by
  rw [h_split]
  simp

/-- Zero row for totalizing concrete Main table projections. -/
def zeroMainRowWithRom : ZiskFv.AirsClean.Main.MainRowWithRom FGL where
  core := {
    a_0 := 0
    a_1 := 0
    b_0 := 0
    b_1 := 0
    c_0 := 0
    c_1 := 0
    flag := 0
    pc := 0
    is_external_op := 0
    op := 0
    m32 := 0
    ind_width := 0
    set_pc := 0
    jmp_offset1 := 0
    jmp_offset2 := 0
    store_pc := 0
    im_high_degree_2 := 0
    segment_l1 := 0 }
  rom := {
    a_offset_imm0 := 0
    a_imm1 := 0
    b_offset_imm0 := 0
    b_imm1 := 0
    store_offset := 0
    a_src_imm := 0
    a_src_mem := 0
    is_precompiled := 0
    b_src_imm := 0
    b_src_mem := 0
    store_mem := 0
    store_ind := 0
    b_src_ind := 0
    a_src_reg := 0
    b_src_reg := 0
    store_reg := 0
    addr0 := 0
    addr1 := 0
    addr2 := 0
    main_step := 0 }

/-- Project row `row` of a concrete Clean Main table to its unified Main+ROM
    row input. Out-of-range rows use `zeroMainRowWithRom` only to keep the
    named-column view total. -/
@[reducible]
def mainTableRowAtOrZero
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar
  else
    zeroMainRowWithRom

/-- Named-column Main view obtained from the concrete Clean unified Main table. -/
@[reducible]
def mainOfTable
    {length : ℕ}
    (program : Program length)
    (table : Table FGL) :
    ZiskFv.Airs.Main.Valid_Main FGL FGL where
  a_0 := fun row => (mainTableRowAtOrZero program table row).core.a_0
  a_1 := fun row => (mainTableRowAtOrZero program table row).core.a_1
  b_0 := fun row => (mainTableRowAtOrZero program table row).core.b_0
  b_1 := fun row => (mainTableRowAtOrZero program table row).core.b_1
  c_0 := fun row => (mainTableRowAtOrZero program table row).core.c_0
  c_1 := fun row => (mainTableRowAtOrZero program table row).core.c_1
  flag := fun row => (mainTableRowAtOrZero program table row).core.flag
  pc := fun row => (mainTableRowAtOrZero program table row).core.pc
  is_external_op := fun row => (mainTableRowAtOrZero program table row).core.is_external_op
  op := fun row => (mainTableRowAtOrZero program table row).core.op
  b_src_imm := fun row => (mainTableRowAtOrZero program table row).rom.b_src_imm
  b_src_mem := fun row => (mainTableRowAtOrZero program table row).rom.b_src_mem
  b_src_ind := fun row => (mainTableRowAtOrZero program table row).rom.b_src_ind
  b_src_reg := fun row => (mainTableRowAtOrZero program table row).rom.b_src_reg
  m32 := fun row => (mainTableRowAtOrZero program table row).core.m32
  ind_width := fun row => (mainTableRowAtOrZero program table row).core.ind_width
  set_pc := fun row => (mainTableRowAtOrZero program table row).core.set_pc
  jmp_offset1 := fun row => (mainTableRowAtOrZero program table row).core.jmp_offset1
  jmp_offset2 := fun row => (mainTableRowAtOrZero program table row).core.jmp_offset2
  store_pc := fun row => (mainTableRowAtOrZero program table row).core.store_pc
  im_high_degree_2 := fun row => (mainTableRowAtOrZero program table row).core.im_high_degree_2
  segment_l1 := fun row => (mainTableRowAtOrZero program table row).core.segment_l1

/-- In-range concrete table projection agrees with `List.get`. -/
theorem mainTableRowAtOrZero_get
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    mainTableRowAtOrZero program table idx.val =
      eval (table.environment (table.table.get idx))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar := by
  unfold mainTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete unified Main table has the
    expected core `rowAt` view at every in-range index. -/
theorem rowAt_mainOfTable
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Main.rowAt (mainOfTable program table) idx.val =
      (eval (table.environment (table.table.get idx))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar).core := by
  simp [ZiskFv.AirsClean.Main.rowAt, mainTableRowAtOrZero_get program table idx]

/-- Evaluating the `core` projection of the combined Main+ROM row variable
    agrees with projecting `core` after evaluating the combined row. -/
theorem mainRowWithRom_eval_core
    (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    eval env row.core = (eval env row).core := by
  cases row
  simp [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go]

/-- Evaluating the `is_external_op` projection directly agrees with projecting
    it after evaluating the Main core row. -/
theorem mainRow_eval_is_external_op
    (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.Main.MainRow FGL) :
    Expression.eval env row.is_external_op = (eval env row).is_external_op := by
  cases row with
  | mk a_0 a_1 b_0 b_1 c_0 c_1 flag pc is_external_op op m32 ind_width
      set_pc jmp_offset1 jmp_offset2 store_pc im_high_degree_2 segment_l1 =>
    simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go] using
      (CircuitType.eval_expr env is_external_op).symm

/-- The concrete unified Main operation-bus interaction has multiplicity `-1`
    when the evaluated Main core row is active. -/
theorem main_op_row_eval_mult_neg_one_of_active
    {length : ℕ} {program : Program length}
    (env : Environment FGL)
    (h_active :
      (eval env
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core).is_external_op = 1) :
    (((OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core)).toRaw).eval env).mult = -1 := by
  have h_field :=
    mainRow_eval_is_external_op env
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar.core
  change
    Expression.eval env
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core.is_external_op) = -1
  simp [Expression.eval, h_field, h_active]

/-- Field-projection form of `rowAt_mainOfTable`, matching callers that already
    evaluate the Main core row input directly. -/
theorem rowAt_mainOfTable_core
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    eval (table.environment (table.table.get idx))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar.core =
      ZiskFv.AirsClean.Main.rowAt (mainOfTable program table) idx.val := by
  rw [rowAt_mainOfTable program table idx]
  exact mainRowWithRom_eval_core _ _

/-- The component `Spec` for a concrete unified Main table row projects to the
    named-column `Spec` for the corresponding `mainOfTable` row. -/
theorem mainSpec_rowAt_mainOfTable_of_component_spec
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length)
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_component_spec :
      table.component.Spec (table.environment (table.table.get idx))) :
    ZiskFv.AirsClean.Main.Spec
      (ZiskFv.AirsClean.Main.rowAt (mainOfTable program table) idx.val) := by
  let component :=
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
  let env := table.environment (table.table.get idx)
  have h_unified_spec :
      component.Spec env := by
    simpa [component, env, h_component] using h_component_spec
  have h_input_eq :
      eval env component.rowInputVar = component.rowInput env := by
    simpa only [component, Air.Flat.Component.rowInput,
      Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env)
  have h_core_eq :
      (component.rowInput env).core = eval env component.rowInputVar.core := by
    rw [← h_input_eq]
    exact (mainRowWithRom_eval_core env component.rowInputVar).symm
  have h_row_spec :
      ZiskFv.AirsClean.Main.Spec (eval env component.rowInputVar.core) := by
    have h_row_input_spec :
        ZiskFv.AirsClean.Main.Spec ((component.rowInput env).core) := by
      simpa [component, ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_spec]
        using h_unified_spec
    simpa [h_core_eq] using h_row_input_spec
  rw [← rowAt_mainOfTable_core program table idx]
  exact h_row_spec

/-- The legacy `opBus_row_Main` view of `mainOfTable` is the Clean Main
    operation-bus message evaluated on the same concrete row. -/
theorem opBus_row_Main_mainOfTable
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.OperationBus.opBus_row_Main (mainOfTable program table) idx.val =
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Main.opBusMessage
          (eval (table.environment (table.table.get idx))
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar).core)
        (eval (table.environment (table.table.get idx))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).core.is_external_op := by
  rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
  rw [rowAt_mainOfTable program table idx]
  simp [mainTableRowAtOrZero_get program table idx]

/-- Zero fallback for out-of-range projections from a concrete Binary table.
    In-range rows are the only rows consumed by the table bridge below. -/
@[reducible]
def zeroBinaryRow : ZiskFv.AirsClean.Binary.BinaryRow FGL where
  aBytes := {
    free_in_a_0 := 0
    free_in_a_1 := 0
    free_in_a_2 := 0
    free_in_a_3 := 0
    free_in_a_4 := 0
    free_in_a_5 := 0
    free_in_a_6 := 0
    free_in_a_7 := 0 }
  bBytes := {
    free_in_b_0 := 0
    free_in_b_1 := 0
    free_in_b_2 := 0
    free_in_b_3 := 0
    free_in_b_4 := 0
    free_in_b_5 := 0
    free_in_b_6 := 0
    free_in_b_7 := 0 }
  cBytes := {
    free_in_c_0 := 0
    free_in_c_1 := 0
    free_in_c_2 := 0
    free_in_c_3 := 0
    free_in_c_4 := 0
    free_in_c_5 := 0
    free_in_c_6 := 0
    free_in_c_7 := 0 }
  chain := {
    carry_0 := 0
    carry_1 := 0
    carry_2 := 0
    carry_3 := 0
    carry_4 := 0
    carry_5 := 0
    carry_6 := 0
    carry_7 := 0
    b_op := 0
    b_op_or_sext := 0 }
  mode := {
    mode32 := 0
    result_is_a := 0
    use_first_byte := 0
    c_is_signed := 0
    mode32_and_c_is_signed := 0 }

/-- Project row `row` of a concrete Clean Binary table to the Binary row input.
    Out-of-range rows use `zeroBinaryRow` only to make the named-column view total. -/
@[reducible]
def binaryTableRowAtOrZero
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar
  else
    zeroBinaryRow

/-- Named-column Binary view obtained from the concrete Clean Binary table. -/
@[reducible]
def binaryOfTable
    (table : Table FGL) :
    ZiskFv.Airs.Binary.Valid_Binary FGL FGL where
  b_op := fun row => (binaryTableRowAtOrZero table row).chain.b_op
  free_in_a_0 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_0
  free_in_a_1 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_1
  free_in_a_2 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_2
  free_in_a_3 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_3
  free_in_a_4 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_4
  free_in_a_5 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_5
  free_in_a_6 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_6
  free_in_a_7 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_7
  free_in_b_0 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_0
  free_in_b_1 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_1
  free_in_b_2 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_2
  free_in_b_3 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_3
  free_in_b_4 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_4
  free_in_b_5 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_5
  free_in_b_6 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_6
  free_in_b_7 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_7
  free_in_c_0 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_0
  free_in_c_1 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_1
  free_in_c_2 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_2
  free_in_c_3 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_3
  free_in_c_4 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_4
  free_in_c_5 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_5
  free_in_c_6 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_6
  free_in_c_7 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_7
  carry_0 := fun row => (binaryTableRowAtOrZero table row).chain.carry_0
  carry_1 := fun row => (binaryTableRowAtOrZero table row).chain.carry_1
  carry_2 := fun row => (binaryTableRowAtOrZero table row).chain.carry_2
  carry_3 := fun row => (binaryTableRowAtOrZero table row).chain.carry_3
  carry_4 := fun row => (binaryTableRowAtOrZero table row).chain.carry_4
  carry_5 := fun row => (binaryTableRowAtOrZero table row).chain.carry_5
  carry_6 := fun row => (binaryTableRowAtOrZero table row).chain.carry_6
  carry_7 := fun row => (binaryTableRowAtOrZero table row).chain.carry_7
  mode32 := fun row => (binaryTableRowAtOrZero table row).mode.mode32
  result_is_a := fun row => (binaryTableRowAtOrZero table row).mode.result_is_a
  use_first_byte := fun row => (binaryTableRowAtOrZero table row).mode.use_first_byte
  c_is_signed := fun row => (binaryTableRowAtOrZero table row).mode.c_is_signed
  b_op_or_sext := fun row => (binaryTableRowAtOrZero table row).chain.b_op_or_sext
  mode32_and_c_is_signed :=
    fun row => (binaryTableRowAtOrZero table row).mode.mode32_and_c_is_signed
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0
  im_2 := fun _ => 0
  im_3 := fun _ => 0

/-- In-range concrete Binary table projection agrees with `List.get`. -/
theorem binaryTableRowAtOrZero_get
    (table : Table FGL)
    (idx : Fin table.table.length) :
    binaryTableRowAtOrZero table idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar := by
  unfold binaryTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete Binary table has the expected
    `rowAt` view at every in-range index. -/
theorem rowAt_binaryOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Binary.rowAt (binaryOfTable table) idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar := by
  simp [ZiskFv.AirsClean.Binary.rowAt, binaryTableRowAtOrZero_get table idx]
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar
  change
    { aBytes := row.aBytes
      bBytes := row.bBytes
      cBytes := row.cBytes
      chain := row.chain
      mode := row.mode } = row
  cases row
  rfl

/-- The legacy `opBus_row_Binary` view of `binaryOfTable` is the Clean Binary
    operation-bus message evaluated on the same concrete row. -/
theorem opBus_row_Binary_binaryOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.OperationBus.opBus_row_Binary (binaryOfTable table) idx.val =
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (eval (table.environment (table.table.get idx))
            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1 := by
  rw [← ZiskFv.AirsClean.Binary.opBusMessage_toEntry_rowAt_eq_opBus_row]
  rw [rowAt_binaryOfTable table idx]

/-- Zero fallback for out-of-range projections from a concrete BinaryExtension
    table. In-range rows are the only rows consumed by the table bridge below. -/
@[reducible]
def zeroBinaryExtensionRow : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL where
  aCols := {
    free_in_a_0 := 0
    free_in_a_1 := 0
    free_in_a_2 := 0
    free_in_a_3 := 0
    free_in_a_4 := 0
    free_in_a_5 := 0
    free_in_a_6 := 0
    free_in_a_7 := 0 }
  cColsLo := {
    free_in_c_0 := 0
    free_in_c_1 := 0
    free_in_c_2 := 0
    free_in_c_3 := 0
    free_in_c_4 := 0
    free_in_c_5 := 0
    free_in_c_6 := 0
    free_in_c_7 := 0 }
  cColsHi := {
    free_in_c_8 := 0
    free_in_c_9 := 0
    free_in_c_10 := 0
    free_in_c_11 := 0
    free_in_c_12 := 0
    free_in_c_13 := 0
    free_in_c_14 := 0
    free_in_c_15 := 0 }
  flags := {
    op := 0
    free_in_b := 0
    op_is_shift := 0
    b_0 := 0
    b_1 := 0 }

/-- Project row `row` of a concrete Clean BinaryExtension table to the
    BinaryExtension row input. Out-of-range rows use `zeroBinaryExtensionRow`
    only to make the named-column view total. -/
@[reducible]
def binaryExtensionTableRowAtOrZero
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      shiftStaticLookupComponent.rowInputVar
  else
    zeroBinaryExtensionRow

/-- Named-column BinaryExtension view obtained from the concrete Clean
    BinaryExtension table. -/
@[reducible]
def binaryExtensionOfTable
    (table : Table FGL) :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL where
  op := fun row => (binaryExtensionTableRowAtOrZero table row).flags.op
  free_in_a_0 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_0
  free_in_a_1 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_1
  free_in_a_2 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_2
  free_in_a_3 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_3
  free_in_a_4 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_4
  free_in_a_5 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_5
  free_in_a_6 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_6
  free_in_a_7 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_7
  free_in_b := fun row => (binaryExtensionTableRowAtOrZero table row).flags.free_in_b
  free_in_c_0 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_0
  free_in_c_1 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_1
  free_in_c_2 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_2
  free_in_c_3 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_3
  free_in_c_4 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_4
  free_in_c_5 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_5
  free_in_c_6 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_6
  free_in_c_7 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_7
  free_in_c_8 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_8
  free_in_c_9 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_9
  free_in_c_10 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_10
  free_in_c_11 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_11
  free_in_c_12 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_12
  free_in_c_13 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_13
  free_in_c_14 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_14
  free_in_c_15 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_15
  op_is_shift := fun row =>
    (binaryExtensionTableRowAtOrZero table row).flags.op_is_shift
  b_0 := fun row => (binaryExtensionTableRowAtOrZero table row).flags.b_0
  b_1 := fun row => (binaryExtensionTableRowAtOrZero table row).flags.b_1
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0
  im_2 := fun _ => 0
  im_3 := fun _ => 0
  im_high_degree_0 := fun _ => 0

/-- In-range concrete BinaryExtension table projection agrees with `List.get`. -/
theorem binaryExtensionTableRowAtOrZero_get
    (table : Table FGL)
    (idx : Fin table.table.length) :
    binaryExtensionTableRowAtOrZero table idx.val =
      eval (table.environment (table.table.get idx))
        shiftStaticLookupComponent.rowInputVar := by
  unfold binaryExtensionTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete BinaryExtension table has the
    expected `rowAt` view at every in-range index. -/
theorem rowAt_binaryExtensionOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.BinaryExtension.rowAt
      (binaryExtensionOfTable table) idx.val =
      eval (table.environment (table.table.get idx))
        shiftStaticLookupComponent.rowInputVar := by
  simp [ZiskFv.AirsClean.BinaryExtension.rowAt,
    binaryExtensionTableRowAtOrZero_get table idx]
  let row :=
    eval (table.environment (table.table.get idx))
      shiftStaticLookupComponent.rowInputVar
  change
    { aCols := row.aCols
      cColsLo := row.cColsLo
      cColsHi := row.cColsHi
      flags := row.flags } = row
  cases row
  rfl

/-- The legacy `opBus_row_BinaryExtension` view of `binaryExtensionOfTable` is
    the Clean BinaryExtension operation-bus message evaluated on the same row. -/
theorem opBus_row_BinaryExtension_binaryExtensionOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension
        (binaryExtensionOfTable table) idx.val =
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (eval (table.environment (table.table.get idx))
            shiftStaticLookupComponent.rowInputVar)) 1 := by
  rw [← ZiskFv.AirsClean.BinaryExtension.opBusMessage_toEntry_rowAt_eq_opBus_row]
  rw [rowAt_binaryExtensionOfTable table idx]

/-- Zero fallback for out-of-range projections from a concrete Mem table.
    In-range rows are the only rows consumed by the table bridge below. -/
@[reducible]
def zeroMemRow : ZiskFv.AirsClean.Mem.MemRow FGL where
  addr := 0
  step := 0
  sel := 0
  addr_changes := 0
  step_dual := 0
  sel_dual := 0
  value_0 := 0
  value_1 := 0
  wr := 0
  previous_step := 0
  increment_0 := 0
  increment_1 := 0
  read_same_addr := 0
  segment_id := 0
  previous_segment_value_0 := 0
  previous_segment_value_1 := 0
  previous_segment_addr := 0
  previous_segment_step := 0
  segment_last_value_0 := 0
  segment_last_value_1 := 0
  segment_last_addr := 0
  segment_last_step := 0
  is_last_segment := 0

/-- Project row `row` of a concrete Clean Mem table to the Mem row input.
    Out-of-range rows use `zeroMemRow` only to make the named-column view total. -/
@[reducible]
def memTableRowAtOrZero
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.Mem.MemRow FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  else
    zeroMemRow

/-- Named-column Mem view obtained from the concrete Clean Mem table.

    The Clean table row input contains the primary Mem columns. The stage-2
    permutation columns are supplied separately because they are not fields of
    the Clean `MemRow`. -/
@[reducible]
def memOfTable
    (table : Table FGL)
    (gsum im0 im1 : ℕ → FGL) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL where
  addr := fun row => (memTableRowAtOrZero table row).addr
  step := fun row => (memTableRowAtOrZero table row).step
  sel := fun row => (memTableRowAtOrZero table row).sel
  addr_changes := fun row => (memTableRowAtOrZero table row).addr_changes
  step_dual := fun row => (memTableRowAtOrZero table row).step_dual
  sel_dual := fun row => (memTableRowAtOrZero table row).sel_dual
  value_0 := fun row => (memTableRowAtOrZero table row).value_0
  value_1 := fun row => (memTableRowAtOrZero table row).value_1
  wr := fun row => (memTableRowAtOrZero table row).wr
  previous_step := fun row => (memTableRowAtOrZero table row).previous_step
  increment_0 := fun row => (memTableRowAtOrZero table row).increment_0
  increment_1 := fun row => (memTableRowAtOrZero table row).increment_1
  read_same_addr := fun row => (memTableRowAtOrZero table row).read_same_addr
  gsum := gsum
  im_0 := im0
  im_1 := im1
  -- Carry the unified Mem row's segment-boundary columns (XCAP #103, route (b))
  -- so `rowAt (memOfTable ...)` reflects the concrete Clean Mem row faithfully,
  -- including its seam columns (keeping `rowAt_memOfTable` a full-row equality).
  segment_id := fun row => (memTableRowAtOrZero table row).segment_id
  previous_segment_value_0 := fun row => (memTableRowAtOrZero table row).previous_segment_value_0
  previous_segment_value_1 := fun row => (memTableRowAtOrZero table row).previous_segment_value_1
  previous_segment_addr := fun row => (memTableRowAtOrZero table row).previous_segment_addr
  previous_segment_step := fun row => (memTableRowAtOrZero table row).previous_segment_step
  segment_last_value_0 := fun row => (memTableRowAtOrZero table row).segment_last_value_0
  segment_last_value_1 := fun row => (memTableRowAtOrZero table row).segment_last_value_1
  segment_last_addr := fun row => (memTableRowAtOrZero table row).segment_last_addr
  segment_last_step := fun row => (memTableRowAtOrZero table row).segment_last_step
  is_last_segment := fun row => (memTableRowAtOrZero table row).is_last_segment

/-- In-range concrete table projection agrees with `List.get`. -/
theorem memTableRowAtOrZero_get
    (table : Table FGL)
    (idx : Fin table.table.length) :
    memTableRowAtOrZero table idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar := by
  unfold memTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete Mem table has the expected
    `rowAt` view at every in-range index. -/
theorem rowAt_memOfTable
    (table : Table FGL)
    (gsum im0 im1 : ℕ → FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.rowAt (memOfTable table gsum im0 im1) idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar := by
  simp [ZiskFv.AirsClean.Mem.rowAt, memTableRowAtOrZero_get table idx]
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  change
    { addr := row.addr
      step := row.step
      sel := row.sel
      addr_changes := row.addr_changes
      step_dual := row.step_dual
      sel_dual := row.sel_dual
      value_0 := row.value_0
      value_1 := row.value_1
      wr := row.wr
      previous_step := row.previous_step
      increment_0 := row.increment_0
      increment_1 := row.increment_1
      read_same_addr := row.read_same_addr
      segment_id := row.segment_id
      previous_segment_value_0 := row.previous_segment_value_0
      previous_segment_value_1 := row.previous_segment_value_1
      previous_segment_addr := row.previous_segment_addr
      previous_segment_step := row.previous_segment_step
      segment_last_value_0 := row.segment_last_value_0
      segment_last_value_1 := row.segment_last_value_1
      segment_last_addr := row.segment_last_addr
      segment_last_step := row.segment_last_step
      is_last_segment := row.is_last_segment } = row
  cases row
  rfl

/-- Continuation-segment initial memory: start from the finite zero preload for
    the table's active rows, then seed the previous segment's carried-out bytes. -/
@[reducible]
def previousSegmentInitialMemoryOfRows
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry
    (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows rows)
    (memPreviousSegmentReplayEntry segment)

/-- Explicit row-index bridge from a concrete Clean Mem table to the
    row-indexed generated `Valid_Mem` surface.

    `Table.Constraints` is membership-based (`∀ row ∈ table.table`) and does
    not identify a row's list position with the index consumed by
    `Valid_Mem`/`generated_every_row`. This structure names that missing
    connection without turning it into an anonymous replay-soundness field:
    each concrete table position must evaluate to `rowAt mem idx`, and the
    generated Mem constraints must hold at the same index.

    The generated constraint field cites the complete extracted Mem surface:
    `generated_every_row = segment_every_row ∧ permutation_every_row`, whose
    constituent lemmas mirror the cited `mem.pil` constraints. -/
structure MemTableGeneratedRowsBridge
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop where
  component :
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
  length_eq : table.table.length = rowCount
  rowAt_eq :
    ∀ idx : Fin table.table.length,
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val
  generatedAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val

/-- Build the indexed row bridge from the concrete table projection.

    This discharges the list-position/`rowAt` part definitionally. The remaining
    caller input is exactly the generated Mem every-row fact for that projected
    named-column view. -/
theorem memTableGeneratedRowsBridge_of_memOfTable
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          segment permutation (memOfTable table gsum im0 im1) idx.val) :
    MemTableGeneratedRowsBridge
      table (memOfTable table gsum im0 im1)
      segment permutation table.table.length where
  component := h_component
  length_eq := rfl
  rowAt_eq := by
    intro idx
    exact (rowAt_memOfTable table gsum im0 im1 idx).symm
  generatedAt := h_generatedAt

/-- Concrete range facts for the indexed Mem table rows.

    These facts name the non-field AIR range-check surface used when turning
    generated field equations into Nat timestamp order:

    * `incrementChunks` mirrors `mem.pil:384-385`.
    * `addrColumns` mirrors `mem.pil:109`, where `addr` is `bits(29)`;
      this is the no-wrap fact needed for byte-address disjointness of
      provider pointers `addr * 8`.
    * `stepColumns` mirrors the `bits(MEM_STEP_BITS)` witness declarations at
      `mem.pil:110` and `mem.pil:122`, with `MEM_STEP_BITS = 40` in the pinned
      RV64IM configuration.
    * `dualStepDelta` mirrors the selector-gated range check
      `mem.pil:397`; it is intentionally conditional on `sel_dual = 1`.

    Keeping this separate from `MemTableGeneratedRowsBridge` avoids silently
    treating selector-gated range checks as unconditional replay soundness. -/
structure MemTableGeneratedRangeFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) : Prop where
  incrementChunks :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.increment_chunks_in_range mem idx.val
  addrColumns :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.addr_columns_in_range mem idx.val
  stepColumns :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.step_columns_in_range mem idx.val
  dualStepDelta :
    ∀ idx : Fin table.table.length,
      mem.sel_dual idx.val = 1 →
        ZiskFv.Airs.Mem.dual_step_delta_in_range mem idx.val

/-- Segment-level range facts for one generated Mem table segment.

    These facts name the segment-global range-check surface used by
    continuation-segment replay:

    * `distanceBaseChunks` mirrors `mem.pil:267-268`, where
      `distance_base[0]` and `distance_base[1]` are 16-bit chunks.

    Together with the generated `mem.pil:265` equation already present in
    `segment_every_row`, these chunks give a coarse bound on
    `previous_segment_addr`. Row-0 generated facts then refine that bound to
    the 29-bit Mem address range required for byte-address no-wrap. -/
structure MemSegmentGeneratedRangeFacts
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) : Prop where
  distanceBaseChunks :
    ZiskFv.Airs.Mem.distance_chunks_in_range
      segment.distance_base_0 segment.distance_base_1

/-- Clean lookup source for the concrete Mem table row range facts.

    This exposes the range-check provenance separately from the replay proof:
    ungated row ranges come from `rowRangeLookups`, while the dual-step delta
    lookup is requested only for rows with `sel_dual = 1`, matching the
    selector-gated `mem.pil:397` range check. -/
structure MemTableGeneratedRangeLookupFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) : Type 1 where
  rowRanges :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.RowRangeLookupWitness mem idx.val
  dualStepDelta :
    ∀ idx : Fin table.table.length,
      mem.sel_dual idx.val = 1 →
        ZiskFv.AirsClean.Mem.DualStepDeltaRangeLookupWitness mem idx.val

/-- Project concrete Mem table row range facts from lookup-aware Clean
    witnesses. -/
def memTableGeneratedRangeFacts_of_lookupFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h_lookup : MemTableGeneratedRangeLookupFacts table mem) :
    MemTableGeneratedRangeFacts table mem where
  incrementChunks := by
    intro idx
    exact (ZiskFv.AirsClean.Mem.row_ranges_of_lookup_aware_const_soundness
      (h_lookup.rowRanges idx)).1
  addrColumns := by
    intro idx
    exact (ZiskFv.AirsClean.Mem.row_ranges_of_lookup_aware_const_soundness
      (h_lookup.rowRanges idx)).2.1
  stepColumns := by
    intro idx
    exact (ZiskFv.AirsClean.Mem.row_ranges_of_lookup_aware_const_soundness
      (h_lookup.rowRanges idx)).2.2
  dualStepDelta := by
    intro idx h_sel_dual
    exact ZiskFv.AirsClean.Mem.dual_step_delta_in_range_of_lookup_aware_const_soundness
      (h_lookup.dualStepDelta idx h_sel_dual)

/-- Build lookup-aware Mem row range witnesses from the raw generated range
    propositions. This keeps the witness-aware source API constructible for
    generated Lean modules that prove the range facts directly. -/
def memTableGeneratedRangeLookupFacts_of_rangeFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h_ranges : MemTableGeneratedRangeFacts table mem) :
    MemTableGeneratedRangeLookupFacts table mem where
  rowRanges := by
    intro idx
    exact ZiskFv.AirsClean.Mem.rowRangeLookupWitness_of_range_facts
      (h_ranges.incrementChunks idx)
      (h_ranges.addrColumns idx)
      (h_ranges.stepColumns idx)
  dualStepDelta := by
    intro idx h_sel_dual
    exact ZiskFv.AirsClean.Mem.dualStepDeltaRangeLookupWitness_of_range_fact
      (h_ranges.dualStepDelta idx h_sel_dual)

/-- Clean lookup source for the segment-level Mem distance-base range facts. -/
structure MemSegmentGeneratedRangeLookupFacts
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) : Type 1 where
  distanceBaseChunks :
    ZiskFv.AirsClean.Mem.DistanceBaseRangeLookupWitness
      segment.distance_base_0 segment.distance_base_1

/-- Project segment-level Mem range facts from lookup-aware Clean witnesses. -/
def memSegmentGeneratedRangeFacts_of_lookupFacts
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    (h_lookup : MemSegmentGeneratedRangeLookupFacts segment) :
    MemSegmentGeneratedRangeFacts segment where
  distanceBaseChunks :=
    ZiskFv.AirsClean.Mem.distance_chunks_in_range_of_lookup_aware_const_soundness
      h_lookup.distanceBaseChunks

/-- Build lookup-aware segment range witnesses from the raw generated segment
    range propositions. -/
def memSegmentGeneratedRangeLookupFacts_of_rangeFacts
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    (h_ranges : MemSegmentGeneratedRangeFacts segment) :
    MemSegmentGeneratedRangeLookupFacts segment where
  distanceBaseChunks :=
    ZiskFv.AirsClean.Mem.distanceBaseRangeLookupWitness_of_range_fact
      h_ranges.distanceBaseChunks

/-- Extractor-facing generated Mem AIR facts for one concrete table segment.

    This is the remaining generated/source surface after the table projection,
    fixed `SEGMENT_L1` shape, active-row equality, and nonempty evidence are
    constructed locally. It intentionally contains only PIL-generated row facts
    and range-check facts; replay soundness is derived downstream from these
    facts by `acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts`. -/
structure MemTableGeneratedAirFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Prop where
  generatedAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val
  rowRanges : MemTableGeneratedRangeFacts table mem
  segmentRanges : MemSegmentGeneratedRangeFacts segment

/-- Split extractor-facing generated Mem constraints for one concrete table.

    `pil-extract mem-air-facts` reports this exact split: generated Mem
    constraints `0..=23` are the `segment_every_row` surface, and constraints
    `24..=33` are the `permutation_every_row` surface. A generated Lean module
    can prove these two fields separately, then assemble
    `MemTableGeneratedAirFacts` without reintroducing a replay-soundness
    assumption. -/
structure MemTableGeneratedConstraintFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Prop where
  segmentAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.segment_every_row segment mem idx.val
  permutationAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.permutation_every_row segment permutation mem idx.val

/-- Type-level package for raw generated Mem facts.

    The individual raw fact families are `Prop`, so this wrapper lets witness
    source callbacks carry them alongside source columns in `Type`. -/
structure MemTableGeneratedRawSourceFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Type where
  constraints : MemTableGeneratedConstraintFacts table mem segment permutation
  rowRanges : MemTableGeneratedRangeFacts table mem
  segmentRanges : MemSegmentGeneratedRangeFacts segment

/-- Clean assertion source for the split generated Mem constraint groups. -/
structure MemTableGeneratedConstraintAssertionFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Type 1 where
  segmentAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.SegmentConstraintAssertionWitness segment mem idx.val
  permutationAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.PermutationConstraintAssertionWitness
        segment permutation mem idx.val

/-- Project split generated Mem constraint facts from their Clean assertion
    witnesses. -/
def memTableGeneratedConstraintFacts_of_assertionFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_assertions :
      MemTableGeneratedConstraintAssertionFacts table mem segment permutation) :
    MemTableGeneratedConstraintFacts table mem segment permutation where
  segmentAt := by
    intro idx
    exact ZiskFv.AirsClean.Mem.segment_every_row_of_constraint_assertions
      (h_assertions.segmentAt idx)
  permutationAt := by
    intro idx
    exact ZiskFv.AirsClean.Mem.permutation_every_row_of_constraint_assertions
      (h_assertions.permutationAt idx)

/-- Build Clean assertion witnesses from raw split generated Mem constraints.

    The assertion circuits contain only constant assertions over the named
    source columns, so this adapter does not add proof content; it just packages
    raw generated facts in the witness-aware source shape. -/
def memTableGeneratedConstraintAssertionFacts_of_constraintFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintFacts table mem segment permutation) :
    MemTableGeneratedConstraintAssertionFacts table mem segment permutation where
  segmentAt := by
    intro idx
    exact ZiskFv.AirsClean.Mem.segmentConstraintAssertionWitness_of_segment_every_row
      (h_constraints.segmentAt idx)
  permutationAt := by
    intro idx
    exact
      ZiskFv.AirsClean.Mem.permutationConstraintAssertionWitness_of_permutation_every_row
        (h_constraints.permutationAt idx)

/-- Recombine the extractor's split generated-constraint groups into the
    `generated_every_row` package consumed by existing replay proofs. -/
theorem generatedAt_of_memTableGeneratedConstraintFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintFacts table mem segment permutation) :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val := by
  intro idx
  exact ⟨h_constraints.segmentAt idx, h_constraints.permutationAt idx⟩

/-- Assemble `MemTableGeneratedAirFacts` from the extractor's split generated
    constraint groups plus the explicit range-check surfaces. -/
def memTableGeneratedAirFacts_of_constraintFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintFacts table mem segment permutation)
    (h_rowRanges : MemTableGeneratedRangeFacts table mem)
    (h_segmentRanges : MemSegmentGeneratedRangeFacts segment) :
    MemTableGeneratedAirFacts table mem segment permutation where
  generatedAt := generatedAt_of_memTableGeneratedConstraintFacts h_constraints
  rowRanges := h_rowRanges
  segmentRanges := h_segmentRanges

/-- Assemble raw generated Mem source facts from concrete Clean assertion and
    lookup witnesses. -/
def memTableGeneratedRawSourceFacts_of_witnessFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts table mem segment permutation)
    (h_rowRanges : MemTableGeneratedRangeLookupFacts table mem)
    (h_segmentRanges : MemSegmentGeneratedRangeLookupFacts segment) :
    MemTableGeneratedRawSourceFacts table mem segment permutation where
  constraints := memTableGeneratedConstraintFacts_of_assertionFacts h_constraints
  rowRanges := memTableGeneratedRangeFacts_of_lookupFacts h_rowRanges
  segmentRanges := memSegmentGeneratedRangeFacts_of_lookupFacts h_segmentRanges

/-- Build the indexed row bridge from the concrete table projection and the
    compact generated AIR fact package. -/
theorem memTableGeneratedRowsBridge_of_memOfTable_airFacts
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1) segment permutation) :
    MemTableGeneratedRowsBridge
      table (memOfTable table gsum im0 im1)
      segment permutation table.table.length :=
  memTableGeneratedRowsBridge_of_memOfTable h_component h_air.generatedAt

/-- Fixed-column facts for one generated Mem table segment.

    This records the deterministic fixed column declared in `mem.pil:86`:
    `col fixed SEGMENT_L1 = [1,0...]`. The first row of the table segment is a
    segment boundary, and every positive row index is non-boundary. Keeping
    this separate from `MemTableGeneratedRowsBridge` makes the fixed-column
    constructibility obligation explicit instead of hiding it in replay
    evidence. -/
structure MemTableGeneratedFixedColumnFacts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) : Prop where
  segmentL1_first :
    0 < table.table.length → segment.segment_l1 0 = 1
  segmentL1_nonfirst :
    ∀ idx : Fin table.table.length,
      0 < idx.val → segment.segment_l1 idx.val = 0

/-- Replace a segment-column package's fixed `SEGMENT_L1` column by its
    deterministic shape: row 0 is `1`, all later rows are `0`. -/
@[reducible]
def segmentWithFixedL1
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  { segment with segment_l1 := fun row => if row = 0 then 1 else 0 }

/-- The deterministic `SEGMENT_L1` projection supplies the fixed-column facts
    required by the Mem replay bridge. -/
theorem memTableGeneratedFixedColumnFacts_of_segmentWithFixedL1
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) :
    MemTableGeneratedFixedColumnFacts table (segmentWithFixedL1 segment) where
  segmentL1_first := by
    intro _h_nonempty
    simp
  segmentL1_nonfirst := by
    intro idx h_pos
    have h_ne : idx.val ≠ 0 := Nat.ne_of_gt h_pos
    simp [h_ne]

/-- Typed Lean target for the Mem AIR facts source reported by
    `pil-extract mem-air-facts`.

    The extractor/report surface identifies the stage-2 accumulator columns,
    the generated segment/permutation formulas, the fixed `SEGMENT_L1` shape,
    and the range-check metadata. This object packages those source columns and
    the resulting `MemTableGeneratedAirFacts` for the concrete table projection.
    It is deliberately a source package, not replay evidence: accepted replay
    and timeline evidence are derived by the constructors below. -/
structure MemTableGeneratedAirSource
    (table : Table FGL) : Type 1 where
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  gsum : ℕ → FGL
  im0 : ℕ → FGL
  im1 : ℕ → FGL
  facts :
    MemTableGeneratedAirFacts
      table (memOfTable table gsum im0 im1)
      (segmentWithFixedL1 segment) permutation

namespace MemTableGeneratedAirSource

@[reducible]
def mem {table : Table FGL} (source : MemTableGeneratedAirSource table) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL :=
  memOfTable table source.gsum source.im0 source.im1

@[reducible]
def fixedSegment {table : Table FGL} (source : MemTableGeneratedAirSource table) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  segmentWithFixedL1 source.segment

theorem toFacts {table : Table FGL} (source : MemTableGeneratedAirSource table) :
    MemTableGeneratedAirFacts table source.mem source.fixedSegment source.permutation :=
  source.facts

end MemTableGeneratedAirSource

/-! ### Prover-data-backed Mem sidecar columns -/

/- `ProverData` keys for the generated Mem sidecar columns.

   These names are the Lean-side contract for generated/full-ensemble code:
   each key stores a one-column array (`n = 1`) whose row `0` is used for
   scalars and whose row index is used for table columns. The source map in
   `MemAirFacts.md` ties these keys to pilout witness columns, fixed columns,
   AIR_VALUE entries, and challenges. -/
namespace MemRawSidecarDataKey

abbrev gsum : String := "Mem.sidecar.gsum"
abbrev im0 : String := "Mem.sidecar.im0"
abbrev im1 : String := "Mem.sidecar.im1"

namespace Segment

abbrev segmentId : String := "Mem.sidecar.segment.segment_id"
abbrev isFirstSegment : String := "Mem.sidecar.segment.is_first_segment"
abbrev isLastSegment : String := "Mem.sidecar.segment.is_last_segment"
abbrev previousSegmentValue0 : String := "Mem.sidecar.segment.previous_segment_value_0"
abbrev previousSegmentValue1 : String := "Mem.sidecar.segment.previous_segment_value_1"
abbrev previousSegmentStep : String := "Mem.sidecar.segment.previous_segment_step"
abbrev previousSegmentAddr : String := "Mem.sidecar.segment.previous_segment_addr"
abbrev segmentLastValue0 : String := "Mem.sidecar.segment.segment_last_value_0"
abbrev segmentLastValue1 : String := "Mem.sidecar.segment.segment_last_value_1"
abbrev segmentLastStep : String := "Mem.sidecar.segment.segment_last_step"
abbrev segmentLastAddr : String := "Mem.sidecar.segment.segment_last_addr"
abbrev distanceBase0 : String := "Mem.sidecar.segment.distance_base_0"
abbrev distanceBase1 : String := "Mem.sidecar.segment.distance_base_1"
abbrev distanceEnd0 : String := "Mem.sidecar.segment.distance_end_0"
abbrev distanceEnd1 : String := "Mem.sidecar.segment.distance_end_1"
abbrev segmentL1 : String := "Mem.sidecar.segment.segment_l1"

end Segment

namespace Permutation

abbrev stdAlpha : String := "Mem.sidecar.permutation.std_alpha"
abbrev stdGamma : String := "Mem.sidecar.permutation.std_gamma"
abbrev l1 : String := "Mem.sidecar.permutation.l1"
abbrev imDirect0 : String := "Mem.sidecar.permutation.im_direct_0"
abbrev imDirect1 : String := "Mem.sidecar.permutation.im_direct_1"
abbrev imDirect2 : String := "Mem.sidecar.permutation.im_direct_2"
abbrev imDirect3 : String := "Mem.sidecar.permutation.im_direct_3"
abbrev imDirect4 : String := "Mem.sidecar.permutation.im_direct_4"
abbrev imDirect5 : String := "Mem.sidecar.permutation.im_direct_5"

end Permutation

end MemRawSidecarDataKey

/-- Read one field element from a one-column `ProverData` array.

    Missing keys or out-of-range rows default to zero, matching Clean's
    `Environment.fromArray` convention for absent witness cells. Correctness
    is not hidden here: generated code must still prove
    `MemTableGeneratedRawSourceFacts` for the columns read by this function. -/
@[reducible]
def proverDataColumn (data : ProverData FGL) (key : String) (row : ℕ) : FGL :=
  match (data key 1)[row]? with
  | some values => values[0]
  | none => 0

/-- Read a scalar sidecar value from row `0` of a one-column `ProverData`
    array. -/
@[reducible]
def proverDataScalar (data : ProverData FGL) (key : String) : FGL :=
  proverDataColumn data key 0

@[reducible]
def memSidecarGsumOfProverData (data : ProverData FGL) : ℕ → FGL :=
  proverDataColumn data MemRawSidecarDataKey.gsum

@[reducible]
def memSidecarIm0OfProverData (data : ProverData FGL) : ℕ → FGL :=
  proverDataColumn data MemRawSidecarDataKey.im0

@[reducible]
def memSidecarIm1OfProverData (data : ProverData FGL) : ℕ → FGL :=
  proverDataColumn data MemRawSidecarDataKey.im1

/-- Segment sidecar columns read from the shared Clean `ProverData` map. -/
@[reducible]
def memSegmentColumnsOfProverData
    (data : ProverData FGL) :
    ZiskFv.Airs.Mem.SegmentColumns FGL where
  segment_id := proverDataScalar data MemRawSidecarDataKey.Segment.segmentId
  is_first_segment := proverDataScalar data MemRawSidecarDataKey.Segment.isFirstSegment
  is_last_segment := proverDataScalar data MemRawSidecarDataKey.Segment.isLastSegment
  previous_segment_value_0 :=
    proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentValue0
  previous_segment_value_1 :=
    proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentValue1
  previous_segment_step := proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentStep
  previous_segment_addr := proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentAddr
  segment_last_value_0 := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastValue0
  segment_last_value_1 := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastValue1
  segment_last_step := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastStep
  segment_last_addr := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastAddr
  distance_base_0 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase0
  distance_base_1 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase1
  distance_end_0 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd0
  distance_end_1 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd1
  segment_l1 := proverDataColumn data MemRawSidecarDataKey.Segment.segmentL1

/-- Permutation/direct-update sidecar columns read from the shared Clean
    `ProverData` map. -/
@[reducible]
def memPermutationColumnsOfProverData
    (data : ProverData FGL) :
    ZiskFv.Airs.Mem.PermutationColumns FGL where
  std_alpha := proverDataScalar data MemRawSidecarDataKey.Permutation.stdAlpha
  std_gamma := proverDataScalar data MemRawSidecarDataKey.Permutation.stdGamma
  l1 := proverDataColumn data MemRawSidecarDataKey.Permutation.l1
  im_direct_0 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect0
  im_direct_1 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect1
  im_direct_2 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect2
  im_direct_3 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect3
  im_direct_4 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect4
  im_direct_5 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect5

/-- Table-level sidecar for generated raw Mem AIR source data.

    Generated/full-ensemble code can use this object when it has the concrete
    stage-2 columns and raw split facts for one witness table, but has not yet
    packaged them into the witness-wide `FullWitnessMemAirSourceRawFacts`
    callback. This remains a source-data contract: the raw facts are supplied
    explicitly, and replay evidence is still derived downstream. -/
structure MemTableGeneratedRawSourceSidecar
    (table : Table FGL) : Type 1 where
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  gsum : ℕ → FGL
  im0 : ℕ → FGL
  im1 : ℕ → FGL
  facts :
    MemTableGeneratedRawSourceFacts
      table (memOfTable table gsum im0 im1)
      (segmentWithFixedL1 segment) permutation

namespace MemTableGeneratedRawSourceSidecar

@[reducible]
def mem {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL :=
  memOfTable table sidecar.gsum sidecar.im0 sidecar.im1

@[reducible]
def fixedSegment {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  segmentWithFixedL1 sidecar.segment

def toRawFacts {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    MemTableGeneratedRawSourceFacts
      table sidecar.mem sidecar.fixedSegment sidecar.permutation :=
  sidecar.facts

def toAirFacts {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    MemTableGeneratedAirFacts table sidecar.mem sidecar.fixedSegment sidecar.permutation :=
  memTableGeneratedAirFacts_of_constraintFacts
    sidecar.facts.constraints
    sidecar.facts.rowRanges
    sidecar.facts.segmentRanges

def toAirSource {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    MemTableGeneratedAirSource table where
  segment := sidecar.segment
  permutation := sidecar.permutation
  gsum := sidecar.gsum
  im0 := sidecar.im0
  im1 := sidecar.im1
  facts := sidecar.toAirFacts

end MemTableGeneratedRawSourceSidecar

/-- Build a raw Mem sidecar from the shared Clean `ProverData` map.

    This is the generated/full-ensemble entry point when sidecar columns are
    stored in `witness.data`: the raw facts must be proved for the exact
    ProverData-backed columns defined above, then this constructor packages
    them as a `MemTableGeneratedRawSourceSidecar`. -/
def memTableGeneratedRawSourceSidecar_of_proverData
    (table : Table FGL)
    (data : ProverData FGL)
    (h_facts :
      MemTableGeneratedRawSourceFacts
        table
        (memOfTable table
          (memSidecarGsumOfProverData data)
          (memSidecarIm0OfProverData data)
          (memSidecarIm1OfProverData data))
        (segmentWithFixedL1 (memSegmentColumnsOfProverData data))
        (memPermutationColumnsOfProverData data)) :
    MemTableGeneratedRawSourceSidecar table where
  segment := memSegmentColumnsOfProverData data
  permutation := memPermutationColumnsOfProverData data
  gsum := memSidecarGsumOfProverData data
  im0 := memSidecarIm0OfProverData data
  im1 := memSidecarIm1OfProverData data
  facts := h_facts

/-- Build a raw Mem sidecar from `ProverData` columns plus concrete Clean
    assertion and lookup witnesses for those columns. -/
def memTableGeneratedRawSourceSidecar_of_proverDataWitnessFacts
    (table : Table FGL)
    (data : ProverData FGL)
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts
        table
        (memOfTable table
          (memSidecarGsumOfProverData data)
          (memSidecarIm0OfProverData data)
          (memSidecarIm1OfProverData data))
        (segmentWithFixedL1 (memSegmentColumnsOfProverData data))
        (memPermutationColumnsOfProverData data))
    (h_rowRanges :
      MemTableGeneratedRangeLookupFacts
        table
        (memOfTable table
          (memSidecarGsumOfProverData data)
          (memSidecarIm0OfProverData data)
          (memSidecarIm1OfProverData data)))
    (h_segmentRanges :
      MemSegmentGeneratedRangeLookupFacts
        (segmentWithFixedL1 (memSegmentColumnsOfProverData data))) :
    MemTableGeneratedRawSourceSidecar table :=
  memTableGeneratedRawSourceSidecar_of_proverData
    table
    data
    (memTableGeneratedRawSourceFacts_of_witnessFacts
      h_constraints
      h_rowRanges
      h_segmentRanges)

/-- Build the typed Mem AIR source from the three extractor-facing fact
    families. This is the narrow constructor a future generated Lean module can
    call after proving the pilout-generated row constraints and range facts for
    the concrete table projection. -/
def memTableGeneratedAirSource_of_parts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          (segmentWithFixedL1 segment) permutation
          (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment)) :
    MemTableGeneratedAirSource table where
  segment := segment
  permutation := permutation
  gsum := gsum
  im0 := im0
  im1 := im1
  facts :=
    { generatedAt := h_generatedAt
      rowRanges := h_rowRanges
      segmentRanges := h_segmentRanges }

/-- Build the typed Mem AIR source from the extractor's split generated
    constraint groups. This mirrors the generated constraint grouping reported
    by `pil-extract mem-air-facts`: segment constraints `0..=23`, permutation
    constraints `24..=33`, and the explicit range-check facts. -/
def memTableGeneratedAirSource_of_constraintFacts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_constraints :
      MemTableGeneratedConstraintFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment)) :
    MemTableGeneratedAirSource table :=
  memTableGeneratedAirSource_of_parts
    table segment permutation gsum im0 im1
    (generatedAt_of_memTableGeneratedConstraintFacts h_constraints)
    h_rowRanges
    h_segmentRanges

/-- Build the typed Mem AIR source from concrete Clean assertion and lookup
    witnesses.

    This is the narrow generated/full-ensemble target after the Mem source
    surface has been made lookup-aware: generated code supplies assertion
    witnesses for the split generated constraints plus lookup witnesses for the
    row and segment range facts, and Lean projects those witnesses to the raw
    AIR facts consumed by replay. -/
def memTableGeneratedAirSource_of_witnessFacts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_rowRanges :
      MemTableGeneratedRangeLookupFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges :
      MemSegmentGeneratedRangeLookupFacts (segmentWithFixedL1 segment)) :
    MemTableGeneratedAirSource table :=
  memTableGeneratedAirSource_of_constraintFacts
    table segment permutation gsum im0 im1
    (memTableGeneratedConstraintFacts_of_assertionFacts h_constraints)
    (memTableGeneratedRangeFacts_of_lookupFacts h_rowRanges)
    (memSegmentGeneratedRangeFacts_of_lookupFacts h_segmentRanges)

/-- Any active replay entry from a generated Mem table row is either at the
    same byte pointer as the selected primary row or byte-disjoint from it.

    This packages the `mem.pil:109` address range (`addrColumns`) with the
    provider pointer conversion `addr * 8`. -/
theorem activeMemReplayEntry_same_ptr_or_byteDisjoint_of_rowAt
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (selectedIdx otherIdx : Fin table.table.length)
    {entry : Interaction.MemoryBusEntry FGL}
    (h_entry :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val)) :
    entry.ptr =
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val)).ptr
      ∨ ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val))
        entry := by
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry with
    h_entry_primary | h_entry_dual
  · by_cases h_addr :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr =
        (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr
    · left
      have h_addr_mem : mem.addr otherIdx.val = mem.addr selectedIdx.val := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr
      simp [h_entry_primary, memPrimaryReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.memBusMessage, h_addr_mem]
    · right
      have h_selected_range :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns selectedIdx
      have h_other_range :
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
      have h_addr_ne :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr ≠
            (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
        intro h_eq
        exact h_addr h_eq.symm
      simpa [h_entry_primary] using
        memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
          h_selected_range h_other_range h_addr_ne
  · by_cases h_addr :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr =
        (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr
    · left
      have h_addr_mem : mem.addr otherIdx.val = mem.addr selectedIdx.val := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr
      simp [h_entry_dual, memDualReadReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.memBusDualMessage, h_addr_mem]
    · right
      have h_selected_range :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns selectedIdx
      have h_other_range :
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
      have h_addr_ne :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr ≠
            (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
        intro h_eq
        exact h_addr h_eq.symm
      simpa [h_entry_dual] using
        memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
          h_selected_range h_other_range h_addr_ne

/-- The indexed table bridge projects the generated row range required by
    the Mem trace spec. -/
theorem generatedMemRows_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount) :
    ZiskFv.AirsClean.Mem.GeneratedMemRows mem segment permutation rowCount := by
  intro row h_row
  have h_len : row < table.table.length := by
    rw [h_bridge.length_eq]
    exact h_row
  exact h_bridge.generatedAt ⟨row, h_len⟩

/-- Full-ensemble witness obligation for the concrete mutable Mem table:
    one witness table must be the dual-aware Mem component and must satisfy the
    indexed `Valid_Mem` bridge above. -/
def FullWitnessMemTableGeneratedRowsBridge
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop :=
  ∃ table ∈ witness.allTables,
    MemTableGeneratedRowsBridge table mem segment permutation rowCount

/-- Full-ensemble witness obligation for constructing circuit-side accepted
    memory replay evidence from the concrete mutable Mem table.

    This is intentionally a compact extractor-facing bridge rather than a
    replay-soundness field. It exposes every remaining concrete fact needed by
    `acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts`:
    the table selected from the full witness, the active replay row projection,
    generated Mem row constraints, row/segment range checks, fixed-column shape,
    and nonempty segment evidence. -/
structure FullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type 2 where
  table : Table FGL
  table_mem : table ∈ witness.allTables
  mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  rowCount : ℕ
  rows_eq : rows = activeMemReplayRowsOfTable table
  generatedRows : MemTableGeneratedRowsBridge table mem segment permutation rowCount
  rowRanges : MemTableGeneratedRangeFacts table mem
  segmentRanges : MemSegmentGeneratedRangeFacts segment
  fixedColumns : MemTableGeneratedFixedColumnFacts table segment
  nonempty : 0 < table.table.length

/-- Construct the full-witness replay bridge from the concrete Mem table
    projection and the remaining generated/range/fixed-column facts.

    This is the intended extractor-facing constructor: table membership,
    component identity, row projection, row count, and accepted-row projection
    are no longer independent bridge fields. -/
def fullWitnessMemReplayBridge_of_memTable
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          segment permutation (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts segment)
    (h_fixedColumns : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  { table := table
    table_mem := h_table
    mem := memOfTable table gsum im0 im1
    segment := segment
    permutation := permutation
    rowCount := table.table.length
    rows_eq := rfl
    generatedRows :=
      memTableGeneratedRowsBridge_of_memOfTable h_component h_generatedAt
    rowRanges := h_rowRanges
    segmentRanges := h_segmentRanges
    fixedColumns := h_fixedColumns
    nonempty := h_nonempty }

/-- Construct the full-witness replay bridge using the deterministic
    `SEGMENT_L1` fixed-column shape. The remaining caller-facing inputs are the
    generated every-row facts, row/segment range facts, and nonempty table
    evidence. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          (segmentWithFixedL1 segment) permutation
          (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment))
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable
    h_table
    h_component
    h_generatedAt
    h_rowRanges
    h_segmentRanges
    (memTableGeneratedFixedColumnFacts_of_segmentWithFixedL1 table segment)
    h_nonempty

/-- Construct the full-witness replay bridge from the compact generated AIR
    fact package, using the deterministic `SEGMENT_L1` shape. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1
    h_table
    h_component
    h_air.generatedAt
    h_air.rowRanges
    h_air.segmentRanges
    h_nonempty

/-- Construct the full-witness replay bridge from the typed Mem AIR source
    package. This is the Lean-facing target for generated/extractor output:
    callers supply the concrete table membership/component facts plus one
    `MemTableGeneratedAirSource`, not loose stage-2/source columns. -/
def fullWitnessMemReplayBridge_of_memAirSource
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (source : MemTableGeneratedAirSource table)
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts
    (segment := source.segment) (permutation := source.permutation)
    (gsum := source.gsum) (im0 := source.im0) (im1 := source.im1)
    h_table
    h_component
    source.facts
    h_nonempty

/-- Variant of `fullWitnessMemReplayBridge_of_memTable_fixedL1` that derives
    concrete-table nonemptiness from the active replay projection. This is the
    shape used when a selected-load timeline split is already available. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          (segmentWithFixedL1 segment) permutation
          (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment))
    (h_activeRows : 0 < (activeMemReplayRowsOfTable table).length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1
    h_table
    h_component
    h_generatedAt
    h_rowRanges
    h_segmentRanges
    (table_nonempty_of_activeMemReplayRowsOfTable_nonempty h_activeRows)

/-- Active-row variant of
    `fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts`: the table
    nonemptiness needed by accepted replay is derived from the accepted active
    row projection. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows_airFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_activeRows : 0 < (activeMemReplayRowsOfTable table).length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts
    h_table
    h_component
    h_air
    (table_nonempty_of_activeMemReplayRowsOfTable_nonempty h_activeRows)

/-- Trace-split variant of
    `fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows_airFacts`.
    The selected-entry split proves the active Mem replay projection is
    nonempty, so callers only supply the generated AIR facts and residual
    timeline split. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_traceSplit_airFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_traceSplit :
      activeMemReplayRowsOfTable table = priorRows ++ entry :: laterRows) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows_airFacts
    h_table
    h_component
    h_air
    (activeMemReplayRowsOfTable_nonempty_of_split h_traceSplit)

/-- Trace-split variant of `fullWitnessMemReplayBridge_of_memAirSource`.
    The source object supplies the generated AIR facts, and the selected-entry
    split supplies table nonemptiness. -/
def fullWitnessMemReplayBridge_of_memAirSource_traceSplit
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (source : MemTableGeneratedAirSource table)
    (h_traceSplit :
      activeMemReplayRowsOfTable table = priorRows ++ entry :: laterRows) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memAirSource
    h_table
    h_component
    source
    (table_nonempty_of_activeMemReplayRowsOfTable_nonempty
      (activeMemReplayRowsOfTable_nonempty_of_split h_traceSplit))

/-- Full-witness Mem AIR source for one mutable Mem table.

    This is the generated/full-ensemble source object: it identifies the
    witness-selected mutable Mem table and carries the `MemTableGeneratedAirSource`
    that derives the replay bridge. -/
structure FullWitnessMemAirSource
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 2 where
  table : Table FGL
  table_mem : table ∈ witness.allTables
  component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
  source : MemTableGeneratedAirSource table

namespace FullWitnessMemAirSource

@[reducible]
def rows
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (source : FullWitnessMemAirSource witness) :
    List (Interaction.MemoryBusEntry FGL) :=
  activeMemReplayRowsOfTable source.table

@[reducible]
def replayBridgeOfTraceSplit
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {entry : Interaction.MemoryBusEntry FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    (source : FullWitnessMemAirSource witness)
    (h_traceSplit : source.rows = priorRows ++ entry :: laterRows) :
    FullWitnessMemReplayBridge witness source.rows :=
  fullWitnessMemReplayBridge_of_memAirSource_traceSplit
    source.table_mem
    source.component
    source.source
    h_traceSplit

end FullWitnessMemAirSource

/-- Build the full-witness Mem AIR source from concrete assertion and lookup
    witnesses for the witness-selected mutable Mem table. -/
def fullWitnessMemAirSource_of_witnessFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_rowRanges :
      MemTableGeneratedRangeLookupFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges :
      MemSegmentGeneratedRangeLookupFacts (segmentWithFixedL1 segment)) :
    FullWitnessMemAirSource witness where
  table := table
  table_mem := h_table
  component := h_component
  source :=
    memTableGeneratedAirSource_of_witnessFacts
      table segment permutation gsum im0 im1
      h_constraints
      h_rowRanges
      h_segmentRanges

/-- Build the full-witness Mem AIR source from raw generated facts for the
    witness-selected mutable Mem table. -/
def fullWitnessMemAirSource_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_raw :
      MemTableGeneratedRawSourceFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation) :
    FullWitnessMemAirSource witness :=
  fullWitnessMemAirSource_of_witnessFacts
    h_table
    h_component
    segment
    permutation
    gsum
    im0
    im1
    (memTableGeneratedConstraintAssertionFacts_of_constraintFacts h_raw.constraints)
    (memTableGeneratedRangeLookupFacts_of_rangeFacts h_raw.rowRanges)
    (memSegmentGeneratedRangeLookupFacts_of_rangeFacts h_raw.segmentRanges)

/-- Generated/full-ensemble Mem AIR source facts for every mutable Mem table in
    one full witness. The table membership and component identity are supplied
    by the full witness; this callback supplies only the source columns and the
    concrete assertion/lookup witnesses. -/
def FullWitnessMemAirSourceFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        Σ segment : ZiskFv.Airs.Mem.SegmentColumns FGL,
        Σ permutation : ZiskFv.Airs.Mem.PermutationColumns FGL,
        Σ gsum : ℕ → FGL,
        Σ im0 : ℕ → FGL,
        Σ im1 : ℕ → FGL,
          MemTableGeneratedConstraintAssertionFacts
            table (memOfTable table gsum im0 im1)
            (segmentWithFixedL1 segment) permutation
          × MemTableGeneratedRangeLookupFacts
            table (memOfTable table gsum im0 im1)
          × MemSegmentGeneratedRangeLookupFacts (segmentWithFixedL1 segment)

/-- Raw generated/full-ensemble Mem AIR source facts for every mutable Mem
    table in one full witness.

    This is the shape a generated Lean module may prove first when it derives
    raw split constraints and raw range facts directly from pilout/PIL source.
    `fullWitnessMemAirSourceFacts_of_rawFacts` packages it into the
    witness-aware callback consumed by `exists_fullWitnessMemAirSource_of_facts`. -/
def FullWitnessMemAirSourceRawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        Σ segment : ZiskFv.Airs.Mem.SegmentColumns FGL,
        Σ permutation : ZiskFv.Airs.Mem.PermutationColumns FGL,
        Σ gsum : ℕ → FGL,
        Σ im0 : ℕ → FGL,
        Σ im1 : ℕ → FGL,
          MemTableGeneratedRawSourceFacts
            table (memOfTable table gsum im0 im1)
            (segmentWithFixedL1 segment) permutation

/-- Generated/full-ensemble raw Mem source sidecars for every mutable Mem table
    in one full witness.

    This is a structured generated-code target for the current sidecar route:
    the full witness supplies table membership and component identity, while the
    sidecar supplies the concrete stage-2 columns and raw split facts for that
    table. -/
def FullWitnessMemAirSourceRawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        MemTableGeneratedRawSourceSidecar table

/-- Generated/full-ensemble raw Mem facts whose source columns are read from
    the shared `witness.data` prover-data map.

    `EnsembleWitness.same_data` already requires every table in the witness to
    share this map. This callback is therefore the concrete generated target
    for the sidecar route: generated code proves raw Mem facts for the named
    ProverData keys, and Lean packages those facts into the stored sidecar
    boundary. -/
def FullWitnessMemAirSourceProverDataFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        MemTableGeneratedRawSourceFacts
          table
          (memOfTable table
            (memSidecarGsumOfProverData witness.data)
            (memSidecarIm0OfProverData witness.data)
            (memSidecarIm1OfProverData witness.data))
          (segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data))
          (memPermutationColumnsOfProverData witness.data)

/-- Generated/full-ensemble Mem assertion and lookup witnesses whose source
    columns are read from the shared `witness.data` prover-data map. -/
def FullWitnessMemAirSourceProverDataWitnessFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        MemTableGeneratedConstraintAssertionFacts
          table
          (memOfTable table
            (memSidecarGsumOfProverData witness.data)
            (memSidecarIm0OfProverData witness.data)
            (memSidecarIm1OfProverData witness.data))
          (segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data))
          (memPermutationColumnsOfProverData witness.data)
        × MemTableGeneratedRangeLookupFacts
          table
          (memOfTable table
            (memSidecarGsumOfProverData witness.data)
            (memSidecarIm0OfProverData witness.data)
            (memSidecarIm1OfProverData witness.data))
        × MemSegmentGeneratedRangeLookupFacts
          (segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data))

/-- Project ProverData-backed Clean assertion/lookup witnesses to raw generated
    Mem source facts. -/
def fullWitnessMemAirSourceProverDataFacts_of_witnessFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness) :
    FullWitnessMemAirSourceProverDataFacts witness := by
  intro table h_table h_component
  rcases h_witnessFacts table h_table h_component with
    ⟨h_constraints, h_rowRanges, h_segmentRanges⟩
  exact
    memTableGeneratedRawSourceFacts_of_witnessFacts
      h_constraints
      h_rowRanges
      h_segmentRanges

/-- Build ProverData-backed Clean assertion/lookup witnesses from raw generated
    Mem facts over the same `witness.data` sidecar columns.

    This is the generated-artifact adapter for modules that prove the raw
    pilout/PIL propositions first: Lean repackages those propositions as the
    assertion and lookup witnesses required by
    `FullWitnessMemAirSourceProverDataWitnessFacts`. -/
def fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_rawFacts : FullWitnessMemAirSourceProverDataFacts witness) :
    FullWitnessMemAirSourceProverDataWitnessFacts witness := by
  intro table h_table h_component
  let h_raw := h_rawFacts table h_table h_component
  exact
    ⟨ memTableGeneratedConstraintAssertionFacts_of_constraintFacts h_raw.constraints,
      memTableGeneratedRangeLookupFacts_of_rangeFacts h_raw.rowRanges,
      memSegmentGeneratedRangeLookupFacts_of_rangeFacts h_raw.segmentRanges ⟩

/-- Package generated raw Mem facts over the named `witness.data` sidecar keys
    into the stored full-witness sidecar callback. -/
def fullWitnessMemAirSourceRawSidecars_of_proverData
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_facts : FullWitnessMemAirSourceProverDataFacts witness) :
    FullWitnessMemAirSourceRawSidecars witness := by
  intro table h_table h_component
  exact
    memTableGeneratedRawSourceSidecar_of_proverData
      table
      witness.data
      (h_facts table h_table h_component)

/-- Package ProverData-backed Clean assertion/lookup witnesses into the stored
    full-witness sidecar callback. -/
def fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness) :
    FullWitnessMemAirSourceRawSidecars witness :=
  fullWitnessMemAirSourceRawSidecars_of_proverData
    (fullWitnessMemAirSourceProverDataFacts_of_witnessFacts h_witnessFacts)

/-- Package generated raw Mem source sidecars into the existing raw full-witness
    callback. -/
def fullWitnessMemAirSourceRawFacts_of_sidecars
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    FullWitnessMemAirSourceRawFacts witness := by
  intro table h_table h_component
  let sidecar := h_sidecars table h_table h_component
  exact
    ⟨ sidecar.segment, sidecar.permutation, sidecar.gsum, sidecar.im0, sidecar.im1,
      sidecar.facts ⟩

/-- Package raw generated/full-ensemble Mem facts into sidecar form.

    This is a compatibility adapter for callers that can still prove the raw
    sigma callback directly. The full-witness timeline boundary stores
    sidecars, so generated artifacts should prefer
    `FullWitnessMemAirSourceRawSidecars` when possible. -/
def fullWitnessMemAirSourceRawSidecars_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    FullWitnessMemAirSourceRawSidecars witness := by
  intro table h_table h_component
  rcases h_raw table h_table h_component with
    ⟨segment, permutation, gsum, im0, im1, h_rawFacts⟩
  exact
    { segment := segment
      permutation := permutation
      gsum := gsum
      im0 := im0
      im1 := im1
      facts := h_rawFacts }

/-- Package raw generated/full-ensemble Mem facts into the witness-aware source
    callback. -/
def fullWitnessMemAirSourceFacts_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    FullWitnessMemAirSourceFacts witness := by
  intro table h_table h_component
  rcases h_raw table h_table h_component with
    ⟨segment, permutation, gsum, im0, im1, h_rawFacts⟩
  exact
    ⟨ segment, permutation, gsum, im0, im1,
      memTableGeneratedConstraintAssertionFacts_of_constraintFacts h_rawFacts.constraints,
      memTableGeneratedRangeLookupFacts_of_rangeFacts h_rawFacts.rowRanges,
      memSegmentGeneratedRangeLookupFacts_of_rangeFacts h_rawFacts.segmentRanges ⟩

/-- Select the concrete mutable Mem table from a full witness and build its
    Mem AIR source from the generated/full-ensemble source facts. -/
theorem exists_fullWitnessMemAirSource_of_facts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_facts : FullWitnessMemAirSourceFacts witness) :
    Nonempty (FullWitnessMemAirSource witness) := by
  rcases exists_mem_table_of_fullRv64im_witness witness with
    ⟨table, h_table, h_component⟩
  rcases h_facts table h_table h_component with
    ⟨segment, permutation, gsum, im0, im1, h_constraints, h_rowRanges, h_segmentRanges⟩
  exact ⟨fullWitnessMemAirSource_of_witnessFacts
    h_table h_component segment permutation gsum im0 im1
    h_constraints h_rowRanges h_segmentRanges⟩

/-- Select the concrete mutable Mem table from a full witness and build its
    Mem AIR source directly from raw generated/full-ensemble source facts. -/
theorem exists_fullWitnessMemAirSource_of_rawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    Nonempty (FullWitnessMemAirSource witness) :=
  exists_fullWitnessMemAirSource_of_facts
    witness
    (fullWitnessMemAirSourceFacts_of_rawFacts h_raw)

/-- Select the concrete mutable Mem table from sidecar-form raw source facts. -/
theorem exists_fullWitnessMemAirSource_of_rawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    Nonempty (FullWitnessMemAirSource witness) :=
  exists_fullWitnessMemAirSource_of_rawFacts
    witness
    (fullWitnessMemAirSourceRawFacts_of_sidecars h_sidecars)

/-- A named Mem AIR source selected from raw full-witness facts.

    This is only a choice of the concrete mutable Mem table already proved to
    exist in the full witness. Residual timeline facts that use this source
    should refer to this name so the selection is explicit. -/
noncomputable def fullWitnessMemAirSourceOfRawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    FullWitnessMemAirSource witness :=
  Classical.choice (exists_fullWitnessMemAirSource_of_rawFacts witness h_raw)

/-- A named Mem AIR source selected from sidecar-form raw full-witness facts. -/
noncomputable def fullWitnessMemAirSourceOfRawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    FullWitnessMemAirSource witness :=
  Classical.choice (exists_fullWitnessMemAirSource_of_rawSidecars witness h_sidecars)

/-- The sidecar-selected source is exactly the raw-facts selected source after
    applying the sidecar-to-raw adapter. -/
@[simp]
theorem fullWitnessMemAirSourceOfRawSidecars_eq_rawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    fullWitnessMemAirSourceOfRawSidecars witness h_sidecars =
      fullWitnessMemAirSourceOfRawFacts witness
        (fullWitnessMemAirSourceRawFacts_of_sidecars h_sidecars) := by
  rfl

/-- The compact full-witness replay bridge includes the older generated-row
    bridge obligation. -/
theorem fullWitnessMemTableGeneratedRowsBridge_of_fullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_bridge : FullWitnessMemReplayBridge witness rows) :
    FullWitnessMemTableGeneratedRowsBridge witness
      h_bridge.mem h_bridge.segment h_bridge.permutation h_bridge.rowCount :=
  ⟨h_bridge.table, h_bridge.table_mem, h_bridge.generatedRows⟩

/-- The full-witness bridge projects the generated row range required by the
    Mem trace spec. -/
theorem generatedMemRows_of_fullWitnessMemTableGeneratedRowsBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge :
      FullWitnessMemTableGeneratedRowsBridge
        witness mem segment permutation rowCount) :
    ZiskFv.AirsClean.Mem.GeneratedMemRows mem segment permutation rowCount := by
  rcases h_bridge with ⟨table, _h_table, h_table_bridge⟩
  exact generatedMemRows_of_memTableGeneratedRowsBridge h_table_bridge

/-- Project the generated Mem row fact at one concrete Clean table position. -/
theorem generated_every_row_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val :=
  h_bridge.generatedAt idx

/-- Project the local Clean bridge constraints at one concrete table
    position, via the generated Mem row surface. -/
theorem constraints_at_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.constraints_at mem idx.val :=
  ZiskFv.AirsClean.Mem.constraints_at_of_generated_every_row
    mem segment permutation idx.val (h_bridge.generatedAt idx)

/-- The indexed table bridge projects the Clean Mem row `Spec` at one
    `Valid_Mem` row. -/
theorem rowAt_spec_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.Spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) := by
  have h_constraints :=
    constraints_at_of_memTableGeneratedRowsBridge h_bridge idx
  simpa [ZiskFv.AirsClean.Mem.Spec, ZiskFv.AirsClean.Mem.constraints_at,
    ZiskFv.AirsClean.Mem.rowAt] using h_constraints

/-- The indexed table bridge projects the Clean Mem row `Spec` for the
    concrete evaluated table row at a list position. -/
theorem tableRow_spec_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.Spec
      (eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rw [h_bridge.rowAt_eq idx]
  exact h_spec

/-- The indexed table bridge supplies generated row specs for every concrete
    table row, in the membership form consumed by table-level `flatMap`
    inductions. -/
theorem tableRow_specs_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount) :
    ∀ providerRow, providerRow ∈ table.table →
      ZiskFv.AirsClean.Mem.Spec
        (eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
  intro providerRow h_mem
  rcases List.mem_iff_get.mp h_mem with ⟨idx, h_get⟩
  rw [← h_get]
  exact tableRow_spec_of_memTableGeneratedRowsBridge h_bridge idx

/-- A bridged generated Mem table position has a boolean current-row write
    flag at the Nat-value level. -/
theorem wr_val_lt_two_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    (mem.wr idx.val).val < 2 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_wr_zero | h_wr_one
  · have h_wr_zero_mem : mem.wr idx.val = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero
    rw [h_wr_zero_mem]
    norm_num
  · have h_wr_one_mem : mem.wr idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_one
    rw [h_wr_one_mem]
    norm_num

/-- A generated Mem table row with inactive primary selector cannot be a
    primary write, because `mem.pil` has the `wr * (1 - sel) = 0` constraint. -/
theorem wr_eq_zero_of_sel_zero_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_sel_zero : mem.sel idx.val = 0) :
    mem.wr idx.val = 0 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_wr_zero | h_wr_one
  · simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero
  · have h_sel_one :=
      ZiskFv.AirsClean.Mem.sel_of_wr_one_of_spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec h_wr_one
    have h_sel_one_mem : mem.sel idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_sel_one
    rw [h_sel_zero] at h_sel_one_mem
    norm_num at h_sel_one_mem

/-- The indexed table bridge lifts the generated non-boundary same-address
    address-carry constraint to a concrete Mem table position. -/
theorem addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.addr idx.val = mem.addr (idx.val - 1) := by
  exact
    ZiskFv.Airs.Mem.addr_eq_previous_of_same_addr_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary

/-- On a bridged concrete Mem table row, the Clean row-spec identity
    `read_same_addr = (1 - addr_changes) * (1 - wr)` turns a read at the same
    address into the generated `read_same_addr = 1` witness. -/
theorem read_same_addr_eq_one_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0) :
    mem.read_same_addr idx.val = 1 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_read_same_addr :=
    ZiskFv.AirsClean.Mem.read_same_addr_eq_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
  simpa [ZiskFv.AirsClean.Mem.rowAt, h_same_addr, h_read] using h_read_same_addr

/-- The indexed table bridge lifts the generated non-boundary same-address read
    value-carry constraints to a concrete Mem table position. -/
theorem values_eq_previous_of_read_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_read_same_addr : mem.read_same_addr idx.val = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.value_0 idx.val = mem.value_0 (idx.val - 1)
      ∧ mem.value_1 idx.val = mem.value_1 (idx.val - 1) := by
  exact
    ZiskFv.Airs.Mem.values_eq_previous_of_read_same_addr_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_read_same_addr h_not_boundary

/-- Same-address reads at non-boundary bridged Mem table rows carry both value
    chunks from the previous row. This is the table-level form needed by the
    per-address prefix-read proof. -/
theorem values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.value_0 idx.val = mem.value_0 (idx.val - 1)
      ∧ mem.value_1 idx.val = mem.value_1 (idx.val - 1) := by
  exact values_eq_previous_of_read_same_addr_memTableGeneratedRowsBridge
    h_bridge idx
    (read_same_addr_eq_one_of_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read)
    h_not_boundary

/-- A bridged non-boundary same-address read is byte-for-byte justified by
    replaying the previous primary row when that previous row is a write.

    This is the adjacent write→read replay step behind the per-address
    `MemoryBusRowsPrefixReadSound` induction. -/
theorem readEventReplayAgreement_after_previous_primary_write_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_write : mem.wr (idx.val - 1) = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_addr :=
    addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_not_boundary
  have h_values :=
    values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read h_not_boundary
  let writeEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    dsimp [readEntry, writeEntry]
    simp [h_addr]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry initialMemory writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      initialMemory h_ptr h_value_0 h_value_1
  simpa [writeEntry, readEntry, ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
    ZiskFv.AirsClean.Mem.rowAt, h_previous_write,
    ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent_storeEventOfEntry] using h_replay

/-- A bridged non-boundary same-address read is byte-for-byte justified by a
    previous primary read that was already replay-sound, because the previous
    read leaves replay memory unchanged and the generated value-carry
    constraints identify the current read's bytes with the previous row. -/
theorem readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_read : mem.wr (idx.val - 1) = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_agreement :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_addr :=
    addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_not_boundary
  have h_values :=
    values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read h_not_boundary
  let sourceEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))
  let targetEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_ptr : targetEntry.ptr = sourceEntry.ptr := by
    dsimp [targetEntry, sourceEntry]
    simp [h_addr]
  have h_value_0 : targetEntry.value_0 = sourceEntry.value_0 := by
    dsimp [targetEntry, sourceEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : targetEntry.value_1 = sourceEntry.value_1 := by
    dsimp [targetEntry, sourceEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_carried :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry targetEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_entry_same
      (by simpa [sourceEntry] using h_previous_agreement)
      h_ptr h_value_0 h_value_1
  have h_source_as : sourceEntry.as = (2 : FGL) := by
    simp [sourceEntry]
  have h_source_read : sourceEntry.multiplicity = (-1 : FGL) := by
    simp [sourceEntry, h_previous_read]
  have h_source_replay :=
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
      initialMemory sourceEntry h_source_as h_source_read
  rw [h_source_replay]
  simpa [targetEntry]

/-- A selected previous Mem row justifies a non-boundary same-address current
    read after replaying that previous row's active chunk.

    If the previous primary emission was a write, the write sets the bytes
    carried by the current read. If it was a read, the caller supplies the
    previous read agreement. A selected previous dual emission is replay-neutral
    because dual Mem emissions are pinned reads. -/
theorem readEventReplayAgreement_after_previous_selected_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_sel : mem.sel (idx.val - 1) = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
        (activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  let previousRow := ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1)
  let previousPrimaryEntry := memPrimaryReplayEntryOfRow previousRow
  let previousDualEntry := memDualReadReplayEntryOfRow previousRow
  have h_previous_spec :
      ZiskFv.AirsClean.Mem.Spec previousRow := by
    simpa [previousRow, previousIdx] using
      rowAt_spec_of_memTableGeneratedRowsBridge h_bridge previousIdx
  have h_previous_sel_row : previousRow.sel = 1 := by
    simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_sel
  have h_after_primary :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
          previousPrimaryEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
    rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec previousRow h_previous_spec with
      h_previous_wr_zero_row | h_previous_wr_one_row
    · have h_previous_wr_zero : mem.wr (idx.val - 1) = 0 := by
        simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_wr_zero_row
      simpa [previousPrimaryEntry, previousRow] using
        readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge
          initialMemory h_bridge idx h_same_addr h_read h_previous_wr_zero
          h_not_boundary (h_previous_read_agreement h_previous_wr_zero)
    · have h_previous_wr_one : mem.wr (idx.val - 1) = 1 := by
        simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_wr_one_row
      simpa [previousPrimaryEntry, previousRow] using
        readEventReplayAgreement_after_previous_primary_write_memTableGeneratedRowsBridge
          initialMemory h_bridge idx h_same_addr h_read h_previous_wr_one
          h_not_boundary
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec previousRow h_previous_spec with
    h_previous_sel_dual_zero | h_previous_sel_dual_one
  · have h_previous_sel_dual_ne : previousRow.sel_dual ≠ 1 := by
      simp [h_previous_sel_dual_zero]
    rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
      h_previous_sel_row h_previous_sel_dual_ne]
    simpa [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows,
      previousPrimaryEntry, previousRow] using h_after_primary
  · rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
      h_previous_sel_row h_previous_sel_dual_one]
    have h_dual_as : previousDualEntry.as = (2 : FGL) := by
      simp [previousDualEntry]
    have h_dual_read : previousDualEntry.multiplicity = (-1 : FGL) := by
      simp [previousDualEntry]
    have h_dual_replay :=
      ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
          previousPrimaryEntry)
        previousDualEntry h_dual_as h_dual_read
    rw [show
      ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
          [previousPrimaryEntry, previousDualEntry] =
        ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
            previousPrimaryEntry)
          previousDualEntry by
        rfl]
    rw [h_dual_replay]
    simpa [previousPrimaryEntry, previousRow] using h_after_primary

/-- An inactive previous Mem row carries a non-boundary same-address current
    read without changing the replay memory.

    The generated row spec forces an inactive row to have no active primary or
    dual replay emissions; if its primary polarity is read, the existing
    previous-primary-read carry lemma transports the supplied previous-row
    agreement to the current row. -/
theorem readEventReplayAgreement_after_previous_inactive_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_inactive : mem.sel (idx.val - 1) = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_agreement :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
        (activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  let previousRow := ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1)
  let previousPrimaryEntry := memPrimaryReplayEntryOfRow previousRow
  have h_previous_spec :
      ZiskFv.AirsClean.Mem.Spec previousRow := by
    simpa [previousRow, previousIdx] using
      rowAt_spec_of_memTableGeneratedRowsBridge h_bridge previousIdx
  have h_previous_sel_zero_row : previousRow.sel = 0 := by
    simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_inactive
  have h_previous_wr_zero : mem.wr (idx.val - 1) = 0 := by
    rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec previousRow h_previous_spec with
      h_wr_zero_row | h_wr_one_row
    · simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero_row
    · have h_sel_one :=
        ZiskFv.AirsClean.Mem.sel_of_wr_one_of_spec
          previousRow h_previous_spec h_wr_one_row
      rw [h_previous_sel_zero_row] at h_sel_one
      norm_num at h_sel_one
  have h_current_after_previous_primary :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
          previousPrimaryEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
    simpa [previousPrimaryEntry, previousRow] using
      readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge
        initialMemory h_bridge idx h_same_addr h_read h_previous_wr_zero
        h_not_boundary h_previous_agreement
  have h_previous_primary_as : previousPrimaryEntry.as = (2 : FGL) := by
    simp [previousPrimaryEntry]
  have h_previous_primary_read :
      previousPrimaryEntry.multiplicity = (-1 : FGL) := by
    simp [previousPrimaryEntry, previousRow, h_previous_wr_zero]
  have h_previous_primary_replay :=
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
      initialMemory previousPrimaryEntry h_previous_primary_as
      h_previous_primary_read
  rw [h_previous_primary_replay] at h_current_after_previous_primary
  have h_previous_sel_ne : previousRow.sel ≠ 1 := by
    simp [h_previous_sel_zero_row]
  have h_previous_sel_dual_ne : previousRow.sel_dual ≠ 1 := by
    intro h_sel_dual_one
    have h_sel_one :=
      ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec
        previousRow h_previous_spec h_sel_dual_one
    rw [h_previous_sel_zero_row] at h_sel_one
    norm_num at h_sel_one
  rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
    h_previous_sel_ne h_previous_sel_dual_ne]
  simpa [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows] using
    h_current_after_previous_primary

/-- One-step same-address carry across the previous table row.

    This packages the selected and inactive predecessor cases. If the previous
    row's primary event is a read, the caller supplies its replay agreement;
    if it is a write, the selected-row lemma uses the write update directly. -/
theorem readEventReplayAgreement_after_previous_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
        (activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  let previousRow := ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1)
  have h_previous_spec :
      ZiskFv.AirsClean.Mem.Spec previousRow := by
    simpa [previousRow, previousIdx] using
      rowAt_spec_of_memTableGeneratedRowsBridge h_bridge previousIdx
  rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec previousRow h_previous_spec with
    h_previous_sel_zero_row | h_previous_sel_one_row
  · have h_previous_sel_zero : mem.sel (idx.val - 1) = 0 := by
      simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_sel_zero_row
    have h_previous_wr_zero : mem.wr (idx.val - 1) = 0 :=
      wr_eq_zero_of_sel_zero_memTableGeneratedRowsBridge
        h_bridge previousIdx (by simpa [previousIdx] using h_previous_sel_zero)
    exact
      readEventReplayAgreement_after_previous_inactive_row_memTableGeneratedRowsBridge
        initialMemory h_bridge idx h_idx_pos h_same_addr h_read
        h_previous_sel_zero h_not_boundary
        (h_previous_read_agreement h_previous_wr_zero)
  · have h_previous_sel_one : mem.sel (idx.val - 1) = 1 := by
      simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_sel_one_row
    exact
      readEventReplayAgreement_after_previous_selected_row_memTableGeneratedRowsBridge
        initialMemory h_bridge idx h_idx_pos h_same_addr h_read
        h_previous_sel_one h_not_boundary h_previous_read_agreement

/-- Split-shaped same-address predecessor step for table prefixes over an
    arbitrary initial memory.

If the current provider row is immediately after `previousProviderRow` in the
concrete table split, the one-step predecessor lemma composes with the replay
append law to justify the current read against the whole split prefix
`priorPrefix ++ [previousProviderRow]`. -/
theorem readEventReplayAgreement_after_initialMemory_splitPrefix_previous_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (priorPrefix : List (Array FGL))
    (previousProviderRow providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split :
      table.table = priorPrefix ++ previousProviderRow :: providerRow :: laterRows)
    (h_idx_val : idx.val = priorPrefix.length + 1)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
            initialMemory
            (priorPrefix.flatMap fun priorProviderRow =>
              activeMemReplayEntriesOfRow
                (eval (table.environment priorProviderRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        initialMemory
        ((priorPrefix ++ [previousProviderRow]).flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_idx_pos : 0 < idx.val := by omega
  have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  have h_previous_get : table.table.get previousIdx = previousProviderRow := by
    have h_previous_val : previousIdx.val = priorPrefix.length := by
      simp [previousIdx]
      omega
    have h_previous_get?_prior :
        table.table[priorPrefix.length]? = some previousProviderRow := by
      have h_lookup :=
        congrArg (fun rows : List (Array FGL) => rows[priorPrefix.length]?)
          h_split
      have h_lookup' :
          table.table[priorPrefix.length]? =
            (priorPrefix ++ previousProviderRow :: providerRow :: laterRows)[priorPrefix.length]? := by
        simpa using h_lookup
      rw [h_lookup']
      simp
    have h_previous_get? :
        table.table[previousIdx.val]? = some previousProviderRow := by
      rw [h_previous_val]
      exact h_previous_get?_prior
    have h_get_current :
        table.table[previousIdx.val]? = some (table.table.get previousIdx) := by
      exact List.getElem?_eq_getElem previousIdx.isLt
    rw [h_get_current] at h_previous_get?
    exact Option.some.inj h_previous_get?
  have h_previous_rowAt :
      eval (table.environment previousProviderRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1) := by
    rw [← h_previous_get]
    simpa [previousIdx] using h_bridge.rowAt_eq previousIdx
  have h_step :=
    readEventReplayAgreement_after_previous_row_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        initialMemory
        (priorPrefix.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      h_bridge idx h_idx_pos h_same_addr h_read h_not_boundary
      h_previous_read_agreement
  simpa [List.flatMap_append, h_previous_rowAt,
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows_append] using h_step

/-- Split-shaped same-address predecessor step specialized to the finite
    zero-preloaded Mem-table memory. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_previous_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (priorPrefix : List (Array FGL))
    (previousProviderRow providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split :
      table.table = priorPrefix ++ previousProviderRow :: providerRow :: laterRows)
    (h_idx_val : idx.val = priorPrefix.length + 1)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
            (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
              (activeMemReplayRowsOfTable table))
            (priorPrefix.flatMap fun priorProviderRow =>
              activeMemReplayEntriesOfRow
                (eval (table.environment priorProviderRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        ((priorPrefix ++ [previousProviderRow]).flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  exact
    readEventReplayAgreement_after_initialMemory_splitPrefix_previous_row_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
      h_bridge h_fixed idx priorPrefix previousProviderRow providerRow laterRows
      h_split h_idx_val h_same_addr h_read h_previous_read_agreement

/-- Replaying a primary write from one Mem row justifies the pinned dual read
    emitted by the same row, because the dual message has the same pointer and
    value chunks and appears after the primary emission. -/
theorem readEventReplayAgreement_after_primary_write_dual_read_of_row
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (row : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_write : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memDualReadReplayEntryOfRow row)) := by
  let writeEntry := memPrimaryReplayEntryOfRow row
  let readEntry := memDualReadReplayEntryOfRow row
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    simp [readEntry, writeEntry]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    simp [readEntry, writeEntry]
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    simp [readEntry, writeEntry]
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry initialMemory writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      initialMemory h_ptr h_value_0 h_value_1
  simpa [writeEntry, readEntry, ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage, h_write,
    ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent_storeEventOfEntry] using h_replay

/-- A replay-sound primary read justifies the pinned dual read emitted by the
    same Mem row when the primary event is also a read. The primary read leaves
    replay memory unchanged, and the dual message carries the same pointer and
    value chunks. -/
theorem readEventReplayAgreement_after_primary_read_dual_read_of_row
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (row : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_read : row.wr = 0)
    (h_primary_agreement :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow row))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memDualReadReplayEntryOfRow row)) := by
  let sourceEntry := memPrimaryReplayEntryOfRow row
  let targetEntry := memDualReadReplayEntryOfRow row
  have h_ptr : targetEntry.ptr = sourceEntry.ptr := by
    simp [targetEntry, sourceEntry]
  have h_value_0 : targetEntry.value_0 = sourceEntry.value_0 := by
    simp [targetEntry, sourceEntry]
  have h_value_1 : targetEntry.value_1 = sourceEntry.value_1 := by
    simp [targetEntry, sourceEntry]
  have h_carried :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry targetEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_entry_same
      (by simpa [sourceEntry] using h_primary_agreement)
      h_ptr h_value_0 h_value_1
  have h_source_as : sourceEntry.as = (2 : FGL) := by
    simp [sourceEntry]
  have h_source_read : sourceEntry.multiplicity = (-1 : FGL) := by
    simp [sourceEntry, h_read]
  have h_source_replay :=
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
      initialMemory sourceEntry h_source_as h_source_read
  rw [h_source_replay]
  simpa [targetEntry]

/-- An address-change primary read is locally justified by the finite
    zero-preload memory at its pointer. The generated row spec forces both
    value chunks to zero when `addr_changes = 1` and `wr = 0`. -/
theorem readEventReplayAgreement_after_zeroMemoryOfEntry_primary_read_of_addr_change
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_addr_change : row.addr_changes = 1)
    (h_read : row.wr = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfEntry initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow row)) := by
  have h_value_0 :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_0_zero_of_spec
      row h_spec h_addr_change h_read
  have h_value_1 :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_1_zero_of_spec
      row h_spec h_addr_change h_read
  exact
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_zeroMemoryOfEntry
      initialMemory
      (by
        simpa [memPrimaryReplayEntryOfRow,
          ZiskFv.AirsClean.Mem.memBusMessage] using h_value_0)
      (by
        simpa [memPrimaryReplayEntryOfRow,
          ZiskFv.AirsClean.Mem.memBusMessage] using h_value_1)

/-- The indexed table bridge projects the address-change zero-read
    justification to a concrete Mem table row. -/
theorem readEventReplayAgreement_after_zeroMemoryOfEntry_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfEntry initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  exact
    readEventReplayAgreement_after_zeroMemoryOfEntry_primary_read_of_addr_change
      initialMemory h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)

/-- A selected address-change primary read is justified by the finite
    zero-preload memory built from all active Mem table replay rows.

    This is the table-shaped zero-preload fact. It does not yet replay the
    selected row's prior prefix; that follow-on step additionally needs the
    prior-prefix rows to be byte-disjoint from the selected read. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_value_0_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_0_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_1_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_1_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_0 : readEntry.value_0 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_0_row
  have h_value_1 : readEntry.value_1 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_1_row
  have h_row_mem : table.table.get idx ∈ table.table := by
    exact List.mem_iff_get.mpr ⟨idx, rfl⟩
  have h_readEntry_mem : readEntry ∈ activeMemReplayRowsOfTable table := by
    unfold activeMemReplayRowsOfTable
    exact List.mem_flatMap.mpr
      ⟨table.table.get idx, h_row_mem, by
        rw [h_bridge.rowAt_eq idx]
        simp [activeMemReplayEntriesOfRow, readEntry,
          ZiskFv.AirsClean.Mem.rowAt, h_sel]⟩
  have h_same_or_disjoint :
      ∀ entry, entry ∈ activeMemReplayRowsOfTable table →
        entry.ptr = readEntry.ptr
          ∨ ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint readEntry entry := by
    intro entry h_entry
    unfold activeMemReplayRowsOfTable at h_entry
    rcases List.mem_flatMap.mp h_entry with
      ⟨providerRow, h_provider_mem, h_entry_row⟩
    rcases List.mem_iff_get.mp h_provider_mem with ⟨otherIdx, h_get⟩
    have h_entry_rowAt :
        entry ∈ activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
      rw [← h_get] at h_entry_row
      rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
      exact h_entry_row
    simpa [readEntry] using
      activeMemReplayEntry_same_ptr_or_byteDisjoint_of_rowAt
        h_ranges idx otherIdx h_entry_rowAt
  simpa [readEntry] using
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_zeroMemoryOfRows_mem
      h_value_0 h_value_1 h_readEntry_mem h_same_or_disjoint

/-- A read row whose address changes is justified by the whole-table
zero-preload memory when any selected row at the same Mem address contributes a
primary active replay entry.

This same-pointer preload form is needed for inactive same-address predecessor
rows: they may not themselves appear in `activeMemReplayRowsOfTable`, but the
eventual selected row at the same pointer does. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx preloadIdx : Fin table.table.length)
    (h_preload_sel : mem.sel preloadIdx.val = 1)
    (h_addr_eq : mem.addr idx.val = mem.addr preloadIdx.val)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  let preloadEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem preloadIdx.val)
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_value_0_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_0_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_1_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_1_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_0 : readEntry.value_0 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_0_row
  have h_value_1 : readEntry.value_1 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_1_row
  have h_preload_mem : preloadEntry ∈ activeMemReplayRowsOfTable table := by
    have h_row_mem : table.table.get preloadIdx ∈ table.table := by
      exact List.mem_iff_get.mpr ⟨preloadIdx, rfl⟩
    unfold activeMemReplayRowsOfTable
    exact List.mem_flatMap.mpr
      ⟨table.table.get preloadIdx, h_row_mem, by
        rw [h_bridge.rowAt_eq preloadIdx]
        simp [activeMemReplayEntriesOfRow, preloadEntry,
          ZiskFv.AirsClean.Mem.rowAt, h_preload_sel]⟩
  have h_ptr : preloadEntry.ptr = readEntry.ptr := by
    simp [preloadEntry, readEntry, h_addr_eq.symm]
  have h_same_or_disjoint :
      ∀ entry, entry ∈ activeMemReplayRowsOfTable table →
        entry.ptr = readEntry.ptr
          ∨ ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint readEntry entry := by
    intro entry h_entry
    unfold activeMemReplayRowsOfTable at h_entry
    rcases List.mem_flatMap.mp h_entry with
      ⟨providerRow, h_provider_mem, h_entry_row⟩
    rcases List.mem_iff_get.mp h_provider_mem with ⟨otherIdx, h_get⟩
    have h_entry_rowAt :
        entry ∈ activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
      rw [← h_get] at h_entry_row
      rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
      exact h_entry_row
    simpa [readEntry] using
      activeMemReplayEntry_same_ptr_or_byteDisjoint_of_rowAt
        h_ranges idx otherIdx h_entry_rowAt
  simpa [readEntry, preloadEntry] using
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_zeroMemoryOfRows_same_ptr_mem
      h_value_0 h_value_1 h_preload_mem h_ptr h_same_or_disjoint

/-- The table-shaped zero-preload fact lifts through any prior active replay
    prefix whose rows are byte-disjoint from the selected address-change read.

    The remaining AIR-ordering work is to prove the `h_prior_disjoint`
    premise for the concrete prefix of an address-sorted Mem table. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_disjoint_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_prior_disjoint :
      ∀ entry,
        entry ∈
            (priorRows.flatMap fun priorProviderRow =>
              activeMemReplayEntriesOfRow
                (eval (table.environment priorProviderRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) →
          ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem idx.val))
            entry) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_zero :=
    readEventReplayAgreement_after_zeroMemoryOfRows_memTableGeneratedRowsBridge
      h_bridge h_ranges idx h_sel h_addr_change h_read
  exact
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
      h_zero h_prior_disjoint

/-- If a table list is split as `priorRows ++ providerRow :: laterRows`, every
    member of `priorRows` has an occurrence at an index before the split point. -/
theorem priorRows_mem_index_lt_of_split
    {α : Type}
    {xs priorRows laterRows : List α}
    {providerRow priorProviderRow : α}
    (h_split : xs = priorRows ++ providerRow :: laterRows)
    (h_prior_mem : priorProviderRow ∈ priorRows) :
    ∃ idx : Fin xs.length,
      xs.get idx = priorProviderRow ∧ idx.val < priorRows.length := by
  subst xs
  rcases List.mem_iff_get.mp h_prior_mem with ⟨priorIdx, h_get_prior⟩
  have h_idx_lt : priorIdx.val < (priorRows ++ providerRow :: laterRows).length := by
    simp [List.length_append]
    omega
  let idx : Fin (priorRows ++ providerRow :: laterRows).length :=
    ⟨priorIdx.val, h_idx_lt⟩
  refine ⟨idx, ?_, ?_⟩
  · simpa [idx] using h_get_prior
  · exact priorIdx.isLt

/-- In a split `xs = priorRows ++ providerRow :: laterRows`, the element at the
split index is `providerRow`. The proof uses `getElem?` to avoid dependent
rewrites through the `Fin` proof term. -/
theorem providerRow_get_eq_of_split
    {α : Type}
    {xs priorRows laterRows : List α}
    {providerRow : α}
    (idx : Fin xs.length)
    (h_split : xs = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length) :
    xs.get idx = providerRow := by
  have h_get_prior : xs[priorRows.length]? = some providerRow := by
    have h_lookup :=
      congrArg (fun rows : List α => rows[priorRows.length]?) h_split
    have h_lookup' :
        xs[priorRows.length]? =
          (priorRows ++ providerRow :: laterRows)[priorRows.length]? := by
      simpa using h_lookup
    rw [h_lookup']
    simp
  have h_get_idx : xs[idx.val]? = some providerRow := by
    rw [h_idx_val]
    exact h_get_prior
  have h_get_current : xs[idx.val]? = some (xs.get idx) := by
    exact List.getElem?_eq_getElem idx.isLt
  rw [h_get_current] at h_get_idx
  exact Option.some.inj h_get_idx

/-- The zero-preload prior-prefix lift only needs the concrete AIR ordering
    proof to rule out equal Mem addresses in the prior prefix.

    This theorem turns that address-separation statement into the byte-range
    disjointness required by the replay core. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_addr_ne_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_prior_addr_ne :
      ∀ priorProviderRow, priorProviderRow ∈ priorRows →
        ∃ otherIdx : Fin table.table.length,
          table.table.get otherIdx = priorProviderRow ∧
            mem.addr otherIdx.val ≠ mem.addr idx.val) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  apply
    readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_disjoint_memTableGeneratedRowsBridge
      h_bridge h_ranges idx priorRows h_sel h_addr_change h_read
  intro entry h_entry
  rcases List.mem_flatMap.mp h_entry with
    ⟨priorProviderRow, h_prior_mem, h_entry_row⟩
  rcases h_prior_addr_ne priorProviderRow h_prior_mem with
    ⟨otherIdx, h_get, h_addr_ne_mem⟩
  have h_entry_rowAt :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
    rw [← h_get] at h_entry_row
    rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
    exact h_entry_row
  have h_selected_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_other_range :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
  have h_addr_ne :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
    intro h_addr_eq
    exact h_addr_ne_mem (by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq.symm)
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry_rowAt with
    h_entry_primary | h_entry_dual
  · simpa [h_entry_primary] using
      memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
        h_selected_range h_other_range h_addr_ne
  · simpa [h_entry_dual] using
      memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
        h_selected_range h_other_range h_addr_ne

/-- A split-shaped version of the address-separation zero-preload lift.

    The remaining semantic input is the indexed all-prior address inequality;
    list-prefix bookkeeping is discharged here from the concrete split. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_ne_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_prior_addr_ne :
      ∀ otherIdx : Fin table.table.length,
        otherIdx.val < idx.val → mem.addr otherIdx.val ≠ mem.addr idx.val) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  exact
    readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_addr_ne_memTableGeneratedRowsBridge
      h_bridge h_ranges idx priorRows h_sel h_addr_change h_read
      (fun priorProviderRow h_prior_mem => by
        rcases priorRows_mem_index_lt_of_split
            (xs := table.table) (priorRows := priorRows)
            (laterRows := laterRows) (providerRow := providerRow)
            h_split h_prior_mem with
          ⟨otherIdx, h_get, h_other_lt_prior_length⟩
        refine ⟨otherIdx, h_get, h_prior_addr_ne otherIdx ?_⟩
        omega)

/-- A generated Mem row's active replay chunk is recursively read/write-sound
    once any selected primary read has already been justified against the
    incoming replay memory.

    The same-row dual read is then discharged from the primary event: writes
    use the row-local write→read replay theorem, and reads use read-no-mutation
    plus equal pointer/value transport. -/
theorem memoryBusRowsReadWriteSound_activeMemReplayEntriesOfRow_of_spec
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_primary_read :
      row.sel = 1 →
      row.wr = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow row))) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory (activeMemReplayEntriesOfRow row) := by
  have h_primary_write_not_read :
      row.wr = 1 →
        ¬(memPrimaryReplayEntryOfRow row).multiplicity = (-1 : FGL) := by
    intro h_wr_one h_mult
    have h_mult_one :
        (memPrimaryReplayEntryOfRow row).multiplicity = (1 : FGL) := by
      simp [h_wr_one]
    have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
      decide
    exact h_one_ne_neg_one (h_mult_one.symm.trans h_mult)
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec row h_spec with
    h_sel_dual_zero | h_sel_dual_one
  · rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec row h_spec with
      h_sel_zero | h_sel_one
    · have h_sel_ne : row.sel ≠ 1 := by
        simp [h_sel_zero]
      have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
        h_sel_ne h_sel_dual_ne]
      simp [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
    · have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
        h_sel_one h_sel_dual_ne]
      simp only [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
      constructor
      · intro _h_as h_mult
        rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec row h_spec with
          h_wr_zero | h_wr_one
        · exact h_primary_read h_sel_one h_wr_zero
        · exact False.elim (h_primary_write_not_read h_wr_one h_mult)
      · simp
  · have h_sel_one :=
      ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec
        row h_spec h_sel_dual_one
    rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
      h_sel_one h_sel_dual_one]
    simp only [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
    constructor
    · intro _h_as h_mult
      rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec row h_spec with
        h_wr_zero | h_wr_one
      · exact h_primary_read h_sel_one h_wr_zero
      · exact False.elim (h_primary_write_not_read h_wr_one h_mult)
    · rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec row h_spec with
        h_wr_zero | h_wr_one
      · constructor
        · intro _h_as _h_mult
          exact
            readEventReplayAgreement_after_primary_read_dual_read_of_row
              initialMemory row h_wr_zero
              (h_primary_read h_sel_one h_wr_zero)
        · simp
      · constructor
        · intro _h_as _h_mult
          exact
            readEventReplayAgreement_after_primary_write_dual_read_of_row
              initialMemory row h_wr_one
        · simp

/-- The remaining semantic input required by the active table replay fold:
    every selected primary read agrees with the memory obtained by replaying
    the preceding active table rows. -/
def ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ∀ priorRows providerRow laterRows,
    table.table = priorRows ++ providerRow :: laterRows →
    (eval (table.environment providerRow)
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1 →
    (eval (table.environment providerRow)
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0 →
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
          (priorRows.flatMap fun priorProviderRow =>
            activeMemReplayEntriesOfRow
              (eval (table.environment priorProviderRow)
                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (eval (table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))

/-- Row-local active replay soundness composes over a list of generated Mem
    rows. The only semantic input still required at each row is the replay
    agreement for a selected primary read at the memory obtained from the
    preceding active rows. -/
theorem memoryBusRowsReadWriteSound_flatMap_activeMemReplayEntriesOfRow
    {α : Type}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (items : List α)
    (rowOf : α → ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_specs :
      ∀ item, item ∈ items → ZiskFv.AirsClean.Mem.Spec (rowOf item))
    (h_primary_read :
      ∀ priorItems item laterItems,
        items = priorItems ++ item :: laterItems →
        (rowOf item).sel = 1 →
        (rowOf item).wr = 0 →
          ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
            (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
              (priorItems.flatMap fun priorItem =>
                activeMemReplayEntriesOfRow (rowOf priorItem)))
            (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
              (memPrimaryReplayEntryOfRow (rowOf item)))) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory
      (items.flatMap fun item => activeMemReplayEntriesOfRow (rowOf item)) := by
  induction items generalizing initialMemory with
  | nil =>
      simp [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
  | cons item rest ih =>
      simp only [List.flatMap_cons]
      apply ZiskFv.ZiskCircuit.MemTrace.memoryBusRowsReadWriteSound_append
      · exact
          memoryBusRowsReadWriteSound_activeMemReplayEntriesOfRow_of_spec
            initialMemory
            (h_specs item (by simp))
            (fun h_sel h_wr =>
              h_primary_read [] item rest (by simp) h_sel h_wr)
      · exact
          ih
            (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
              (activeMemReplayEntriesOfRow (rowOf item)))
            (fun restItem h_restItem =>
              h_specs restItem (by simp [h_restItem]))
            (fun priorItems restItem laterItems h_split h_sel h_wr => by
              have h_split_full :
                  item :: rest = (item :: priorItems) ++ restItem :: laterItems := by
                simp [h_split]
              have h_agreement :=
                h_primary_read (item :: priorItems) restItem laterItems
                  h_split_full h_sel h_wr
              simpa [List.flatMap_cons,
                ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows_append]
                using h_agreement)

/-- Table-level wrapper for the active replay-row fold. It packages the
    mechanical `flatMap` induction while keeping the selected-primary-read
    prefix obligation explicit. -/
theorem memoryBusRowsReadWriteSound_activeMemReplayRowsOfTable_of_primary_reads
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL)
    (h_specs :
      ∀ providerRow, providerRow ∈ table.table →
        ZiskFv.AirsClean.Mem.Spec
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
    (h_primary_read :
      ActiveMemReplayRowsOfTablePrimaryReadPrefixSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory (activeMemReplayRowsOfTable table) := by
  unfold activeMemReplayRowsOfTable
  exact
    memoryBusRowsReadWriteSound_flatMap_activeMemReplayEntriesOfRow
      initialMemory table.table
      (fun providerRow =>
        eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      h_specs
      h_primary_read

/-- The indexed table bridge and range facts prove local chronological order
    for the active replay emissions projected from one concrete table row.

    This discharges the primary-before-dual part of the chronological proof
    from the generated Mem row and `mem.pil:397` range check. It does not claim
    full table-level `Pairwise` order across different provider rows. -/
theorem activeMemReplayEntriesOfTableRow_chronological_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow
        (eval (table.environment (table.table.get idx))
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) := by
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_rowAt : row = ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    dsimp [row]
    exact h_bridge.rowAt_eq idx
  have h_spec_rowAt :
      ZiskFv.AirsClean.Mem.Spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) :=
    rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_spec_row : ZiskFv.AirsClean.Mem.Spec row := by
    simpa [h_rowAt] using h_spec_rowAt
  have h_step_le_of_dual :
      row.sel_dual = 1 → row.step.val ≤ row.step_dual.val := by
    intro h_sel_dual
    have h_sel_dual_mem : mem.sel_dual idx.val = 1 := by
      simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_dual
    have h_wr_lt := wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx
    have h_step_le_rowAt :
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val).step.val ≤
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val).step_dual.val :=
      ZiskFv.AirsClean.Mem.rowAt_step_le_step_dual_of_dual_step_delta_range
        mem idx.val (h_ranges.stepColumns idx) h_wr_lt
        (h_ranges.dualStepDelta idx h_sel_dual_mem)
    simpa [h_rowAt] using h_step_le_rowAt
  exact activeMemReplayEntriesOfRow_chronological_of_spec_of_dual_step_le
    h_spec_row h_step_le_of_dual

/-- On a bridged non-boundary same-address Mem table position, if the previous
    `Valid_Mem` row has no dual emission, the previous primary timestamp is no
    later than the current primary timestamp. This is the adjacent-row
    cross-row ordering step behind full chronological `Pairwise` order. -/
theorem previous_primary_step_le_step_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_no_dual : mem.sel_dual (idx.val - 1) = 0) :
    (mem.step (idx.val - 1)).val ≤ (mem.step idx.val).val := by
  exact
    ZiskFv.Airs.Mem.previous_primary_step_le_step_of_same_addr_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary
      (h_ranges.stepColumns idx)
      (wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx)
      (h_ranges.incrementChunks idx) h_no_dual

/-- On a bridged non-boundary same-address Mem table position, if the previous
    `Valid_Mem` row has a dual emission, the previous dual timestamp is no
    later than the current primary timestamp. This is the dual predecessor case
    for adjacent-row chronological order. -/
theorem previous_dual_step_le_step_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_dual : mem.sel_dual (idx.val - 1) = 1) :
    (mem.step_dual (idx.val - 1)).val ≤ (mem.step idx.val).val := by
  exact
    ZiskFv.Airs.Mem.previous_dual_step_le_step_of_same_addr_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary
      (h_ranges.stepColumns idx)
      (wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx)
      (h_ranges.incrementChunks idx) h_dual

/-- On a bridged non-boundary address-change Mem table position, the previous
    row's address is strictly smaller than the current row's address. This is
    the adjacent address-order step behind the prior-prefix disjointness proof. -/
theorem previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    (mem.addr (idx.val - 1)).val < (mem.addr idx.val).val := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  exact
    ZiskFv.Airs.Mem.previous_addr_lt_addr_of_addr_change_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_addr_change h_not_boundary
      (h_ranges.addrColumns idx) (h_ranges.addrColumns previousIdx)
      (h_ranges.incrementChunks idx)

/-- Adjacent Mem rows in a generated single-segment table have monotone
    addresses after the first row.

    This splits on the generated `addr_changes` bit: same-address rows carry
    the previous address, and address-change rows strictly increase it. The
    non-boundary premise is supplied by the fixed `SEGMENT_L1 = [1,0...]`
    column from `mem.pil:86`. -/
theorem previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val) :
    (mem.addr (idx.val - 1)).val ≤ (mem.addr idx.val).val := by
  have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_addr_changes_zero | h_addr_changes_one
  · have h_addr_changes_zero_mem : mem.addr_changes idx.val = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero
    have h_addr_eq :=
      addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
        h_bridge idx h_addr_changes_zero_mem h_not_boundary
    rw [h_addr_eq]
  · have h_addr_changes_one_mem : mem.addr_changes idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one
    exact le_of_lt
      (previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
        h_bridge h_ranges idx h_addr_changes_one_mem h_not_boundary)

/-- The generated single-segment Mem address order is monotone between any two
    table indices. -/
theorem addr_le_of_index_le_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (earlier later : Fin table.table.length)
    (h_le : earlier.val ≤ later.val) :
    (mem.addr earlier.val).val ≤ (mem.addr later.val).val := by
  have h_mono :
      ∀ n, (h_earlier_le_n : earlier.val ≤ n) →
        n < table.table.length →
          (mem.addr earlier.val).val ≤ (mem.addr n).val := by
    intro n h_earlier_le_n h_n_lt
    induction n, h_earlier_le_n using Nat.le_induction with
    | base =>
        exact le_rfl
    | succ n _h_earlier_le_n ih =>
        have h_adj :
            (mem.addr n).val ≤ (mem.addr (n + 1)).val := by
          simpa using
            previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge
              h_bridge h_ranges h_fixed ⟨n + 1, h_n_lt⟩ (Nat.succ_pos n)
        have h_n_lt' : n < table.table.length := by omega
        exact le_trans (ih h_n_lt') h_adj
  exact h_mono later.val h_le later.isLt

/-- At a selected address-change row, every prior table row has a different
    Mem address.

    The final adjacent step is strict by the address-change increment
    constraint; all earlier adjacent steps are monotone by generated
    same-address carry or strict address-change order. -/
theorem prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1) :
    ∀ otherIdx : Fin table.table.length,
      otherIdx.val < idx.val → mem.addr otherIdx.val ≠ mem.addr idx.val := by
  intro otherIdx h_other_lt h_addr_eq
  have h_idx_pos : 0 < idx.val := by omega
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
  have h_previous_lt_current :
      (mem.addr previousIdx.val).val < (mem.addr idx.val).val := by
    simpa [previousIdx] using
      previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
        h_bridge h_ranges idx h_addr_change h_not_boundary
  have h_other_le_previous :
      (mem.addr otherIdx.val).val ≤ (mem.addr previousIdx.val).val := by
    apply addr_le_of_index_le_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed otherIdx previousIdx
    simp [previousIdx]
    omega
  have h_other_lt_current :
      (mem.addr otherIdx.val).val < (mem.addr idx.val).val :=
    lt_of_le_of_lt h_other_le_previous h_previous_lt_current
  rw [h_addr_eq] at h_other_lt_current
  exact (lt_irrefl _ h_other_lt_current)

/-- A nonempty generated Mem segment carries a 29-bit previous-segment address.

    The segment distance chunks (`mem.pil:267-268`) and generated base-distance
    equation (`mem.pil:265`) first give a coarse `2^33` bound. The fixed
    `SEGMENT_L1` row-0 boundary (`mem.pil:86`) then splits on row 0:
    same-address rows identify `mem.addr 0` with `previous_segment_addr`, and
    address-change rows make `previous_segment_addr < mem.addr 0`. In both
    cases the row address has the 29-bit witness-column bound from
    `mem.pil:109`. -/
theorem previous_segment_addr_lt_two_pow_29_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    segment.previous_segment_addr.val < 2 ^ 29 := by
  let idx0 : Fin table.table.length := ⟨0, h_nonempty⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    simpa [idx0] using (h_bridge.generatedAt idx0).1
  have h_boundary : segment.segment_l1 0 = 1 :=
    h_fixed.segmentL1_first h_nonempty
  have h_prev_lt_33 : segment.previous_segment_addr.val < 2 ^ 33 :=
    ZiskFv.Airs.Mem.previous_segment_addr_lt_two_pow_33_of_segment_every_row
      h_segment h_segment_ranges.distanceBaseChunks
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx0
  rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem 0) h_spec with
    h_addr_changes_zero | h_addr_changes_one
  · have h_addr_changes_zero_mem : mem.addr_changes 0 = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero
    have h_addr_eq :=
      ZiskFv.Airs.Mem.addr_eq_previous_segment_of_same_addr_boundary_segment_every_row
        h_segment h_addr_changes_zero_mem h_boundary
    rw [← h_addr_eq]
    exact h_ranges.addrColumns idx0
  · have h_addr_changes_one_mem : mem.addr_changes 0 = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one
    have h_prev_expr :=
      ZiskFv.Airs.Mem.segment_previous_addr_eq_previous_segment_of_boundary
        (cols := segment) (v := mem) (row := 0) h_boundary
    have h_prev_expr_range :
        (ZiskFv.Airs.Mem.segment_previous_addr segment mem 0).val < 2 ^ 33 := by
      rw [h_prev_expr]
      exact h_prev_lt_33
    have h_lt :=
      ZiskFv.Airs.Mem.segment_previous_addr_lt_addr_of_addr_change_segment_every_row_of_previous_lt_two_pow_33
        (cols := segment) (v := mem) (row := 0)
        h_segment h_addr_changes_one_mem (h_ranges.addrColumns idx0)
        h_prev_expr_range (h_ranges.incrementChunks idx0)
    rw [h_prev_expr] at h_lt
    exact lt_trans h_lt (h_ranges.addrColumns idx0)

/-- The previous-segment carried address is no greater than any generated Mem row
    address, assuming the carried address has the same 29-bit no-wrap bound as
    row addresses.

    Row zero is the fixed segment boundary (`mem.pil:86`): same-address rows
    equal the carried address, while address-change rows are strictly larger by
    the generated increment equation (`mem.pil:375`) plus range checks. Later
    rows inherit the bound from adjacent monotonicity. -/
theorem previous_segment_addr_le_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29)
    (idx : Fin table.table.length) :
    segment.previous_segment_addr.val ≤ (mem.addr idx.val).val := by
  have h_mono :
      ∀ n, n < table.table.length →
        segment.previous_segment_addr.val ≤ (mem.addr n).val := by
    intro n h_n_lt
    induction n with
    | zero =>
        let idx0 : Fin table.table.length := ⟨0, h_n_lt⟩
        have h_segment :
            ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
          simpa [idx0] using (h_bridge.generatedAt idx0).1
        have h_boundary : segment.segment_l1 0 = 1 := h_fixed.segmentL1_first h_n_lt
        have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx0
        rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
            (ZiskFv.AirsClean.Mem.rowAt mem 0) h_spec with
          h_addr_changes_zero | h_addr_changes_one
        · have h_addr_changes_zero_mem : mem.addr_changes 0 = 0 := by
            simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero
          have h_addr_eq :=
            ZiskFv.Airs.Mem.addr_eq_previous_segment_of_same_addr_boundary_segment_every_row
              h_segment h_addr_changes_zero_mem h_boundary
          rw [h_addr_eq]
        · have h_addr_changes_one_mem : mem.addr_changes 0 = 1 := by
            simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one
          have h_prev_expr :=
            ZiskFv.Airs.Mem.segment_previous_addr_eq_previous_segment_of_boundary
              (cols := segment) (v := mem) (row := 0) h_boundary
          have h_prev_expr_range :
              (ZiskFv.Airs.Mem.segment_previous_addr segment mem 0).val < 2 ^ 29 := by
            rw [h_prev_expr]
            exact h_previous_segment_addr_range
          have h_lt :=
            ZiskFv.Airs.Mem.segment_previous_addr_lt_addr_of_addr_change_segment_every_row
              (cols := segment) (v := mem) (row := 0)
              h_segment h_addr_changes_one_mem (h_ranges.addrColumns idx0)
              h_prev_expr_range (h_ranges.incrementChunks idx0)
          rw [h_prev_expr] at h_lt
          exact le_of_lt h_lt
    | succ n ih =>
        have h_n_lt' : n < table.table.length := by omega
        have h_adj :
            (mem.addr n).val ≤ (mem.addr (n + 1)).val := by
          simpa using
            previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge
              h_bridge h_ranges h_fixed ⟨n + 1, h_n_lt⟩ (Nat.succ_pos n)
        exact le_trans (ih h_n_lt') h_adj
  exact h_mono idx.val idx.isLt

/-- At an address-change row, the previous-segment seed address is strictly less
    than the current row address. -/
theorem previous_segment_addr_lt_addr_of_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1) :
    segment.previous_segment_addr.val < (mem.addr idx.val).val := by
  by_cases h_idx_zero : idx.val = 0
  · let idx0 : Fin table.table.length := ⟨0, by omega⟩
    have h_segment :
        ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
      simpa [idx0] using (h_bridge.generatedAt idx0).1
    have h_boundary : segment.segment_l1 0 = 1 :=
      h_fixed.segmentL1_first idx0.isLt
    have h_prev_expr :=
      ZiskFv.Airs.Mem.segment_previous_addr_eq_previous_segment_of_boundary
        (cols := segment) (v := mem) (row := 0) h_boundary
    have h_prev_expr_range :
        (ZiskFv.Airs.Mem.segment_previous_addr segment mem 0).val < 2 ^ 29 := by
      rw [h_prev_expr]
      exact h_previous_segment_addr_range
    have h_addr_change_zero : mem.addr_changes 0 = 1 := by
      simpa [h_idx_zero] using h_addr_change
    have h_lt :=
      ZiskFv.Airs.Mem.segment_previous_addr_lt_addr_of_addr_change_segment_every_row
        (cols := segment) (v := mem) (row := 0)
        h_segment h_addr_change_zero (h_ranges.addrColumns idx0)
        h_prev_expr_range (h_ranges.incrementChunks idx0)
    rw [h_prev_expr] at h_lt
    simpa [h_idx_zero] using h_lt
  · have h_idx_pos : 0 < idx.val := by omega
    let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
    have h_seed_le_previous :
        segment.previous_segment_addr.val ≤ (mem.addr previousIdx.val).val :=
      previous_segment_addr_le_addr_memTableGeneratedRowsBridge
        h_bridge h_ranges h_fixed h_previous_segment_addr_range previousIdx
    have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
    have h_previous_lt_current :
        (mem.addr previousIdx.val).val < (mem.addr idx.val).val := by
      simpa [previousIdx] using
        previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge
          h_bridge h_ranges idx h_addr_change h_not_boundary
    exact lt_of_le_of_lt h_seed_le_previous h_previous_lt_current

/-- Address-change primary reads are byte-disjoint from the continuation seed
    entry once the seed address has the 29-bit no-wrap bound. -/
theorem previousSegmentSeedDisjoint_of_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
      (memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val))
      (memPreviousSegmentReplayEntry segment) := by
  have h_seed_lt_current :=
    previous_segment_addr_lt_addr_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed h_previous_segment_addr_range idx h_addr_change
  have h_row_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_addr_ne :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        segment.previous_segment_addr := by
    intro h_addr_eq
    have h_mem_addr_eq : mem.addr idx.val = segment.previous_segment_addr := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq
    rw [h_mem_addr_eq] at h_seed_lt_current
    exact lt_irrefl _ h_seed_lt_current
  exact
    memoryBusEntryByteDisjoint_primary_previousSegment_of_addr_ne
      h_row_range h_previous_segment_addr_range h_addr_ne

/-- Address-change reads are justified against their concrete split prefix when
some selected row at the same Mem address contributes the zero-preload pointer.

This generalizes the selected-row address-change theorem to inactive predecessor
rows used by the same-address carry induction. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx preloadIdx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_preload_sel : mem.sel preloadIdx.val = 1)
    (h_addr_eq : mem.addr idx.val = mem.addr preloadIdx.val)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_zero :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) := by
    simpa [readEntry] using
      readEventReplayAgreement_after_zeroMemoryOfRows_same_addr_memTableGeneratedRowsBridge
        h_bridge h_ranges idx preloadIdx h_preload_sel h_addr_eq h_addr_change h_read
  apply
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
      h_zero
  intro entry h_entry
  rcases List.mem_flatMap.mp h_entry with
    ⟨priorProviderRow, h_prior_mem, h_entry_row⟩
  rcases priorRows_mem_index_lt_of_split
      (xs := table.table) (priorRows := priorRows)
      (laterRows := laterRows) (providerRow := providerRow)
      h_split h_prior_mem with
    ⟨otherIdx, h_get, h_other_lt_prior_length⟩
  have h_other_lt_idx : otherIdx.val < idx.val := by omega
  have h_addr_ne :=
    prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed idx h_addr_change otherIdx h_other_lt_idx
  have h_entry_rowAt :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
    rw [← h_get] at h_entry_row
    rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
    exact h_entry_row
  have h_selected_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_other_range :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
  have h_addr_ne_row :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
    intro h_addr_eq_row
    exact h_addr_ne (by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq_row.symm)
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry_rowAt with
    h_entry_primary | h_entry_dual
  · simpa [readEntry, h_entry_primary] using
      memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row
  · simpa [readEntry, h_entry_dual] using
      memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row

/-- Address-change reads are justified against the continuation-seeded initial
    memory when the previous-segment seed entry is byte-disjoint from the read.

    This factors the replay-fold mechanics from the remaining AIR/range fact:
    proving the seed disjointness (or a safe overwrite alternative) is the next
    continuation-specific obligation. -/
theorem readEventReplayAgreement_after_previousSegmentInitialMemory_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx preloadIdx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_preload_sel : mem.sel preloadIdx.val = 1)
    (h_addr_eq : mem.addr idx.val = mem.addr preloadIdx.val)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_seed_disjoint :
      ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
        (memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val))
        (memPreviousSegmentReplayEntry segment)) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_zero :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) := by
    simpa [readEntry] using
      readEventReplayAgreement_after_zeroMemoryOfRows_same_addr_memTableGeneratedRowsBridge
        h_bridge h_ranges idx preloadIdx h_preload_sel h_addr_eq h_addr_change h_read
  have h_seed :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) := by
    have h_lift :=
      ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_disjoint
        h_zero
        (by simpa [readEntry] using h_seed_disjoint)
    simpa [previousSegmentInitialMemoryOfRows] using h_lift
  apply
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
      h_seed
  intro entry h_entry
  rcases List.mem_flatMap.mp h_entry with
    ⟨priorProviderRow, h_prior_mem, h_entry_row⟩
  rcases priorRows_mem_index_lt_of_split
      (xs := table.table) (priorRows := priorRows)
      (laterRows := laterRows) (providerRow := providerRow)
      h_split h_prior_mem with
    ⟨otherIdx, h_get, h_other_lt_prior_length⟩
  have h_other_lt_idx : otherIdx.val < idx.val := by omega
  have h_addr_ne :=
    prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed idx h_addr_change otherIdx h_other_lt_idx
  have h_entry_rowAt :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
    rw [← h_get] at h_entry_row
    rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
    exact h_entry_row
  have h_selected_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_other_range :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
  have h_addr_ne_row :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
    intro h_addr_eq_row
    exact h_addr_ne (by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq_row.symm)
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry_rowAt with
    h_entry_primary | h_entry_dual
  · simpa [readEntry, h_entry_primary] using
      memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row
  · simpa [readEntry, h_entry_dual] using
      memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
        h_selected_range h_other_range h_addr_ne_row

/-- Iterate same-address predecessor carry for any read row up to a selected row
    at the same Mem address over an arbitrary initial memory.

The induction itself only uses generated same-address predecessor facts. The
caller supplies the semantic bases: row-0/segment-boundary same-address reads,
and address-change reads against the chosen initial memory. -/
theorem readEventReplayAgreement_after_initialMemory_splitPrefix_to_selected_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (selectedIdx : Fin table.table.length)
    (h_boundary_same_addr :
      ∀ providerRow laterRows,
        table.table = providerRow :: laterRows →
        mem.addr_changes 0 = 0 →
        mem.wr 0 = 0 →
        mem.addr 0 = mem.addr selectedIdx.val →
          ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
            initialMemory
            (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
              (memPrimaryReplayEntryOfRow
                (ZiskFv.AirsClean.Mem.rowAt mem 0))))
    (h_addr_change_base :
      ∀ currentIdx : Fin table.table.length,
        ∀ currentPriorRows currentProviderRow currentLaterRows,
          table.table =
              currentPriorRows ++ currentProviderRow :: currentLaterRows →
          currentIdx.val = currentPriorRows.length →
          currentIdx.val ≤ selectedIdx.val →
          mem.addr currentIdx.val = mem.addr selectedIdx.val →
          mem.addr_changes currentIdx.val = 1 →
          mem.wr currentIdx.val = 0 →
            ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
              (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
                initialMemory
                (currentPriorRows.flatMap fun currentPriorProviderRow =>
                  activeMemReplayEntriesOfRow
                    (eval (table.environment currentPriorProviderRow)
                      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
              (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
                (memPrimaryReplayEntryOfRow
                  (ZiskFv.AirsClean.Mem.rowAt mem currentIdx.val))))
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_idx_le_selected : idx.val ≤ selectedIdx.val)
    (h_addr_eq_selected : mem.addr idx.val = mem.addr selectedIdx.val)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        initialMemory
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let prefixRows (rows : List (Array FGL)) :=
    rows.flatMap fun priorProviderRow =>
      activeMemReplayEntriesOfRow
        (eval (table.environment priorProviderRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
  let P : ℕ → Prop := fun n =>
    ∀ (idx : Fin table.table.length)
      (priorRows : List (Array FGL))
      (providerRow : Array FGL)
      (laterRows : List (Array FGL)),
      idx.val = n →
      table.table = priorRows ++ providerRow :: laterRows →
      idx.val = priorRows.length →
      idx.val ≤ selectedIdx.val →
      mem.addr idx.val = mem.addr selectedIdx.val →
      mem.wr idx.val = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
            initialMemory (prefixRows priorRows))
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem idx.val)))
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih idx priorRows providerRow laterRows h_idx_n h_split
      h_idx_val h_idx_le_selected h_addr_eq_selected h_read
    have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
    rcases ZiskFv.AirsClean.Mem.addr_changes_boolean_of_spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
      h_addr_changes_zero_row | h_addr_changes_one_row
    · have h_addr_changes_zero : mem.addr_changes idx.val = 0 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_zero_row
      by_cases h_idx_zero : idx.val = 0
      · have h_prior_nil : priorRows = [] := by
          have h_prior_length_zero : priorRows.length = 0 := by omega
          exact List.length_eq_zero_iff.mp h_prior_length_zero
        have h_split_zero : table.table = providerRow :: laterRows := by
          simpa [h_prior_nil] using h_split
        have h_zero :=
          h_boundary_same_addr providerRow laterRows h_split_zero
            (by simpa [h_idx_zero] using h_addr_changes_zero)
            (by simpa [h_idx_zero] using h_read)
            (by simpa [h_idx_zero] using h_addr_eq_selected)
        simpa [prefixRows, h_prior_nil, h_idx_zero] using h_zero
      · have h_idx_pos : 0 < idx.val := Nat.pos_of_ne_zero h_idx_zero
        have h_prior_ne : priorRows ≠ [] := by
          intro h_nil
          rw [h_nil] at h_idx_val
          simp at h_idx_val
          omega
        let previousProviderRow := priorRows.getLast h_prior_ne
        let priorPrefix := priorRows.dropLast
        have h_prior_split :
            priorRows = priorPrefix ++ [previousProviderRow] := by
          exact (List.dropLast_concat_getLast h_prior_ne).symm
        have h_split_previous :
            table.table = priorPrefix ++ previousProviderRow :: providerRow :: laterRows := by
          rw [h_prior_split] at h_split
          simpa [priorPrefix, previousProviderRow, List.append_assoc] using h_split
        have h_idx_val_previous : idx.val = priorPrefix.length + 1 := by
          have h_len : priorRows.length = priorPrefix.length + 1 := by
            rw [h_prior_split]
            simp [priorPrefix, previousProviderRow]
          omega
        let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
        have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
        have h_addr_previous :=
          addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
            h_bridge idx h_addr_changes_zero h_not_boundary
        have h_previous_addr_eq_selected :
            mem.addr previousIdx.val = mem.addr selectedIdx.val := by
          simpa [previousIdx] using h_addr_previous.symm.trans h_addr_eq_selected
        have h_previous_idx_val :
            previousIdx.val = priorPrefix.length := by
          simp [previousIdx]
          omega
        have h_previous_lt : previousIdx.val < idx.val := by
          simp [previousIdx]
          omega
        have h_previous_lt_n : previousIdx.val < n := by
          omega
        have h_previous_le_selected : previousIdx.val ≤ selectedIdx.val := by
          omega
        have h_current :=
          readEventReplayAgreement_after_initialMemory_splitPrefix_previous_row_memTableGeneratedRowsBridge
            initialMemory h_bridge h_fixed idx priorPrefix previousProviderRow
            providerRow laterRows h_split_previous h_idx_val_previous
            h_addr_changes_zero h_read
            (fun h_previous_read => by
              exact
                ih previousIdx.val h_previous_lt_n previousIdx priorPrefix
                  previousProviderRow (providerRow :: laterRows) rfl
                  h_split_previous h_previous_idx_val h_previous_le_selected
                  h_previous_addr_eq_selected h_previous_read)
        simpa [prefixRows, h_prior_split] using h_current
    · have h_addr_changes_one : mem.addr_changes idx.val = 1 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_changes_one_row
      simpa [prefixRows] using
        h_addr_change_base idx priorRows providerRow laterRows h_split h_idx_val
          h_idx_le_selected h_addr_eq_selected h_addr_changes_one h_read
  exact
    hP idx.val idx priorRows providerRow laterRows rfl h_split h_idx_val
      h_idx_le_selected h_addr_eq_selected h_read

/-- Iterate same-address predecessor carry for any read row up to a selected row
at the same Mem address from the finite zero-preloaded Mem-table memory.

The only remaining base outside the extracted local constraints is the
row-0/segment-boundary same-address case. When `addr_changes = 1`, the finite
zero-preload memory supplies the read bytes; when `addr_changes = 0` at a
positive index, the predecessor lemma moves one row backward. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_to_selected_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (selectedIdx : Fin table.table.length)
    (h_selected_sel : mem.sel selectedIdx.val = 1)
    (h_boundary_same_addr :
      ∀ providerRow laterRows,
        table.table = providerRow :: laterRows →
        mem.addr_changes 0 = 0 →
        mem.wr 0 = 0 →
        mem.addr 0 = mem.addr selectedIdx.val →
          ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
            (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
              (activeMemReplayRowsOfTable table))
            (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
              (memPrimaryReplayEntryOfRow
                (ZiskFv.AirsClean.Mem.rowAt mem 0))))
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_idx_le_selected : idx.val ≤ selectedIdx.val)
    (h_addr_eq_selected : mem.addr idx.val = mem.addr selectedIdx.val)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  refine
    readEventReplayAgreement_after_initialMemory_splitPrefix_to_selected_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
      h_bridge h_fixed selectedIdx h_boundary_same_addr ?_
      idx priorRows providerRow laterRows h_split h_idx_val h_idx_le_selected
      h_addr_eq_selected h_read
  intro currentIdx currentPriorRows currentProviderRow currentLaterRows
    h_current_split h_current_idx_val _h_current_le_selected h_current_addr_eq
    h_current_addr_change h_current_read
  exact
    readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed currentIdx selectedIdx currentPriorRows currentProviderRow
      currentLaterRows h_current_split h_current_idx_val h_selected_sel
      h_current_addr_eq h_current_addr_change h_current_read

/-- The concrete table's selected-primary-read prefix obligation follows from
the Mem AIR predecessor induction plus one explicit row-0 same-address boundary
input.

This is the current reduced proof surface: all positive-index same-address
reads iterate to either an address-change zero-preload base or this row-0
segment-continuation case. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_memTableGeneratedRowsBridge_boundary_same_addr
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_boundary_same_addr :
      ∀ selectedIdx : Fin table.table.length,
        ∀ providerRow laterRows,
          mem.sel selectedIdx.val = 1 →
          table.table = providerRow :: laterRows →
          mem.addr_changes 0 = 0 →
          mem.wr 0 = 0 →
          mem.addr 0 = mem.addr selectedIdx.val →
            ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
              (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
                (activeMemReplayRowsOfTable table))
              (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
                (memPrimaryReplayEntryOfRow
                  (ZiskFv.AirsClean.Mem.rowAt mem 0)))) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      table := by
  intro priorRows providerRow laterRows h_split h_sel_row h_wr_row
  let idx : Fin table.table.length := ⟨priorRows.length, by
    rw [h_split]
    simp⟩
  have h_idx_val : idx.val = priorRows.length := rfl
  have h_provider_get : table.table.get idx = providerRow :=
    providerRow_get_eq_of_split idx h_split h_idx_val
  have h_rowAt :
      eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    rw [← h_provider_get]
    exact h_bridge.rowAt_eq idx
  have h_sel : mem.sel idx.val = 1 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_row
  have h_read : mem.wr idx.val = 0 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_wr_row
  have h_agreement :=
    readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_to_selected_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed idx h_sel
      (fun providerRow laterRows h_boundary_split h_addr_changes_zero h_boundary_read
          h_boundary_addr_eq =>
        h_boundary_same_addr idx providerRow laterRows h_sel h_boundary_split
          h_addr_changes_zero h_boundary_read h_boundary_addr_eq)
      idx priorRows providerRow laterRows h_split h_idx_val le_rfl rfl h_read
  simpa [h_rowAt] using h_agreement

/-- The generated first-segment boundary constraint forces `addr_changes = 1`
    at row 0.

    This projects `mem.pil:377`
    `is_first_segment * SEGMENT_L1 * (1 - addr_changes) = 0` through the
    indexed table bridge, using the fixed `SEGMENT_L1 0 = 1` fact from
    `mem.pil:86` and an explicit first-segment witness. -/
theorem addr_changes_eq_one_of_first_segment_row_zero_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1)
    {providerRow : Array FGL}
    {laterRows : List (Array FGL)}
    (h_split : table.table = providerRow :: laterRows) :
    mem.addr_changes 0 = 1 := by
  let idx0 : Fin table.table.length := ⟨0, by
    rw [h_split]
    simp⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    have h_generated := h_bridge.generatedAt idx0
    simpa [idx0] using h_generated.1
  have h_boundary : segment.segment_l1 0 = 1 := by
    have h_nonempty : 0 < table.table.length := by
      rw [h_split]
      simp
    exact h_fixed.segmentL1_first h_nonempty
  exact
    ZiskFv.Airs.Mem.addr_changes_eq_one_of_first_segment_boundary_segment_every_row
      h_segment h_first_segment h_boundary

/-- For the first generated Mem segment, the row-0 same-address boundary case
    is impossible: `mem.pil:377` forces row 0 to be an address-change row.

    Continuation segments still require a different initial-memory statement
    carrying `previous_segment_*`; this theorem intentionally closes only the
    first-segment specialization against the finite zero-preload memory. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_firstSegment_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      table := by
  refine
    activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_memTableGeneratedRowsBridge_boundary_same_addr
      h_bridge h_ranges h_fixed ?_
  intro selectedIdx providerRow laterRows _h_sel h_split h_addr_changes_zero _h_read _h_addr_eq
  have h_addr_changes_one :=
    addr_changes_eq_one_of_first_segment_row_zero_memTableGeneratedRowsBridge
      h_bridge h_fixed h_first_segment (providerRow := providerRow) (laterRows := laterRows)
      h_split
  rw [h_addr_changes_zero] at h_addr_changes_one
  exact False.elim (zero_ne_one h_addr_changes_one)

/-- In a continuation Mem segment, a row-0 same-address read is justified by
    the previous segment's carried-out address and value chunks.

    This is the local base case needed before changing the table-wide induction
    to use a continuation-aware initial memory. It intentionally proves only the
    row-0 read itself; preservation through later zero-preload/replay folds is a
    separate integration obligation. -/
theorem readEventReplayAgreement_after_previousSegmentInitialMemory_row_zero_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    {providerRow : Array FGL}
    {laterRows : List (Array FGL)}
    (h_split : table.table = providerRow :: laterRows)
    (h_addr_changes_zero : mem.addr_changes 0 = 0)
    (h_read : mem.wr 0 = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem 0))) := by
  let idx0 : Fin table.table.length := ⟨0, by
    rw [h_split]
    simp⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    have h_generated := h_bridge.generatedAt idx0
    simpa [idx0] using h_generated.1
  have h_boundary : segment.segment_l1 0 = 1 := by
    have h_nonempty : 0 < table.table.length := by
      rw [h_split]
      simp
    exact h_fixed.segmentL1_first h_nonempty
  have h_read_same_addr :
      mem.read_same_addr 0 = 1 := by
    simpa [idx0] using
      read_same_addr_eq_one_of_memTableGeneratedRowsBridge
        h_bridge idx0 h_addr_changes_zero h_read
  have h_addr :
      mem.addr 0 = segment.previous_segment_addr :=
    ZiskFv.Airs.Mem.addr_eq_previous_segment_of_same_addr_boundary_segment_every_row
      h_segment h_addr_changes_zero h_boundary
  have h_values :
      mem.value_0 0 = segment.previous_segment_value_0
        ∧ mem.value_1 0 = segment.previous_segment_value_1 :=
    ZiskFv.Airs.Mem.values_eq_previous_segment_of_read_same_addr_boundary_segment_every_row
      h_segment h_read_same_addr h_boundary
  let writeEntry := memPreviousSegmentReplayEntry segment
  let readEntry := memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem 0)
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    dsimp [readEntry, writeEntry]
    simp [h_addr]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry
          (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
          writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
      h_ptr h_value_0 h_value_1
  simpa [previousSegmentInitialMemoryOfRows, writeEntry, readEntry] using h_replay

/-- The continuation-seeded table's selected-primary-read prefix obligation
    follows from the generic predecessor induction plus an explicit
    address-change seed-disjointness premise.

    The row-0 same-address base is supplied by `previous_segment_*`; the
    remaining continuation-specific work is to prove the seed cannot corrupt
    zero-valued address-change reads. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_addr_change_seed_disjoint :
      ∀ currentIdx selectedIdx : Fin table.table.length,
        ∀ currentPriorRows currentProviderRow currentLaterRows,
          mem.sel selectedIdx.val = 1 →
          table.table =
              currentPriorRows ++ currentProviderRow :: currentLaterRows →
          currentIdx.val = currentPriorRows.length →
          currentIdx.val ≤ selectedIdx.val →
          mem.addr currentIdx.val = mem.addr selectedIdx.val →
          mem.addr_changes currentIdx.val = 1 →
          mem.wr currentIdx.val = 0 →
            ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
              (memPrimaryReplayEntryOfRow
                (ZiskFv.AirsClean.Mem.rowAt mem currentIdx.val))
              (memPreviousSegmentReplayEntry segment)) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  intro priorRows providerRow laterRows h_split h_sel_row h_wr_row
  let idx : Fin table.table.length := ⟨priorRows.length, by
    rw [h_split]
    simp⟩
  have h_idx_val : idx.val = priorRows.length := rfl
  have h_provider_get : table.table.get idx = providerRow :=
    providerRow_get_eq_of_split idx h_split h_idx_val
  have h_rowAt :
      eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    rw [← h_provider_get]
    exact h_bridge.rowAt_eq idx
  have h_sel : mem.sel idx.val = 1 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_row
  have h_read : mem.wr idx.val = 0 := by
    simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_wr_row
  have h_agreement :=
    readEventReplayAgreement_after_initialMemory_splitPrefix_to_selected_memTableGeneratedRowsBridge
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      h_bridge h_fixed idx
      (fun boundaryProviderRow boundaryLaterRows h_boundary_split
          h_addr_changes_zero h_boundary_read _h_boundary_addr_eq =>
        readEventReplayAgreement_after_previousSegmentInitialMemory_row_zero_memTableGeneratedRowsBridge
          h_bridge h_fixed h_boundary_split h_addr_changes_zero h_boundary_read)
      (fun currentIdx currentPriorRows currentProviderRow currentLaterRows
          h_current_split h_current_idx_val h_current_le_selected h_current_addr_eq
          h_current_addr_change h_current_read =>
        readEventReplayAgreement_after_previousSegmentInitialMemory_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge
          h_bridge h_ranges h_fixed currentIdx idx currentPriorRows currentProviderRow
          currentLaterRows h_current_split h_current_idx_val h_sel h_current_addr_eq
          h_current_addr_change h_current_read
          (h_addr_change_seed_disjoint currentIdx idx currentPriorRows
            currentProviderRow currentLaterRows h_sel h_current_split h_current_idx_val
            h_current_le_selected h_current_addr_eq h_current_addr_change h_current_read))
      idx priorRows providerRow laterRows h_split h_idx_val le_rfl rfl h_read
  simpa [h_rowAt] using h_agreement

/-- The continuation-seeded table's selected-primary-read prefix obligation
    follows from concrete Mem facts plus a 29-bit range fact for the carried
    previous-segment address.

    The explicit range premise is the remaining extractor-facing input: the
    table proof no longer assumes address-change seed disjointness. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  apply
    activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed
  intro currentIdx _selectedIdx _currentPriorRows _currentProviderRow _currentLaterRows
    _h_selected_sel _h_split _h_idx_val _h_current_le_selected _h_current_addr_eq
    h_current_addr_change _h_current_read
  exact
    previousSegmentSeedDisjoint_of_addr_change_memTableGeneratedRowsBridge
      h_bridge h_ranges h_fixed h_previous_segment_addr_range
      currentIdx h_current_addr_change

/-- Continuation-seeded selected-primary-read prefix soundness with the
    previous-segment address range derived from segment-global range facts. -/
theorem activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ActiveMemReplayRowsOfTablePrimaryReadPrefixSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
      h_bridge h_ranges h_fixed
      (previous_segment_addr_lt_two_pow_29_of_memTableGeneratedRowsBridge
        h_bridge h_ranges h_segment_ranges h_fixed h_nonempty)

/-- Address-change selected primary reads are justified against their concrete
    prior table prefix from the zero-preloaded Mem-table memory.

    This closes the prior-prefix byte-disjointness premise by deriving
    all-prior address separation from the fixed `SEGMENT_L1` shape and the
    generated address-order constraints. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  exact
    readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_ne_memTableGeneratedRowsBridge
      h_bridge h_ranges idx priorRows providerRow laterRows h_split h_idx_val
      h_sel h_addr_change h_read
      (prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge
        h_bridge h_ranges h_fixed idx h_addr_change)

/-- Row-order facts for the concrete mutable-Mem replay projection. This is
    the table-local target that accepted full-execution integration should
    prove from Mem sorting, segment carry, and timestamp range facts.

    The target intentionally does not require `Nodup`: the Mem PIL allows
    equal-timestamp read/read dual rows, and identical duplicate reads are
    harmless for replay because reads do not mutate memory. -/
structure MemReplayRowsOfTableOrderFacts
    (table : Table FGL) : Prop where
  chronologicalRows :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (memReplayRowsOfTable table)

/-- Prefix-read soundness for the concrete mutable-Mem replay projection.
    Proving this is the memory-continuity part of the accepted Mem trace
    bridge, after the replay row list has been identified with the concrete
    table projection. -/
def MemReplayRowsOfTablePrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
    initialMemory (memReplayRowsOfTable table)

/-- Row-order facts for the active mutable-Mem replay projection. This is the
    sound chronological target: inactive selector-gated emissions are not
    replay events.  As above, duplicate read entries are permitted. -/
structure ActiveMemReplayRowsOfTableOrderFacts
    (table : Table FGL) : Prop where
  chronologicalRows :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayRowsOfTable table)

/-- Prefix-read soundness for the active mutable-Mem replay projection. -/
def ActiveMemReplayRowsOfTablePrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
    initialMemory (activeMemReplayRowsOfTable table)

/-- Once the selected-primary-read prefix obligation is proved, the active
    table replay fold supplies prefix-read soundness for the whole projected
    active Mem table. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_primary_reads
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL)
    (h_specs :
      ∀ providerRow, providerRow ∈ table.table →
        ZiskFv.AirsClean.Mem.Spec
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
    (h_primary_read :
      ActiveMemReplayRowsOfTablePrimaryReadPrefixSound initialMemory table) :
    ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table := by
  exact
    ZiskFv.ZiskCircuit.MemTrace.memoryBusRowsPrefixReadSound_of_readWriteSound
      initialMemory (activeMemReplayRowsOfTable table)
      (memoryBusRowsReadWriteSound_activeMemReplayRowsOfTable_of_primary_reads
        initialMemory table h_specs h_primary_read)

/-- The indexed generated-row bridge discharges the row-spec input to the
    active-table prefix theorem, leaving only the selected-primary-read prefix
    obligation. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_primary_read :
      ActiveMemReplayRowsOfTablePrimaryReadPrefixSound initialMemory table) :
    ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_primary_reads
      initialMemory table
      (tableRow_specs_of_memTableGeneratedRowsBridge h_bridge)
      h_primary_read

/-- First-segment specialization of the generated Mem-table prefix-read
    theorem, with initial memory given by the finite zero-preload table memory.

    The additional first-segment input is the constructible segment selector
    needed to rule out the row-0 continuation case. Later continuation segments
    need an initial-memory theorem parameterized by `previous_segment_*`
    instead of this zero-preload specialization. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_firstSegment_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1) :
    ActiveMemReplayRowsOfTablePrefixReadSound
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
        h_bridge
        (activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_firstSegment_memTableGeneratedRowsBridge
          h_bridge h_ranges h_fixed h_first_segment)

/-- Continuation-segment specialization of the generated Mem-table prefix-read
    theorem, with initial memory seeded by `previous_segment_*`.

    The remaining segment-level range input rules out overlap between the
    previous-segment seed entry and address-change zero-valued reads. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29) :
    ActiveMemReplayRowsOfTablePrefixReadSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      h_bridge
      (activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
        h_bridge h_ranges h_fixed h_previous_segment_addr_range)

/-- Continuation-segment active-table prefix-read soundness with the
    previous-segment address range derived from segment-global range facts. -/
theorem activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ActiveMemReplayRowsOfTablePrefixReadSound
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      table := by
  exact
    activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge
      (previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table))
      h_bridge
      (activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
        h_bridge h_ranges h_segment_ranges h_fixed h_nonempty)

/-- Transport table-local replay-row order facts across the concrete row-list
    equality used by the raw accepted Mem extraction path. -/
theorem generatedMemRowOrderFacts_of_memReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = memReplayRowsOfTable table)
    (h_order : MemReplayRowsOfTableOrderFacts table) :
    ZiskFv.AirsClean.Mem.GeneratedMemRowOrderFacts rows := by
  rw [h_rows]
  exact
    { chronologicalRows := h_order.chronologicalRows }

/-- Transport table-local prefix-read soundness across the concrete row-list
    equality used by the raw accepted Mem extraction path. -/
theorem memoryBusRowsPrefixReadSound_of_memReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {initialMemory : Std.ExtHashMap Nat (BitVec 8)}
    (h_rows : rows = memReplayRowsOfTable table)
    (h_prefix : MemReplayRowsOfTablePrefixReadSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      initialMemory rows := by
  rw [h_rows]
  exact h_prefix

/-- Transport table-local active replay-row order facts across the concrete
    row-list equality used by the raw accepted Mem extraction path. -/
theorem generatedMemRowOrderFacts_of_activeMemReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_order : ActiveMemReplayRowsOfTableOrderFacts table) :
    ZiskFv.AirsClean.Mem.GeneratedMemRowOrderFacts rows := by
  rw [h_rows]
  exact
    { chronologicalRows := h_order.chronologicalRows }

/-- Transport table-local active prefix-read soundness across the concrete
    row-list equality used by the raw accepted Mem extraction path. -/
theorem memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {initialMemory : Std.ExtHashMap Nat (BitVec 8)}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_prefix : ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      initialMemory rows := by
  rw [h_rows]
  exact h_prefix

/-- The generated segment selector is boolean on any nonempty generated Mem
    table.

    This projects the `is_first_segment * (1 - is_first_segment) = 0`
    constraint from the row-0 `segment_every_row` bundle. -/
theorem is_first_segment_eq_one_or_zero_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_nonempty : 0 < table.table.length) :
    segment.is_first_segment = 1 ∨ segment.is_first_segment = 0 := by
  let idx0 : Fin table.table.length := ⟨0, h_nonempty⟩
  have h_segment :
      ZiskFv.Airs.Mem.segment_every_row segment mem 0 := by
    simpa [idx0] using (h_bridge.generatedAt idx0).1
  rcases h_segment with
    ⟨h_first_bool, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases mul_eq_zero.mp h_first_bool with h_zero | h_one_sub
  · exact Or.inr h_zero
  · exact Or.inl ((sub_eq_zero.mp h_one_sub).symm)

/-- Construct the accepted replay evidence for a first generated Mem segment
    whose accepted row list is the active replay projection of the concrete
    Mem table.

    This fills the former `AcceptedMemoryReplayEvidence.prefixReadSound`
    obligation from extracted Mem-table constraints. It is still only the
    circuit-side replay object; the Sail timeline fields in
    `MemoryTimelineEvidence` remain the separate whole-execution boundary. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_first_segment : segment.is_first_segment = 1) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
    { rows := rows
      initialMemory :=
        ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table)
      prefixReadSound :=
        memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
          h_rows
          (activeMemReplayRowsOfTablePrefixReadSound_of_firstSegment_memTableGeneratedRowsBridge
            h_bridge h_ranges h_fixed h_first_segment) }

/-- Construct the accepted replay evidence for a continuation generated Mem
    segment whose accepted row list is the active replay projection of the
    concrete Mem table.

    This is the continuation counterpart of the first-segment constructor above:
    `prefixReadSound` is derived from concrete table facts, with the
    previous-segment carried memory entry used as the initial memory seed. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_previous_segment_addr_range : segment.previous_segment_addr.val < 2 ^ 29) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  { rows := rows
    initialMemory :=
      previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table)
    prefixReadSound :=
      memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
        h_rows
        (activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range
          h_bridge h_ranges h_fixed h_previous_segment_addr_range) }

/-- Construct continuation accepted replay evidence with the previous-segment
    address range derived from segment-global Mem range facts.

    This is the constructor shape expected by concrete full-witness integration:
    the remaining obligations are generated-row bridge facts, row range facts,
    segment distance-base range facts, fixed-column shape, and nonempty table
    evidence. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  { rows := rows
    initialMemory :=
      previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table)
    prefixReadSound :=
      memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
        h_rows
        (activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
          h_bridge h_ranges h_segment_ranges h_fixed h_nonempty) }

/-- Construct accepted replay evidence for a generated Mem segment by choosing
    the first-segment or continuation-segment initial memory from the segment
    selector.

    The constructor keeps the circuit-side replay proof local to generated Mem
    table facts. The remaining Sail-timeline fields of `MemoryTimelineEvidence`
    are still the separate residual boundary. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length)
    (h_segment_selector : segment.is_first_segment = 1 ∨ segment.is_first_segment = 0) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  if h_first_segment : segment.is_first_segment = 1 then
      acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge
        h_rows h_bridge h_ranges h_fixed h_first_segment
  else
      have _h_continuation : segment.is_first_segment = 0 := by
        rcases h_segment_selector with h_first | h_continuation
        · exact False.elim (h_first_segment h_first)
        · exact h_continuation
      acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts
        h_rows h_bridge h_ranges h_segment_ranges h_fixed h_nonempty

/-- Construct accepted replay evidence for a nonempty generated Mem segment,
    deriving the first/continuation choice from the generated segment selector
    booleanity constraint. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (h_segment_ranges : MemSegmentGeneratedRangeFacts segment)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge
    h_rows h_bridge h_ranges h_segment_ranges h_fixed h_nonempty
    (is_first_segment_eq_one_or_zero_of_memTableGeneratedRowsBridge
      h_bridge h_nonempty)

/-- Construct accepted replay evidence from the compact full-witness Mem replay
    bridge.

    The resulting `AcceptedMemoryReplayEvidence.prefixReadSound` is still
    derived from generated Mem AIR facts; the bridge merely collects the
    concrete full-witness/extractor facts that identify those AIR facts with
    the selected table. -/
@[reducible]
def acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_bridge : FullWitnessMemReplayBridge witness rows) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts
    h_bridge.rows_eq
    h_bridge.generatedRows
    h_bridge.rowRanges
    h_bridge.segmentRanges
    h_bridge.fixedColumns
    h_bridge.nonempty

/-- Construct the residual timeline evidence while deriving its accepted-replay
    subobject from the compact full-witness Mem replay bridge.

    The remaining parameters are exactly the intended whole-execution boundary:
    the selected row's split in the accepted trace, its read tag, and the
    byte-local Sail/replay agreement at the selected read. -/
@[reducible]
def memoryTimelineEvidence_of_fullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_bridge : FullWitnessMemReplayBridge witness rows)
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit : rows = priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge h_bridge).initialMemory
          priorRows)
        entry.ptr.toNat) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry :=
  { acceptedReplay := acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge h_bridge
    priorRows := priorRows
    laterRows := laterRows
    traceSplit := by
      by_cases h_first : h_bridge.segment.is_first_segment = 1
      · simpa [
          acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge,
          acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts,
          acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge,
          acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge,
          h_first
        ] using h_traceSplit
      · simpa [
          acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge,
          acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts,
          acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge,
          acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts,
          h_first
        ] using h_traceSplit
    selectedRead := h_selectedRead
    stateBytesAtPrefix := h_stateBytesAtPrefix }

/-- Concrete full-witness source for the global memory-timeline boundary.

    This keeps the circuit-side replay source explicit without mentioning the
    full Clean ensemble in the public compliance theorem signature. The
    evidence object carries generated sidecars for the raw full-witness Mem AIR
    facts that derive the replay bridge and accepted replay object; the
    remaining field is only the residual byte-local Sail timeline fact. -/
structure FullWitnessMemoryTimelineEvidence
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type 2 where
  length : ℕ
  program : Program length
  witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble
  sidecars : FullWitnessMemAirSourceRawSidecars witness
  priorRows : List (Interaction.MemoryBusEntry FGL)
  laterRows : List (Interaction.MemoryBusEntry FGL)
  traceSplit :
    (fullWitnessMemAirSourceOfRawSidecars witness sidecars).rows =
      priorRows ++ entry :: laterRows
  selectedRead :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
      some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry)
  stateBytesAtPrefix :
    ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          ((fullWitnessMemAirSourceOfRawSidecars witness sidecars).replayBridgeOfTraceSplit
            traceSplit)).initialMemory
        priorRows)
      entry.ptr.toNat

namespace FullWitnessMemoryTimelineEvidence

/-- The Mem AIR source selected by the carried raw full-witness facts.
    This is an accessor, not an independent structure field. -/
@[reducible]
noncomputable def memSource
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    FullWitnessMemAirSource evidence.witness :=
  fullWitnessMemAirSourceOfRawSidecars evidence.witness evidence.sidecars

/-- The replay bridge determined by the carried raw full-witness Mem AIR facts.
    This is an accessor, not an independent structure field. -/
@[reducible]
noncomputable def replayBridge
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    FullWitnessMemReplayBridge evidence.witness evidence.memSource.rows :=
  evidence.memSource.replayBridgeOfTraceSplit evidence.traceSplit

/-- The accepted replay object determined by the carried raw full-witness Mem
    AIR facts. This is an accessor, not an independent structure field. -/
@[reducible]
noncomputable def acceptedReplay
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge evidence.replayBridge

end FullWitnessMemoryTimelineEvidence

/-- Construct full-witness timeline evidence from sidecar-form raw Mem AIR
    source facts plus the residual Sail timeline facts.

    This is the generated-sidecar entry point. The sidecars select a concrete
    full-witness Mem AIR source via `fullWitnessMemAirSourceOfRawSidecars`; the
    remaining parameters are still the intended residual boundary: selected
    read tag and byte-local Sail/replay memory agreement. -/
@[reducible]
noncomputable def fullWitnessMemoryTimelineEvidence_of_rawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness h_sidecars).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness h_sidecars).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessMemoryTimelineEvidence state entry :=
  let memSource := fullWitnessMemAirSourceOfRawSidecars witness h_sidecars
  let bridge := memSource.replayBridgeOfTraceSplit h_traceSplit
  let timeline :=
    memoryTimelineEvidence_of_fullWitnessMemReplayBridge
      bridge priorRows laterRows h_traceSplit h_selectedRead
      h_stateBytesAtPrefix
  { length := length
    program := program
    witness := witness
    sidecars := h_sidecars
    priorRows := priorRows
    laterRows := laterRows
    traceSplit := h_traceSplit
    selectedRead := h_selectedRead
    stateBytesAtPrefix := timeline.stateBytesAtPrefix }

/-- Construct full-witness timeline evidence from raw full-witness Mem AIR
    source facts plus the residual Sail timeline facts.

    This is a compatibility constructor for callers that can still prove the
    raw sigma callback directly. It packages those raw facts into sidecar form
    before constructing the timeline evidence, matching the generated sidecar
    boundary stored by `FullWitnessMemoryTimelineEvidence`. -/
@[reducible]
noncomputable def fullWitnessMemoryTimelineEvidence_of_rawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_raw : FullWitnessMemAirSourceRawFacts witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_rawFacts h_raw)).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness
                (fullWitnessMemAirSourceRawSidecars_of_rawFacts h_raw)).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessMemoryTimelineEvidence state entry :=
  fullWitnessMemoryTimelineEvidence_of_rawSidecars
    witness
    (fullWitnessMemAirSourceRawSidecars_of_rawFacts h_raw)
    priorRows
    laterRows
    h_traceSplit
    h_selectedRead
    h_stateBytesAtPrefix

/-- Construct full-witness timeline evidence from ProverData-backed Clean
    assertion/lookup witnesses plus the residual Sail timeline facts.

    This is the preferred generated/full-ensemble entry point when the Mem
    sidecar columns live in the shared `witness.data` map. -/
@[reducible]
noncomputable def fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts h_witnessFacts)).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness
                (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
                  h_witnessFacts)).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessMemoryTimelineEvidence state entry :=
  fullWitnessMemoryTimelineEvidence_of_rawSidecars
    witness
    (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts h_witnessFacts)
    priorRows
    laterRows
    h_traceSplit
    h_selectedRead
    h_stateBytesAtPrefix

/-- Forget the concrete full-witness source, retaining the existing residual
    timeline API consumed by load proofs. -/
@[reducible]
noncomputable def FullWitnessMemoryTimelineEvidence.toMemoryTimelineEvidence
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessMemoryTimelineEvidence state entry) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry :=
  memoryTimelineEvidence_of_fullWitnessMemReplayBridge
    evidence.replayBridge
    evidence.priorRows
    evidence.laterRows
    evidence.traceSplit
    evidence.selectedRead
    evidence.stateBytesAtPrefix

noncomputable instance fullWitnessMemoryTimelineEvidenceCoe
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL} :
    CoeOut
      (FullWitnessMemoryTimelineEvidence state entry)
      (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry) where
  coe := FullWitnessMemoryTimelineEvidence.toMemoryTimelineEvidence

/-- Generated-artifact wrapper for the global memory-timeline boundary.

    The embedded `FullWitnessMemoryTimelineEvidence` is the object consumed by
    load proofs. The extra fields make the generated ProverData sidecar source
    explicit: the stored sidecars must be exactly those packaged from
    `FullWitnessMemAirSourceProverDataWitnessFacts`. -/
structure FullWitnessGeneratedTimelineEvidence
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type 2 where
  evidence : FullWitnessMemoryTimelineEvidence state entry
  witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts evidence.witness
  sidecars_eq :
    evidence.sidecars =
      fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts witnessFacts

namespace FullWitnessGeneratedTimelineEvidence

@[reducible]
noncomputable def toFullWitnessMemoryTimelineEvidence
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessGeneratedTimelineEvidence state entry) :
    FullWitnessMemoryTimelineEvidence state entry :=
  evidence.evidence

@[reducible]
noncomputable def toMemoryTimelineEvidence
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (evidence : FullWitnessGeneratedTimelineEvidence state entry) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry :=
  evidence.evidence.toMemoryTimelineEvidence

end FullWitnessGeneratedTimelineEvidence

noncomputable instance fullWitnessGeneratedTimelineEvidenceCoe
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL} :
    CoeOut
      (FullWitnessGeneratedTimelineEvidence state entry)
      (FullWitnessMemoryTimelineEvidence state entry) where
  coe := FullWitnessGeneratedTimelineEvidence.toFullWitnessMemoryTimelineEvidence

noncomputable instance fullWitnessGeneratedTimelineEvidenceMemoryTimelineCoe
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL} :
    CoeOut
      (FullWitnessGeneratedTimelineEvidence state entry)
      (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state entry) where
  coe := FullWitnessGeneratedTimelineEvidence.toMemoryTimelineEvidence

/-- Construct the generated-artifact memory-timeline boundary directly from
    ProverData-backed Clean assertion/lookup witnesses plus the residual Sail
    timeline facts. -/
@[reducible]
noncomputable def fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts h_witnessFacts)).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_stateBytesAtPrefix :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreementOnBytes state
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
          (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
            ((fullWitnessMemAirSourceOfRawSidecars witness
                (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
                  h_witnessFacts)).replayBridgeOfTraceSplit
              h_traceSplit)).initialMemory
          priorRows)
        entry.ptr.toNat) :
    FullWitnessGeneratedTimelineEvidence state entry where
  evidence :=
    fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts
      witness
      h_witnessFacts
      priorRows
      laterRows
      h_traceSplit
      h_selectedRead
      h_stateBytesAtPrefix
  witnessFacts := h_witnessFacts
  sidecars_eq := rfl

/-- The projected read-replay rows of a concrete Mem table are embedded in
    the accepted chronological memory-bus row trace. Proving this embedding
    is the global AIR/Main/Mem integration obligation; selected-row coverage
    can then be discharged from the table-local projection lemmas below. -/
def MemReadReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ memReadReplayRowsOfTable table → entry ∈ rows

/-- The projected read/write replay rows of a concrete Mem table are embedded
    in the accepted chronological memory-bus row trace. This is the stronger
    table-level embedding needed by global memory replay: writes must be
    present in the chronological trace so store replay can update memory. -/
def MemReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ memReplayRowsOfTable table → entry ∈ rows

/-- Active read/write replay rows of a concrete Mem table are embedded in the
    accepted chronological memory-bus row trace. -/
def ActiveMemReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ activeMemReplayRowsOfTable table → entry ∈ rows

/-- If the accepted chronological row list is definitionally supplied by the
    concrete mutable-Mem table replay projection, then all projected replay
    rows are embedded in that trace. This is the structural projection lemma
    used before proving the harder chronological/replay facts. -/
theorem memReplayRowsEmbeddedInTrace_of_rows_eq
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = memReplayRowsOfTable table) :
    MemReplayRowsEmbeddedInTrace table rows := by
  intro entry h_entry
  rw [h_rows]
  exact h_entry

/-- If the accepted chronological row list is definitionally supplied by the
    active mutable-Mem table replay projection, then all active projected
    replay rows are embedded in that trace. -/
theorem activeMemReplayRowsEmbeddedInTrace_of_rows_eq
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = activeMemReplayRowsOfTable table) :
    ActiveMemReplayRowsEmbeddedInTrace table rows := by
  intro entry h_entry
  rw [h_rows]
  exact h_entry

/-- Witness-level embedding obligation for mutable Mem tables. Accepted
    full-execution integration should prove this from the chronological
    AIR/Main/Mem trace: every dual-aware mutable Mem table in the full
    ensemble witness has its projected read-replay rows embedded in the
    accepted chronological memory row list. -/
def MutableMemReadReplayRowsEmbeddedInTrace
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
      MemReadReplayRowsEmbeddedInTrace table rows

/-- Witness-level embedding obligation for all mutable-Mem replay rows,
    including primary writes. This is the trace/table projection needed before
    accepted full execution can prove chronological memory replay, while the
    older read-only embedding remains available for selected-load coverage. -/
def MutableMemReplayRowsEmbeddedInTrace
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
      MemReplayRowsEmbeddedInTrace table rows

/-- A primary read projection is the polarity-preserving primary replay row
    when the concrete Mem row is a read. -/
theorem memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 0) :
    memPrimaryReadReplayEntryOfRow row = memPrimaryReplayEntryOfRow row := by
  simp [memPrimaryReadReplayEntryOfRow, memPrimaryReplayEntryOfRow, h_wr]

/-- A primary polarity-preserving replay row is a legacy read row when
    `wr = 0`. -/
theorem memoryBusTraceEventOfRow_memPrimaryReplayEntryOfRow_read_of_wr_zero
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 0) :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow
      (memPrimaryReplayEntryOfRow row) =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read
          (memPrimaryReplayEntryOfRow row)) := by
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow,
    memPrimaryReplayEntryOfRow, h_wr]

/-- A primary polarity-preserving replay row is a legacy write row when
    `wr = 1`. -/
theorem memoryBusTraceEventOfRow_memPrimaryReplayEntryOfRow_write_of_wr_one
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow
      (memPrimaryReplayEntryOfRow row) =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.write
          (memPrimaryReplayEntryOfRow row)) := by
  have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
    decide
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow,
    memPrimaryReplayEntryOfRow, h_wr, h_one_ne_neg_one]

/-- On primary Mem writes, the raw-row replay step is exactly the store
    update carried by the polarity-preserving primary replay entry. -/
theorem replayMemoryAfterBusRow_memPrimaryReplayEntryOfRow_of_wr_one
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow
      mem (memPrimaryReplayEntryOfRow row) =
        ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent mem
          (ZiskFv.ZiskCircuit.MemTrace.storeEventOfEntry
            (memPrimaryReplayEntryOfRow row)) := by
  simp [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, h_wr]

/-- A concrete Mem table row contributes its primary polarity-preserving
    projection to the table's full replay-row surface. -/
theorem mem_primary_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReplayRowsOfTable table := by
  unfold memReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its primary
    polarity-preserving projection to the table's active replay-row surface. -/
theorem active_mem_primary_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1) :
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReplayRowsOfTable table := by
  unfold activeMemReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReplayEntriesOfRow, h_sel]⟩

/-- A concrete Mem table row contributes its dual read projection to the
    table's full replay-row surface. -/
theorem mem_dual_read_replay_entry_mem_of_replay_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReplayRowsOfTable table := by
  unfold memReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its dual read projection to
    the table's active replay-row surface. -/
theorem active_mem_dual_read_replay_entry_mem_of_replay_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReplayRowsOfTable table := by
  unfold activeMemReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReplayEntriesOfRow, h_sel_dual]⟩

/-- The all-replay-row embedding implies read-only embedding for selected
    primary reads, once the selected Mem row is known to be a read. -/
theorem mem_primary_read_replay_entry_mem_of_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows := by
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (mem_primary_replay_entry_mem_of_table_row h_row)

/-- Active replay-row embedding implies read-only embedding for selected
    primary reads, once the selected Mem row is known to be a read and active. -/
theorem mem_primary_read_replay_entry_mem_of_active_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows := by
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (active_mem_primary_replay_entry_mem_of_table_row h_row h_sel)

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace from active replay-row embedding, provided the
    concrete Mem row is selected and is a read. -/
theorem mem_primary_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact
    mem_primary_read_replay_entry_mem_of_active_replay_embedded_table_row
      h_embedded h_row h_sel h_wr

/-- The all-replay-row embedding directly implies dual-read embedding. -/
theorem mem_dual_read_replay_entry_mem_of_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows :=
  h_embedded _
    (mem_dual_read_replay_entry_mem_of_replay_table_row h_row)

/-- Active replay-row embedding directly implies selected dual-read
    embedding. -/
theorem mem_dual_read_replay_entry_mem_of_active_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows :=
  h_embedded _
    (active_mem_dual_read_replay_entry_mem_of_replay_table_row
      h_row h_sel_dual)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace from active replay-row embedding, provided the
    concrete dual emission is selected. -/
theorem mem_dual_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact
    mem_dual_read_replay_entry_mem_of_active_replay_embedded_table_row
      h_embedded h_row h_sel_dual

/-- A concrete Mem table row contributes its primary read projection to the
    table's read-replay row surface. -/
theorem mem_primary_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReadReplayRowsOfTable table := by
  unfold memReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReadReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its primary read projection
    to the table's active read-replay row surface. -/
theorem active_mem_primary_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReadReplayRowsOfTable table := by
  unfold activeMemReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReadReplayEntriesOfRow, h_sel]⟩

/-- A concrete Mem table row contributes its dual read projection to the
    table's read-replay row surface. -/
theorem mem_dual_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReadReplayRowsOfTable table := by
  unfold memReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReadReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its dual read projection to
    the table's active read-replay row surface. -/
theorem active_mem_dual_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReadReplayRowsOfTable table := by
  unfold activeMemReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReadReplayEntriesOfRow, h_sel_dual]⟩

/-- If a selected legacy memory row matches a concrete primary Mem row's
    read projection, then it is covered by the table's read-replay rows. -/
theorem mem_primary_read_replay_entry_mem_of_table_row_match
    {table : Table FGL} {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ memReadReplayRowsOfTable table := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact mem_primary_read_replay_entry_mem_of_table_row h_row

/-- If a selected legacy memory row matches a concrete dual Mem row's read
    projection, then it is covered by the table's read-replay rows. -/
theorem mem_dual_read_replay_entry_mem_of_table_row_match
    {table : Table FGL} {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ memReadReplayRowsOfTable table := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact mem_dual_read_replay_entry_mem_of_table_row h_row

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace once the table's projected replay rows are
    embedded in that trace. -/
theorem mem_primary_read_replay_entry_mem_of_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReadReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows :=
  h_embedded entry
    (mem_primary_read_replay_entry_mem_of_table_row_match h_row h_match)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace once the table's projected replay rows are
    embedded in that trace. -/
theorem mem_dual_read_replay_entry_mem_of_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReadReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows :=
  h_embedded entry
    (mem_dual_read_replay_entry_mem_of_table_row_match h_row h_match)

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace from the stronger replay-row embedding, provided
    the concrete Mem row is a read. This is the selected-load adapter needed
    to avoid requiring every primary Mem row, including writes, to appear in
    the accepted trace with read polarity. -/
theorem mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (mem_primary_replay_entry_mem_of_table_row h_row)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace from the stronger replay-row embedding. Dual Mem
    projections are always read events in the replay surface. -/
theorem mem_dual_read_replay_entry_mem_of_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact h_embedded _
    (mem_dual_read_replay_entry_mem_of_replay_table_row h_row)

/-! ## Full-ensemble memory-bus row bridges -/

/-- Compose a selected Main `b` memory pull from the full ensemble with a
    selected Mem provider row.

Clean balance supplies equality of the raw PIL memory-bus messages, while
the load witness carries a legacy-entry match for the Main pull.  This
adapter translates those facts into the payload-only provider match needed
by the Mem row bridge; multiplicity polarity is intentionally not part of
the conclusion. -/
theorem mem_provider_payload_match_of_main_b_match_and_msg_eq
    {mainRow : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRow : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRow)) (-1) 2)) :
    ZiskFv.Airs.MemoryBus.matches_memory_payload entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (eval memEnv memRow)) 1 2) := by
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval mainEnv (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow))
          (-1) 2) := by
    simpa [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] using h_main_match
  have h_raw :
      (((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv).msg =
        (((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_payload :=
    ZiskFv.Airs.MemoryBus.matches_memory_payload_of_left_match_eval_emitted_provider_msg_eq
      (mainMsg := ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)
      (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)
      (mainMult := mainMult)
      (providerMult := providerMult)
      (mainEnv := mainEnv)
      (providerEnv := memEnv)
      (entry := entry)
      (mainMultiplicity := (-1 : FGL))
      (providerMultiplicity := (1 : FGL))
      (as := (2 : FGL))
      h_entry h_raw
  simpa [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] using h_payload

/-- Compose a selected Main `b` memory pull with a selected primary Mem
    provider row, viewed as the read-replay row used by chronological memory
    replay.

Unlike the provider-side Clean interaction, the replay projection uses legacy
read multiplicity `-1`, so this theorem returns full `matches_memory_entry`
for `memPrimaryReadReplayEntryOfRow`. -/
theorem mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
    {mainRow : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRow : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRow)) (-1) 2)) :
    ZiskFv.Airs.MemoryBus.matches_memory_entry entry
      (memPrimaryReadReplayEntryOfRow (eval memEnv memRow)) := by
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval mainEnv (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow))
          (-1) 2) := by
    simpa [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] using h_main_match
  have h_raw :
      (((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv).msg =
        (((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_of_left_match_eval_emitted_provider_msg_eq
      (mainMsg := ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)
      (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)
      (mainMult := mainMult)
      (providerMult := providerMult)
      (mainEnv := mainEnv)
      (providerEnv := memEnv)
      (entry := entry)
      (multiplicity := (-1 : FGL))
      (as := (2 : FGL))
      h_entry h_raw
  simpa [memPrimaryReadReplayEntryOfRow,
    ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] using h_provider

/-- Row-native full-ensemble memory projection: an active unified-Main
    memory-bus interaction has a balanced same-message counterpart on a
    concrete full-ensemble table row.

The provider side keeps the unified Main branch explicit. This mirrors
    `exists_matching_mem_component_of_active_main_interaction`: excluding
    Main memory self-matches still needs selector legality that is not yet
    available from Clean Main row soundness. -/
theorem exists_mem_provider_row_msg_eq_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      (mainInteraction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg))
            (ZiskFv.AirsClean.Main.aMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (mainTable.environment mainRow)
        ∨ mainInteraction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg))
            (ZiskFv.AirsClean.Main.bMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (mainTable.environment mainRow)
        ∨ mainInteraction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg))
            (ZiskFv.AirsClean.Main.cMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (mainTable.environment mainRow))
      ∧ ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
        providerInteraction.msg = mainInteraction.msg
          ∧ providerInteraction.mult ≠ -1
          ∧ providerInteraction.mult ≠ 0
          ∧ ∃ providerTable ∈ witness.allTables,
            providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
              ∧
              ((∃ providerRow ∈ providerTable.table,
                  providerTable.component =
                    ZiskFv.AirsClean.MemAlignReadByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.MemAlign.component
                    ∧ providerInteraction =
                      ((MemBusChannel.emitted
                        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                    ∧
                      (providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                            (ZiskFv.AirsClean.Mem.memBusMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∨ providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                            (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component =
                    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                    ∧
                    (providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.a_src_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.a_src_reg))
                          (ZiskFv.AirsClean.Main.aMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)
                      ∨ providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.b_src_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.b_src_ind
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.b_src_reg))
                          (ZiskFv.AirsClean.Main.bMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)
                      ∨ providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.store_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.store_ind
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.store_reg))
                          (ZiskFv.AirsClean.Main.cMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)))) := by
  have h_main_mem_witness :
      mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_mem_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_mem_component_of_active_main_interaction
      witness h_balanced h_main_mem_witness h_active
  refine ⟨mainRow, h_mainRow, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable, h_providerTable,
    h_providerInteraction, ?_⟩
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignReadByte_row_eval_of_interaction_mem
        h_marb h_providerInteraction
    left
    exact ⟨providerRow, h_providerRow, h_marb, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem h_mab h_providerInteraction
    right
    left
    exact ⟨providerRow, h_providerRow, h_mab, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlign_row_eval_of_interaction_mem h_memAlign h_providerInteraction
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_memAlign, h_providerEval⟩
  · rcases exists_mem_dual_row_eval_of_interaction_mem
        h_mem h_providerInteraction with h_primary | h_dual
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_primary
      right
      right
      right
      left
      exact ⟨providerRow, h_providerRow, h_mem, Or.inl h_providerEval⟩
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_dual
      right
      right
      right
      left
      exact ⟨providerRow, h_providerRow, h_mem, Or.inr h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_main_mem_row_eval_of_interaction_mem h_main h_providerInteraction
    right
    right
    right
    right
    exact ⟨providerRow, h_providerRow, h_main, h_providerEval⟩

/-- Spec-carrying variant of
    `exists_mem_provider_row_msg_eq_of_active_main_table_interaction`.

This is structural unpacking only: `witness.Spec` already states per-row
specification for every table in the full ensemble, and this lemma threads it
to the concrete Main/provider rows selected by balance. -/
theorem exists_mem_provider_row_msg_eq_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧
        (mainInteraction =
            ((MemBusChannel.emitted
              (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.a_src_mem
                + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.a_src_reg))
              (ZiskFv.AirsClean.Main.aMemMessageExpr
                (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar)).toRaw).eval
              (mainTable.environment mainRow)
          ∨ mainInteraction =
            ((MemBusChannel.emitted
              (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.b_src_mem
                + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.b_src_ind
                + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.b_src_reg))
              (ZiskFv.AirsClean.Main.bMemMessageExpr
                (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar)).toRaw).eval
              (mainTable.environment mainRow)
          ∨ mainInteraction =
            ((MemBusChannel.emitted
              (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.store_mem
                + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.store_ind
                + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.store_reg))
              (ZiskFv.AirsClean.Main.cMemMessageExpr
                (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar)).toRaw).eval
              (mainTable.environment mainRow))
        ∧ ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.MemAlignReadByte.component
                      ∧ providerInteraction =
                        ((MemBusChannel.pushed
                          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                      ∧ providerInteraction =
                        ((MemBusChannel.pushed
                          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                      ∧ providerInteraction =
                        ((MemBusChannel.emitted
                          (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                            - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                              ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                      ∧
                        (providerInteraction =
                            ((MemBusChannel.emitted
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                              (ZiskFv.AirsClean.Mem.memBusMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                              (providerTable.environment providerRow)
                          ∨ providerInteraction =
                            ((MemBusChannel.emitted
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                              (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                              (providerTable.environment providerRow)))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                      ∧
                      (providerInteraction =
                          ((MemBusChannel.emitted
                            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.a_src_mem
                              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.a_src_reg))
                            (ZiskFv.AirsClean.Main.aMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∨ providerInteraction =
                          ((MemBusChannel.emitted
                            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.b_src_mem
                              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.b_src_ind
                              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.b_src_reg))
                            (ZiskFv.AirsClean.Main.bMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∨ providerInteraction =
                          ((MemBusChannel.emitted
                            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.store_mem
                              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.store_ind
                              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.store_reg))
                            (ZiskFv.AirsClean.Main.cMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)))) := by
  obtain ⟨mainRow, h_mainRow, h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable, h_providerTable,
      h_providerInteraction, h_providerComponent⟩ :=
    exists_mem_provider_row_msg_eq_of_active_main_table_interaction
      witness h_balanced h_mainTable h_mainComponent h_mainInteraction h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main
  · rcases h_marb with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_mab with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_memAlign with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_mem with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_main with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    right
    right
    right
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩

/-- Selected-branch legacy-entry view of the full-ensemble memory-bus bridge.

    Callers that have already selected a concrete Main memory interaction can
    use this theorem to carry Clean balance through the full memory ensemble
    and obtain the legacy `matches_memory_entry` facts expected by the
    existing load/store bridge layer. The unified Main provider branch stays
    explicit; ruling it out still requires selector legality rather than a
    caller promise. -/
theorem exists_mem_provider_row_matches_entry_spec_of_active_main_eval
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL} :
    mainTable.component.Spec (mainTable.environment mainRow)
      ∧ ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
        providerInteraction.msg = mainInteraction.msg
          ∧ providerInteraction.mult ≠ -1
          ∧ providerInteraction.mult ≠ 0
          ∧ ∃ providerTable ∈ witness.allTables,
            providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
              ∧
              ((∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component =
                      ZiskFv.AirsClean.MemAlignReadByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                        multiplicity as))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                        multiplicity as))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                    ∧ providerInteraction =
                      ((MemBusChannel.emitted
                        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                        multiplicity as))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                    ∧
                      ((providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                            (ZiskFv.AirsClean.Mem.memBusMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (mainTable.environment mainRow) mainMsg)
                            multiplicity as)
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (providerTable.environment providerRow)
                              (ZiskFv.AirsClean.Mem.memBusMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                            multiplicity as))
                      ∨ (providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                            (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (mainTable.environment mainRow) mainMsg)
                            multiplicity as)
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (providerTable.environment providerRow)
                              (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                            multiplicity as))))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component =
                      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                    ∧
                    ((providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.a_src_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.a_src_reg))
                          (ZiskFv.AirsClean.Main.aMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)
                      ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (mainTable.environment mainRow) mainMsg)
                          multiplicity as)
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Main.aMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar))
                          multiplicity as))
                    ∨ (providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.b_src_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.b_src_ind
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.b_src_reg))
                          (ZiskFv.AirsClean.Main.bMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)
                      ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (mainTable.environment mainRow) mainMsg)
                          multiplicity as)
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Main.bMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar))
                          multiplicity as))
                    ∨ (providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.store_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.store_ind
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.store_reg))
                          (ZiskFv.AirsClean.Main.cMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)
                      ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (mainTable.environment mainRow) mainMsg)
                          multiplicity as)
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Main.cMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar))
                          multiplicity as))))) := by
  have h_main_mem_witness :
      mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_mem_component_of_active_main_interaction
      witness h_balanced h_main_mem_witness h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨h_mainSpec, providerInteraction, h_provider_witness, h_msg,
    h_nonpull, h_nonzero, providerTable, h_providerTable,
    h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignReadByte_row_eval_of_interaction_mem
        h_marb h_providerInteraction
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_marb, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem h_mab h_providerInteraction
    right
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_mab, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlign_row_eval_of_interaction_mem h_memAlign h_providerInteraction
    right
    right
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_memAlign, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · rcases exists_mem_dual_row_eval_of_interaction_mem
        h_mem h_providerInteraction with h_primary | h_dual
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_primary
      right
      right
      right
      left
      refine ⟨providerRow, h_providerRow,
        h_providerSpecs providerRow h_providerRow, h_mem, ?_⟩
      left
      refine ⟨h_providerEval, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_dual
      right
      right
      right
      left
      refine ⟨providerRow, h_providerRow,
        h_providerSpecs providerRow h_providerRow, h_mem, ?_⟩
      right
      refine ⟨h_providerEval, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_main_mem_row_eval_of_interaction_mem h_main h_providerInteraction
    right
    right
    right
    right
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_main, ?_⟩
    rcases h_providerEval with h_a | h_b | h_c
    · left
      refine ⟨h_a, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_a, ← h_mainEval]
      exact h_msg
    · right
      left
      refine ⟨h_b, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_b, ← h_mainEval]
      exact h_msg
    · right
      right
      refine ⟨h_c, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_c, ← h_mainEval]
      exact h_msg

/-- Named provider-row coverage produced by a balanced active Main memory-bus
    interaction.

This is the reusable form of
`exists_mem_provider_row_matches_entry_spec_of_active_main_eval`'s provider
side.  The mutable-Mem branch is still only one alternative: the alignment
tables and unified-Main branch remain visible because the current balance proof
does not rule them out. -/
def ActiveMainMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧
          ((∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.MemAlignReadByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                ∧ providerInteraction =
                  ((MemBusChannel.emitted
                    (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                      - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                    (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                ∧
                  ((providerInteraction =
                      ((MemBusChannel.emitted
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                        (ZiskFv.AirsClean.Mem.memBusMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.Mem.memBusMessageExpr
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                        multiplicity as))
                  ∨ (providerInteraction =
                      ((MemBusChannel.emitted
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                        (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                        multiplicity as))))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                ∧
                ((providerInteraction =
                    ((MemBusChannel.emitted
                      (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.a_src_mem
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.a_src_reg))
                      (ZiskFv.AirsClean.Main.aMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.aMemMessageExpr
                          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                            length program).rowInputVar))
                      multiplicity as))
                ∨ (providerInteraction =
                    ((MemBusChannel.emitted
                      (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.b_src_mem
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.b_src_ind
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.b_src_reg))
                      (ZiskFv.AirsClean.Main.bMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.bMemMessageExpr
                          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                            length program).rowInputVar))
                      multiplicity as))
                ∨ (providerInteraction =
                    ((MemBusChannel.emitted
                      (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.store_mem
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.store_ind
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.store_reg))
                      (ZiskFv.AirsClean.Main.cMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.Main.cMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar))
                      multiplicity as)))))

/-- Mutable-Mem branch of `ActiveMainMemProviderRowMatchSpec`.

This is the direct provider branch needed to identify a selected load with a
row of the witness-selected mutable Mem table. Direct full-width loads should
aim to prove this branch from the named balance coverage plus route/selector
facts. -/
def ActiveMainMutableMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
              ∧
                ((providerInteraction =
                    ((MemBusChannel.emitted
                      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                      (ZiskFv.AirsClean.Mem.memBusMessageExpr
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Mem.memBusMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                      multiplicity as))
                ∨ (providerInteraction =
                    ((MemBusChannel.emitted
                      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                      (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                      multiplicity as)))

/-- Non-mutable provider branches of `ActiveMainMemProviderRowMatchSpec`.

For subword loads, some MemAlign branches are legitimate intermediate routes
and must be followed to mutable Mem rather than discarded. For direct loads,
this predicate is the exact branch family to rule out before extracting a
mutable-Mem selected row. -/
def ActiveMainNonMutableMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧
          ((∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.MemAlignReadByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                ∧ providerInteraction =
                  ((MemBusChannel.emitted
                    (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                      - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                    (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                ∧
                ((providerInteraction =
                    ((MemBusChannel.emitted
                      (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.a_src_mem
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.a_src_reg))
                      (ZiskFv.AirsClean.Main.aMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.aMemMessageExpr
                          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                            length program).rowInputVar))
                      multiplicity as))
                ∨ (providerInteraction =
                    ((MemBusChannel.emitted
                      (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.b_src_mem
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.b_src_ind
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.b_src_reg))
                      (ZiskFv.AirsClean.Main.bMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.bMemMessageExpr
                          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                            length program).rowInputVar))
                      multiplicity as))
                ∨ (providerInteraction =
                    ((MemBusChannel.emitted
                      (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.store_mem
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.store_ind
                        + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar.rom.store_reg))
                      (ZiskFv.AirsClean.Main.cMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.cMemMessageExpr
                          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                            length program).rowInputVar))
                      multiplicity as)))))

/-- MemAlignReadByte branch of
    `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainMemAlignReadByteProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component =
                ZiskFv.AirsClean.MemAlignReadByte.component
              ∧ providerInteraction =
                ((MemBusChannel.pushed
                  (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (mainTable.environment mainRow) mainMsg)
                  multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                  multiplicity as)

/-- MemAlignByte branch of
    `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainMemAlignByteProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
              ∧ providerInteraction =
                ((MemBusChannel.pushed
                  (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (mainTable.environment mainRow) mainMsg)
                  multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                  multiplicity as)

/-- MemAlign branch of `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainMemAlignProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
              ∧ providerInteraction =
                ((MemBusChannel.emitted
                  (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                    - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                  (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (mainTable.environment mainRow) mainMsg)
                  multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                  multiplicity as)

/-- Main self-provider branch of
    `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainSelfMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component =
                ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
              ∧
              ((providerInteraction =
                  ((MemBusChannel.emitted
                    (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.a_src_mem
                      + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.a_src_reg))
                    (ZiskFv.AirsClean.Main.aMemMessageExpr
                      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.Main.aMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar))
                    multiplicity as))
              ∨ (providerInteraction =
                  ((MemBusChannel.emitted
                    (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.b_src_mem
                      + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.b_src_ind
                      + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.b_src_reg))
                    (ZiskFv.AirsClean.Main.bMemMessageExpr
                      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.Main.bMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar))
                    multiplicity as))
              ∨ (providerInteraction =
                  ((MemBusChannel.emitted
                    (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.store_mem
                      + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.store_ind
                      + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar.rom.store_reg))
                    (ZiskFv.AirsClean.Main.cMemMessageExpr
                      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.Main.cMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar))
                    multiplicity as)))

/-- Main memory-bus interactions in the full ensemble are only active pulls
    or inactive zero-multiplicity rows.

    This is the missing source-legality invariant needed to rule out the
    Main self-provider branch for direct loads. It is deliberately stated as
    an explicit witness-level obligation: the current Main `Spec` only exposes
    core Main constraints, while the needed fact depends on ROM/source flag
    legality for every unified-Main row. -/
def MainMemBusMultiplicitySound
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    Prop :=
  ∀ table ∈ witness.allTables,
    table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program →
      ∀ interaction ∈ table.interactionsWith MemBusChannel.toRaw,
        interaction.mult = -1 ∨ interaction.mult = 0

/-- Row-local ROM/source selector legality needed to make unified-Main
    memory-bus multiplicities pull-or-zero.

    The sums are stated after table evaluation because this is the exact
    proof surface consumed by `MainMemBusMultiplicitySound`: Main emits the
    three memory-bus interactions with multiplicities `-aSum`, `-bSum`, and
    `-storeSum`. -/
def MainMemBusSourceMultiplicitySound
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    Prop :=
  ∀ table ∈ witness.allTables,
    table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program →
      ∀ row ∈ table.table,
        let env := table.environment row
        (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_reg) = 1
          ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_reg) = 0)
        ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_reg) = 1
          ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_reg) = 0)
        ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_reg) = 1
          ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_reg) = 0)

/-- Concrete source selector legality for one unified-Main row. -/
def MainRomRowSourceMultiplicitySound
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL) : Prop :=
  (row.rom.a_src_mem + row.rom.a_src_reg = 1
    ∨ row.rom.a_src_mem + row.rom.a_src_reg = 0)
  ∧ (row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg = 1
    ∨ row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg = 0)
  ∧ (row.rom.store_mem + row.rom.store_ind + row.rom.store_reg = 1
    ∨ row.rom.store_mem + row.rom.store_ind + row.rom.store_reg = 0)

/-- Row-indexed source selector legality for every concrete program ROM row.

    This is closer to the production/provenance boundary than
    `MainProgramRomSourceMultiplicitySound`: for each `program i`, any concrete
    unified-Main row with that ROM message has source-selector sums `1` or `0`.
    The remaining extraction work should prove this from row-shape provenance /
    lowered instruction facts. -/
def MainProgramRomRowsSourceMultiplicitySound
    {length : ℕ} (program : Program length) : Prop :=
  ∀ i : Fin length,
    ∀ row : ZiskFv.AirsClean.Main.MainRowWithRom FGL,
      ZiskFv.AirsClean.Main.romMessage row = program i →
        MainRomRowSourceMultiplicitySound row

/-- Program-ROM source selector legality for unified-Main rows.

    This is the program-indexed source-legality burden exposed by the ROM
    lookup split: accepted row constraints prove that a unified-Main row's ROM
    message is in the program ROM, while this predicate says every such ROM row
    has the source-selector sums needed by the memory-bus proof. -/
def MainProgramRomSourceMultiplicitySound
    {length : ℕ} (program : Program length) : Prop :=
  ∀ env : Environment FGL,
    (ZiskFv.AirsClean.ZiskInstructionRom.romStaticTable length program).Spec
      (eval env
        (ZiskFv.AirsClean.Main.romMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)) →
      (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg) = 1
        ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg) = 0)
      ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg) = 1
        ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg) = 0)
      ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg) = 1
        ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg) = 0)

/-- Row-indexed program ROM source legality implies the env-shaped program-ROM
    source burden consumed by the full-ensemble split. -/
theorem mainProgramRomSourceMultiplicitySound_of_programRowsSourceMultiplicitySound
    {length : ℕ} {program : Program length}
    (h_rows : MainProgramRomRowsSourceMultiplicitySound program) :
    MainProgramRomSourceMultiplicitySound program := by
  intro env h_rom
  rcases h_rom with ⟨i, h_msg⟩
  let component := ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
  let row : ZiskFv.AirsClean.Main.MainRowWithRom FGL := component.rowInput env
  have h_eval_row : eval env component.rowInputVar = row := by
    simpa only [row, component, Air.Flat.Component.rowInput,
      Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env)
  have h_row_msg : ZiskFv.AirsClean.Main.romMessage row = program i := by
    have h_msg' :
        ZiskFv.AirsClean.Main.romMessage (eval env component.rowInputVar) =
          program i := by
      simpa only [component, ZiskFv.AirsClean.Main.eval_romMessageExpr] using h_msg
    simpa only [h_eval_row] using h_msg'
  have h_row_source := h_rows i row h_row_msg
  rcases h_row_source with ⟨h_a, h_b, h_c⟩
  have h_a_sum :
      env (component.rowInputVar.rom.a_src_mem
          + component.rowInputVar.rom.a_src_reg) =
        row.rom.a_src_mem + row.rom.a_src_reg := by
    calc
      env (component.rowInputVar.rom.a_src_mem
          + component.rowInputVar.rom.a_src_reg)
          = (eval env component.rowInputVar).rom.a_src_mem
              + (eval env component.rowInputVar).rom.a_src_reg := by
            exact ZiskFv.AirsClean.Main.eval_aSourceSumExpr env component.rowInputVar
      _ = row.rom.a_src_mem + row.rom.a_src_reg := by
            exact congrArg
              (fun r : ZiskFv.AirsClean.Main.MainRowWithRom FGL =>
                r.rom.a_src_mem + r.rom.a_src_reg) h_eval_row
  have h_b_sum :
      env (component.rowInputVar.rom.b_src_mem
          + component.rowInputVar.rom.b_src_ind
          + component.rowInputVar.rom.b_src_reg) =
        row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg := by
    calc
      env (component.rowInputVar.rom.b_src_mem
          + component.rowInputVar.rom.b_src_ind
          + component.rowInputVar.rom.b_src_reg)
          = (eval env component.rowInputVar).rom.b_src_mem
              + (eval env component.rowInputVar).rom.b_src_ind
              + (eval env component.rowInputVar).rom.b_src_reg := by
            exact ZiskFv.AirsClean.Main.eval_bSourceSumExpr env component.rowInputVar
      _ = row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg := by
            exact congrArg
              (fun r : ZiskFv.AirsClean.Main.MainRowWithRom FGL =>
                r.rom.b_src_mem + r.rom.b_src_ind + r.rom.b_src_reg) h_eval_row
  have h_c_sum :
      env (component.rowInputVar.rom.store_mem
          + component.rowInputVar.rom.store_ind
          + component.rowInputVar.rom.store_reg) =
        row.rom.store_mem + row.rom.store_ind + row.rom.store_reg := by
    calc
      env (component.rowInputVar.rom.store_mem
          + component.rowInputVar.rom.store_ind
          + component.rowInputVar.rom.store_reg)
          = (eval env component.rowInputVar).rom.store_mem
              + (eval env component.rowInputVar).rom.store_ind
              + (eval env component.rowInputVar).rom.store_reg := by
            exact ZiskFv.AirsClean.Main.eval_cSourceSumExpr env component.rowInputVar
      _ = row.rom.store_mem + row.rom.store_ind + row.rom.store_reg := by
            exact congrArg
              (fun r : ZiskFv.AirsClean.Main.MainRowWithRom FGL =>
                r.rom.store_mem + r.rom.store_ind + r.rom.store_reg) h_eval_row
  exact ⟨ by simpa only [component, h_a_sum] using h_a
        , by simpa only [component, h_b_sum] using h_b
        , by simpa only [component, h_c_sum] using h_c ⟩

/-- Accepted row constraints plus program-ROM source legality discharge the
    row-local unified-Main source-multiplicity invariant. -/
theorem mainMemBusSourceMultiplicitySound_of_constraints_and_programRomSourceMultiplicitySound
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints)
    (h_program : MainProgramRomSourceMultiplicitySound program) :
    MainMemBusSourceMultiplicitySound program witness := by
  intro table h_table h_component row h_row
  have h_row_constraints :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).operations.ConstraintsHold (table.environment row) := by
    simpa [h_component] using h_constraints table h_table row h_row
  exact h_program (table.environment row)
    (ZiskFv.AirsClean.Main.romSpec_of_componentWithRomMemAndOpBus_constraints
      length program (table.environment row) h_row_constraints)

/-- Source selector legality discharges the coarser unified-Main memory-bus
    multiplicity invariant used to rule out Main self-provider routes. -/
theorem mainMemBusMultiplicitySound_of_sourceMultiplicitySound
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_source : MainMemBusSourceMultiplicitySound program witness) :
    MainMemBusMultiplicitySound program witness := by
  intro table h_table h_component interaction h_interaction
  obtain ⟨row, h_row, h_eval⟩ :=
    exists_main_mem_row_eval_of_interaction_mem h_component h_interaction
  have h_row_source := h_source table h_table h_component row h_row
  dsimp only at h_row_source
  rcases h_row_source with ⟨h_a, h_b, h_store⟩
  rcases h_eval with h_eval | h_eval | h_eval
  · rcases h_a with h_one | h_zero
    · left
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg) = -1
      rw [h_one]
      ring
    · right
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg) = 0
      rw [h_zero]
      ring
  · rcases h_b with h_one | h_zero
    · left
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg) = -1
      rw [h_one]
      ring
    · right
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg) = 0
      rw [h_zero]
      ring
  · rcases h_store with h_one | h_zero
    · left
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg) = -1
      rw [h_one]
      ring
    · right
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg) = 0
      rw [h_zero]
      ring

/-- Main self-provider memory routes are impossible once unified-Main
    memory-bus multiplicities are known to be pull-or-zero only. -/
theorem no_activeMainSelfMemProviderRowMatchSpec_of_mainMemBusMultiplicitySound
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainMem : MainMemBusMultiplicitySound program witness) :
    ¬ ActiveMainSelfMemProviderRowMatchSpec program witness mainTable mainRow
      mainInteraction mainMsg multiplicity as := by
  intro h_self
  rcases h_self with
    ⟨providerInteraction, _h_provider_witness, _h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      providerRow, _h_providerRow, _h_providerSpec, h_component, _h_branch⟩
  have h_mult :=
    h_mainMem providerTable h_providerTable h_component providerInteraction
      h_providerInteraction
  rcases h_mult with h_pull | h_zero
  · exact h_nonpull h_pull
  · exact h_nonzero h_zero

/-- Branch split for the non-mutable active-Main provider family. -/
theorem activeMainNonMutableMemProviderRowMatchSpec_branch_cases
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_nonmutable :
      ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as) :
    ActiveMainMemAlignReadByteProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainMemAlignByteProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainMemAlignProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainSelfMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  rcases h_nonmutable with
    ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_branch⟩
  rcases h_branch with h_marb | h_mab | h_memAlign | h_main
  · left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_marb⟩
  · right; left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_mab⟩
  · right; right; left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_memAlign⟩
  · right; right; right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_main⟩

/-- Ruling out each named non-mutable branch rules out the aggregate
    non-mutable provider family. -/
theorem activeMainNonMutableMemProviderRowMatchSpec_of_no_branch
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_main :
      ¬ ActiveMainSelfMemProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as) :
    ¬ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
      mainRow mainInteraction mainMsg multiplicity as := by
  intro h_nonmutable
  rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases
      h_nonmutable with h_marb | h_mab | h_memAlign | h_main
  · exact h_no_marb h_marb
  · exact h_no_mab h_mab
  · exact h_no_memAlign h_memAlign
  · exact h_no_main h_main

/-- Split named active-Main provider coverage into mutable-Mem and
    non-mutable branches. -/
theorem activeMainMemProviderRowMatchSpec_mutable_or_nonmutable
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_match :
      ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as) :
    ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as
      ∨ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  rcases h_match with
    ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_branch⟩
  rcases h_branch with h_marb | h_mab | h_memAlign | h_mem | h_main
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inl h_marb⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inl h_mab)⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inr (Or.inl h_memAlign))⟩
  · left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_mem⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inr (Or.inr h_main))⟩

/-- Direct-load route target: if non-mutable branches are ruled out, the named
    active-Main provider coverage yields the mutable-Mem provider branch. -/
theorem activeMainMutableMemProviderRowMatchSpec_of_no_nonmutable
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_match :
      ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as)
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as) :
    ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
      mainInteraction mainMsg multiplicity as := by
  rcases activeMainMemProviderRowMatchSpec_mutable_or_nonmutable h_match with
    h_mutable | h_nonmutable
  · exact h_mutable
  · exact False.elim (h_no_nonmutable h_nonmutable)

/-- Named version of
    `exists_mem_provider_row_matches_entry_spec_of_active_main_eval`.

This is intentionally only a repackaging theorem.  It gives later memory-trace
integration a stable hook while preserving the unresolved provider-branch
disjunction. -/
theorem activeMainMemProviderRowMatchSpec_of_active_main_eval
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL} :
    mainTable.component.Spec (mainTable.environment mainRow)
      ∧ ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as := by
  simpa [ActiveMainMemProviderRowMatchSpec] using
    exists_mem_provider_row_matches_entry_spec_of_active_main_eval
      witness h_balanced h_specs h_mainTable h_mainRow h_mainInteraction
      h_mainEval h_active (multiplicity := multiplicity) (as := as)

end ZiskFv.AirsClean.FullEnsemble
