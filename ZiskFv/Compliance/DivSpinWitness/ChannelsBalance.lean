import ZiskFv.Compliance.DivSpinWitness.MemBusBalance

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

private theorem divSpinWitness_otherChannel_balanced
    (channel : RawChannel FGL)
    (h_mem : channel ≠ MemBusChannel.toRaw)
    (h_op : channel ≠ OpBusChannel.toRaw)
    (h_rsr : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith channel)) := by
  have h_boundary : divSpinBoundaryTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw]
    simpa using h_mem
  have h_arith : divSpinArithTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa using h_op
  have h_remainder : divSpinRemainderBoundTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa using h_op
  have h_binaryAdd : divSpinBinaryAddTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa using h_op
  have h_main : divSpinMainTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · exact h_mem h
    · exact h_op h
    · exact h_rsr h
  have h_empty (component : Component FGL) :
      (ZiskFv.Compliance.SingleAddWitness.emptyComponentTable component).interactionsWith
        channel = [] :=
    ZiskFv.Compliance.SingleAddWitness.emptyComponentTable_interactionsWith component channel
  have h_stepRange :
      (registerStepRangeRowsTable [2, 6, 5, 2, 10]).interactionsWith channel = [] :=
    registerStepRangeRowsTable_interactionsWith_of_ne _ channel h_rsr
  rw [divSpinWitness_tables]
  simp [divSpinTables, h_boundary, h_arith, h_remainder, h_binaryAdd, h_main,
    h_stepRange, h_empty]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [balanceOf]

private theorem divSpinRangeChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  exact (by decide : "SpecifiedRangesSlice103" ≠ "MemoryBus") h_name

private theorem divSpinRangeChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "OperationBus" at h_name
  exact (by decide : "SpecifiedRangesSlice103" ≠ "OperationBus") h_name

private theorem divSpinMemAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "MemoryBus" at h_name
  exact (by decide : "MemAlignRange107" ≠ "MemoryBus") h_name

private theorem divSpinMemAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "OperationBus" at h_name
  exact (by decide : "MemAlignRange107" ≠ "OperationBus") h_name

private theorem divSpinMemAlignRomChannel_ne_memBus :
    MemAlignRomChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRom133" = "MemoryBus" at h_name
  exact (by decide : "MemAlignRom133" ≠ "MemoryBus") h_name

private theorem divSpinMemAlignRomChannel_ne_opBus :
    MemAlignRomChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRom133" = "OperationBus" at h_name
  exact (by decide : "MemAlignRom133" ≠ "OperationBus") h_name

private theorem divSpinRangeChannel_ne_registerStepRange :
    SpecifiedRangesSliceChannel.toRaw ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "SpecifiedRangesSlice102" at h_name
  simp at h_name

private theorem divSpinMemAlignRangeChannel_ne_registerStepRange :
    MemAlignRangeChannel.toRaw ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRange107" = "SpecifiedRangesSlice102" at h_name
  simp at h_name

private theorem divSpinMemAlignRomChannel_ne_registerStepRange :
    MemAlignRomChannel.toRaw ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRom133" = "SpecifiedRangesSlice102" at h_name
  simp at h_name

theorem divSpinWitness_rangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinRangeChannel_ne_memBus divSpinRangeChannel_ne_opBus divSpinRangeChannel_ne_registerStepRange

theorem divSpinWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith MemAlignRangeChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinMemAlignRangeChannel_ne_memBus divSpinMemAlignRangeChannel_ne_opBus divSpinMemAlignRangeChannel_ne_registerStepRange

theorem divSpinWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith MemAlignRomChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinMemAlignRomChannel_ne_memBus divSpinMemAlignRomChannel_ne_opBus divSpinMemAlignRomChannel_ne_registerStepRange

theorem divSpinWitness_registerStepRange_interactions :
    divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) =
      ([2, 6, 5, 2, 10] : List FGL).map registerStepRangeInteraction ++
        divSpinMainRows.flatMap (fun row =>
          [mainARegStepInteraction row, mainBRegStepInteraction row,
            mainCRegStepInteraction row]) := by
  have h_ne_op : ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
    intro h
    have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
    change "SpecifiedRangesSlice102" = "OperationBus" at h_name
    simp at h_name
  have h_boundary :
      divSpinBoundaryTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] :=
    ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_registerStepRange_nil
      rfl
  have h_arith : divSpinArithTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  have h_remainder :
      divSpinRemainderBoundTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  have h_binaryAdd :
      divSpinBinaryAddTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  rw [divSpinWitness_tables]
  simp [divSpinTables, h_boundary, h_arith, h_remainder, h_binaryAdd,
    ZiskFv.Compliance.SingleAddWitness.emptyComponentTable_interactionsWith,
    registerStepRangeRowsTable_interactionsWith,
    divSpinMainTable_registerStepRangeInteractions]

set_option maxRecDepth 8000 in
/-- Bus-102 balance. Five of the fifteen pulls are active: each ADDI row's store (distances 2
    and 6) and all three of the DIV row's slots (5, 2, 10). The provider supplies exactly those
    five; both JAL rows emit at multiplicity 0. -/
theorem divSpinWitness_registerStepRangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)) := by
  rw [divSpinWitness_registerStepRange_interactions]
  refine Air.Flat.balancedInteractions_of_present ?_
    (([0, 1, 2, 4, 5, 6, 10, 12, 13, 14, 16, 17, 18] : List FGL).map
      (fun v => (registerStepRangeInteraction v).msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    revert h_interaction
    simp only [divSpinMainRows, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
  · intro msg h_msg
    revert h_msg
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl) <;> decide

theorem divSpinWitness_balancedChannels : divSpinWitness.BalancedChannels := by
  refine divSpinWitness.balancedChannels_of_tables divSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [divSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl
  · exact divSpinWitness_registerStepRangeChannel_balanced
  · exact divSpinWitness_memAlignRangeChannel_balanced
  · change BalancedInteractions divSpinMemBusInteractions
    exact divSpinWitness_memBus_balanced
  · exact divSpinWitness_opBus_balanced
  · exact divSpinWitness_memAlignRomChannel_balanced
  · exact divSpinWitness_rangeChannel_balanced

end ZiskFv.Compliance.DivSpinWitness
