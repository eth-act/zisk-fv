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
    (h_op : channel ≠ OpBusChannel.toRaw) :
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
    change channel ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => h.elim h_mem h_op
  have h_empty (component : Component FGL) :
      (ZiskFv.Compliance.SingleAddWitness.emptyComponentTable component).interactionsWith
        channel = [] :=
    ZiskFv.Compliance.SingleAddWitness.emptyComponentTable_interactionsWith component channel
  rw [divSpinWitness_tables]
  simp [divSpinTables, h_boundary, h_arith, h_remainder, h_binaryAdd, h_main,
    h_empty]
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

theorem divSpinWitness_rangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith SpecifiedRangesSliceChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinRangeChannel_ne_memBus divSpinRangeChannel_ne_opBus

theorem divSpinWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith MemAlignRangeChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinMemAlignRangeChannel_ne_memBus divSpinMemAlignRangeChannel_ne_opBus

theorem divSpinWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith MemAlignRomChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinMemAlignRomChannel_ne_memBus divSpinMemAlignRomChannel_ne_opBus

theorem divSpinWitness_balancedChannels : divSpinWitness.BalancedChannels := by
  refine divSpinWitness.balancedChannels_of_tables divSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [divSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl
  · exact divSpinWitness_memAlignRangeChannel_balanced
  · change BalancedInteractions divSpinMemBusInteractions
    exact divSpinWitness_memBus_balanced
  · exact divSpinWitness_opBus_balanced
  · exact divSpinWitness_memAlignRomChannel_balanced
  · exact divSpinWitness_rangeChannel_balanced

end ZiskFv.Compliance.DivSpinWitness
