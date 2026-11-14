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
    (h_rsr : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)
    (h_binary_name : channel.name ≠ ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw.name)
    (h_extension_name : channel.name ≠ ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw.name) :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith channel)) := by
  have h_boundary : divSpinBoundaryTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact not_or_intro h_mem h_rsr
  have h_arith : divSpinArithTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa using h_op
  have h_remainder : divSpinRemainderBoundTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw, ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h_op, fun he => h_binary_name (congrArg RawChannel.name he)⟩
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
      (registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows)).interactionsWith channel = [] :=
    registerStepRangeRowsTable_interactionsWith_of_ne _ channel h_rsr
  simp only [List.cons_append, List.nil_append] at h_stepRange
  rw [divSpinWitness_tables]
  simp [h_binary_name, h_extension_name, divSpinTables, h_boundary, h_arith, h_remainder, h_binaryAdd, h_main,
    h_stepRange, h_empty]
  refine ⟨?_, ?_⟩
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    simp [h_binary_name, h_extension_name, balanceOf]

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
    (by decide) (by decide)

theorem divSpinWitness_memAlignRangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith MemAlignRangeChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinMemAlignRangeChannel_ne_memBus divSpinMemAlignRangeChannel_ne_opBus divSpinMemAlignRangeChannel_ne_registerStepRange
    (by decide) (by decide)

theorem divSpinWitness_memAlignRomChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap
        (·.interactionsWith MemAlignRomChannel.toRaw)) :=
  divSpinWitness_otherChannel_balanced _
    divSpinMemAlignRomChannel_ne_memBus divSpinMemAlignRomChannel_ne_opBus divSpinMemAlignRomChannel_ne_registerStepRange
    (by decide) (by decide)

theorem divSpinWitness_registerStepRange_interactions :
    divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) =
      divSpinBoundaryRows.map registerBoundaryRangeInteraction ++
      (([2, 6, 5, 2, 10] : List FGL).map registerStepRangeInteraction ++
        (registerBoundaryRangeValues divSpinBoundaryRows).map registerStepRangeInteraction ++
        divSpinMainRows.flatMap (fun row =>
          [mainARegStepInteraction row, mainBRegStepInteraction row,
            mainCRegStepInteraction row])) := by
  have h_ne_op : ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
    intro h
    have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
    change "SpecifiedRangesSlice102" = "OperationBus" at h_name
    simp at h_name
  have h_boundary :
      divSpinBoundaryTable.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
        divSpinBoundaryRows.map registerBoundaryRangeInteraction := by
    simpa [divSpinBoundaryTable] using
      registerBoundaryRowsTableOf_interactionsWith_registerStepRange divSpinBoundaryRows
        divSpinBoundaryRows_length divSpinBoundaryRows_enumerated emptyData
  have h_arith : divSpinArithTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  have h_remainder :
      divSpinRemainderBoundTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw, ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw]
    decide
  have h_binaryAdd :
      divSpinBinaryAddTable.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
    simpa using h_ne_op
  rw [divSpinWitness_tables]
  simp [divSpinTables, h_boundary, h_arith, h_remainder, h_binaryAdd,
    ZiskFv.Compliance.SingleAddWitness.emptyComponentTable_interactionsWith,
    registerStepRangeRowsTable_interactionsWith,
    divSpinMainTable_registerStepRangeInteractions, List.map_append, List.append_assoc]

set_option maxRecDepth 8000 in
/-- Bus-102 balance. Five of the fifteen pulls are active: each ADDI row's store (distances 2
    and 6) and all three of the DIV row's slots (5, 2, 10). The provider supplies exactly those
    five; both JAL rows emit at multiplicity 0. -/
theorem divSpinMainRegisterStepRange_balanced :
    BalancedInteractions (([2, 6, 5, 2, 10] : List FGL).map registerStepRangeInteraction ++
        divSpinMainRows.flatMap (fun row =>
          [mainARegStepInteraction row, mainBRegStepInteraction row,
            mainCRegStepInteraction row])) := by
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

theorem divSpinWitness_registerStepRangeChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)) := by

  rw [divSpinWitness_registerStepRange_interactions]
  simpa only [List.append_assoc] using
    (registerBoundaryRange_balanced divSpinBoundaryRows (([2, 6, 5, 2, 10] : List FGL).map registerStepRangeInteraction) _
      (by decide) divSpinMainRegisterStepRange_balanced)

/-- Actual bus-125 balance, including the full fixed-domain provider. -/
theorem divSpinWitness_binaryTableChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)) := by
  have h_silent_0 : (divSpinBoundaryTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinBoundaryTable) ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_silent_1 : (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignReadByte.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_2 : (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignByte.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_3 : (emptyComponentTable ZiskFv.AirsClean.MemAlign.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlign.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_4 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignRangeSlice.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_5 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignRomSlice.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_6 : (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.Mem.componentWithDualMemBus ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_7 : (registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows)).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows)) ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_silent_8 : (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.SpecifiedRangesSlice.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_9 : (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.ArithDiv.component ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_10 : (divSpinArithTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinArithTable) ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_silent_11 : (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
  have h_silent_13 : (divSpinBinaryAddTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinBinaryAddTable) ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_silent_14 : (divSpinExtensionSourceTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    exact divSpinExtensionSourceTable_other_channel _ (by decide)
  have h_silent_16 : (divSpinMainTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinMainTable) ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
    decide
  have h_list :
      divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw) =
      (ZiskFv.AirsClean.Binary.tableConsumerComponent.operations.interactionValuesWith
        ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw (Environment.fromInput divSpinRemainderBoundRow emptyData)) ++
      (divSpinBinarySourceTable).interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw := by
    have h_consumer :
        divSpinRemainderBoundTable.interactionsWith
            ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw =
          ZiskFv.AirsClean.Binary.tableConsumerComponent.operations.interactionValuesWith
            ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
            (Environment.fromInput divSpinRemainderBoundRow emptyData) := by
      change (ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable
        emptyData [divSpinRemainderBoundRow]).interactionsWith _ = _
      rw [ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable_interactionsWith
        emptyData [divSpinRemainderBoundRow] ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h := ZiskFv.AirsClean.FullEnsemble.flatMap_seventeen_consumer12_source15
      (fun table : Table FGL =>
        table.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)
      divSpinBoundaryTable
      (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus)
      (registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows))
      (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
      divSpinArithTable
      (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent)
      divSpinRemainderBoundTable divSpinBinaryAddTable
      divSpinExtensionSourceTable divSpinBinarySourceTable divSpinMainTable
      (ZiskFv.AirsClean.Binary.tableConsumerComponent.operations.interactionValuesWith
        ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
        (Environment.fromInput divSpinRemainderBoundRow emptyData))
      h_silent_0 h_silent_1 h_silent_2 h_silent_3 h_silent_4 h_silent_5
      h_silent_6 h_silent_7 h_silent_8 h_silent_9 h_silent_10 h_silent_11
      h_consumer h_silent_13 h_silent_14 h_silent_16
    exact h
  rw [h_list]
  exact balancedInteractions_of_perm divSpinBinarySource_actual_consumer_balanced List.perm_append_comm

/-- Actual bus-124 balance, including the full fixed-domain provider. -/
theorem divSpinWitness_extensionTableChannel_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)) := by
  have h_silent_0 : (divSpinBoundaryTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinBoundaryTable) ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_1 : (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignReadByte.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_2 : (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignByte.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_3 : (emptyComponentTable ZiskFv.AirsClean.MemAlign.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlign.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_4 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignRangeSlice.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_5 : (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.MemAlignRomSlice.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_6 : (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.Mem.componentWithDualMemBus ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_7 : (registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows)).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows)) ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_8 : (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.SpecifiedRangesSlice.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_9 : (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.ArithDiv.component ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_10 : (divSpinArithTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinArithTable) ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_11 : (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact emptyComponentTable_interactionsWith ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
  have h_silent_12 : (divSpinRemainderBoundTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinRemainderBoundTable) ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_13 : (divSpinBinaryAddTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinBinaryAddTable) ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_silent_15 : (divSpinBinarySourceTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    exact divSpinBinarySourceTable_other_channel _ (by decide)
  have h_silent_16 : (divSpinMainTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := divSpinMainTable) ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw
    decide
  have h_list :
      divSpinWitness.tables.flatMap (·.interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw) =
      (divSpinExtensionSourceTable).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw := by
    have h := ZiskFv.AirsClean.FullEnsemble.flatMap_seventeen_source14
      (fun table : Table FGL =>
        table.interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)
      divSpinBoundaryTable
      (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlign.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus)
      (registerStepRangeRowsTable ([2, 6, 5, 2, 10] ++ registerBoundaryRangeValues divSpinBoundaryRows))
      (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component)
      (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component)
      divSpinArithTable
      (emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent)
      divSpinRemainderBoundTable divSpinBinaryAddTable
      divSpinExtensionSourceTable divSpinBinarySourceTable divSpinMainTable
      h_silent_0 h_silent_1 h_silent_2 h_silent_3 h_silent_4 h_silent_5
      h_silent_6 h_silent_7 h_silent_8 h_silent_9 h_silent_10 h_silent_11
      h_silent_12 h_silent_13 h_silent_15 h_silent_16
    exact h
  rw [h_list]
  change BalancedInteractions
    ((ZiskFv.AirsClean.PackedVirtualTableSources.extensionProviderTable
      divSpinPackedSources emptyData).interactionsWith ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)
  rw [ZiskFv.AirsClean.PackedVirtualTableSources.extensionProviderTable_interactionsWith
    divSpinPackedSources emptyData]
  exact ZiskFv.AirsClean.FullEnsemble.extension_no_requests_balanced (fun _ => 0) (List.ofFn divSpinBinarySourceRequests)

theorem divSpinWitness_balancedChannels : divSpinWitness.BalancedChannels := by
  refine divSpinWitness.balancedChannels_of_tables divSpinEnsemble_verifier ?_
  intro channel h_channel
  simp [divSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at h_channel
  rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact divSpinWitness_extensionTableChannel_balanced
  · exact divSpinWitness_binaryTableChannel_balanced
  · exact divSpinWitness_registerStepRangeChannel_balanced
  · exact divSpinWitness_memAlignRangeChannel_balanced
  · change BalancedInteractions divSpinMemBusInteractions
    exact divSpinWitness_memBus_balanced
  · exact divSpinWitness_opBus_balanced
  · exact divSpinWitness_memAlignRomChannel_balanced
  · exact divSpinWitness_rangeChannel_balanced

end ZiskFv.Compliance.DivSpinWitness
