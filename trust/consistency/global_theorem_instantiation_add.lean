import ZiskFv.Compliance

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.Airs.OperationBus
open ZiskFv.AirsClean.Binary
open ZiskFv.AirsClean.BinaryTable
open ZiskFv.EquivCore.Promises

private def addZeroBaseIndex : BinaryTableIndex :=
  ⟨block10, by
    norm_num [tableSize, block10, block9, block8, block7, block6, block5, block4,
      block3, block2, block1, block0, minMaxBlockSize, absBlockSize, fullBlockSize,
      bitwiseBlockSize, sextBlockSize]⟩

private def addZeroFinalIndex : BinaryTableIndex :=
  ⟨block10 + p2_16, by
    norm_num [tableSize, block10, block9, block8, block7, block6, block5, block4,
      block3, block2, block1, block0, minMaxBlockSize, absBlockSize, fullBlockSize,
      bitwiseBlockSize, sextBlockSize, p2_16]⟩

private def binaryAddZeroRow : BinaryRow FGL :=
  binaryStaticRowOf false false false false false
    addZeroBaseIndex addZeroBaseIndex addZeroBaseIndex addZeroBaseIndex
    addZeroBaseIndex addZeroBaseIndex addZeroBaseIndex addZeroFinalIndex

private theorem binaryAddZeroSpec : ZiskFv.AirsClean.Binary.Spec binaryAddZeroRow := by
  norm_num [ZiskFv.AirsClean.Binary.Spec, binaryAddZeroRow, binaryStaticRowOf,
    binaryRowOf, addZeroBaseIndex, addZeroFinalIndex, binaryBOpOrSextOf,
    binaryMode32AndCIsSignedOf, rowOfIndex, lowByte, highByte, cOfIndex,
    cinOfIndex, coutOfIndex, opOfIndex, opOfBlock, posIndOfIndex, relativeIndex,
    startOfBlock, blockOfIndex, block10, block9, block8, block7, block6, block5,
    block4, block3, block2, block1, block0, minMaxBlockSize, absBlockSize,
    fullBlockSize, bitwiseBlockSize, sextBlockSize, p2_16, p2_17, p2_18, p2_19,
    ZiskFv.Airs.Tables.BinaryTable.OP_ADD]

private theorem binaryAddZeroStaticFacts : StaticBinaryTableSpecFacts binaryAddZeroRow := by
  exact ⟨⟨addZeroBaseIndex, by rfl⟩, ⟨addZeroBaseIndex, by rfl⟩,
    ⟨addZeroBaseIndex, by rfl⟩, ⟨addZeroBaseIndex, by rfl⟩,
    ⟨addZeroBaseIndex, by rfl⟩, ⟨addZeroBaseIndex, by rfl⟩,
    ⟨addZeroBaseIndex, by rfl⟩, ⟨addZeroFinalIndex, by rfl⟩⟩

private theorem a64_zero :
    ZiskFv.EquivCore.Add.binaryRowA64 binaryAddZeroRow = 0#64 := by
  norm_num [ZiskFv.EquivCore.Add.binaryRowA64, binaryAddZeroRow,
    binaryStaticRowOf, binaryRowOf, addZeroBaseIndex, addZeroFinalIndex,
    binaryBOpOrSextOf, binaryMode32AndCIsSignedOf, rowOfIndex, lowByte,
    highByte, cOfIndex, cinOfIndex, coutOfIndex, opOfIndex, opOfBlock,
    posIndOfIndex, relativeIndex, startOfBlock, blockOfIndex, block10, block9,
    block8, block7, block6, block5, block4, block3, block2, block1, block0,
    minMaxBlockSize, absBlockSize, fullBlockSize, bitwiseBlockSize,
    sextBlockSize, p2_16, p2_17, p2_18, p2_19,
    ZiskFv.Airs.Tables.BinaryTable.OP_ADD]

private theorem b64_zero :
    ZiskFv.EquivCore.Add.binaryRowB64 binaryAddZeroRow = 0#64 := by
  norm_num [ZiskFv.EquivCore.Add.binaryRowB64, binaryAddZeroRow,
    binaryStaticRowOf, binaryRowOf, addZeroBaseIndex, addZeroFinalIndex,
    binaryBOpOrSextOf, binaryMode32AndCIsSignedOf, rowOfIndex, lowByte,
    highByte, cOfIndex, cinOfIndex, coutOfIndex, opOfIndex, opOfBlock,
    posIndOfIndex, relativeIndex, startOfBlock, blockOfIndex, block10, block9,
    block8, block7, block6, block5, block4, block3, block2, block1, block0,
    minMaxBlockSize, absBlockSize, fullBlockSize, bitwiseBlockSize,
    sextBlockSize, p2_16, p2_17, p2_18, p2_19,
    ZiskFv.Airs.Tables.BinaryTable.OP_ADD]

private def emptyData : ProverData FGL := fun _ _ => #[]

private def providerRow : Array FGL := (toElements binaryAddZeroRow).toArray

private def providerTable : Air.Flat.Table FGL where
  component := staticLookupComponent
  width := staticLookupComponent.width
  table := [providerRow]
  data := emptyData
  uniform_width := by
    intro row h_row
    simp [providerRow] at h_row ⊢
    subst row
    rfl

private theorem rowInput_provider :
    staticLookupComponent.rowInput (providerTable.environment providerRow) =
      binaryAddZeroRow := by
  change staticLookupComponent.rowInput (Environment.fromArray providerRow emptyData) =
    binaryAddZeroRow
  simp [providerRow, staticLookupComponent, Air.Flat.Component.rowInput,
    ProvableType.valueFromOffset_zero_fromInput_eq]

private theorem providerTableSpec : providerTable.Spec := by
  intro row h_row
  simp [providerTable] at h_row
  subst row
  change staticLookupComponent.Spec (Environment.fromArray providerRow emptyData)
  rw [staticLookupComponent_spec]
  have h_row_input := rowInput_provider
  change staticLookupComponent.rowInput (Environment.fromArray providerRow emptyData) =
    binaryAddZeroRow at h_row_input
  rw [h_row_input]
  exact ⟨binaryAddZeroSpec, binaryAddZeroStaticFacts⟩

private theorem providerRowMem : providerRow ∈ providerTable.table := by
  simp [providerTable]

private def witnessMainRow : ZiskFv.AirsClean.Main.MainRow FGL :=
  { a_0 := 0, a_1 := 0, b_0 := 0, b_1 := 0, c_0 := 0, c_1 := 0, flag := 0,
    pc := 0, is_external_op := 1, op := ZiskFv.Trusted.OP_ADD, m32 := 0,
    ind_width := 8, set_pc := 0, jmp_offset1 := 4, jmp_offset2 := 4,
    store_pc := 0, im_high_degree_2 := 0, segment_l1 := 1 }

private def witnessMain : ZiskFv.Airs.Main.Valid_Main FGL FGL :=
  ZiskFv.AirsClean.Main.validOfRow witnessMainRow

private theorem addPins :
    ZiskFv.Compliance.MainRowPins witnessMain 0 1 ZiskFv.Trusted.OP_ADD := by
  exact ⟨rfl, rfl⟩

private theorem opBusMatch :
    matches_entry (opBus_row_Main witnessMain 0)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (staticLookupComponent.rowInput (providerTable.environment providerRow))) 1) := by
  rw [rowInput_provider]
  norm_num [matches_entry, opBus_row_Main, witnessMain, witnessMainRow,
    ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Binary.opBusMessage,
    binaryAddZeroRow, binaryStaticRowOf, binaryRowOf, addZeroBaseIndex,
    addZeroFinalIndex, binaryBOpOrSextOf, binaryMode32AndCIsSignedOf, rowOfIndex,
    lowByte, highByte, cOfIndex, cinOfIndex, coutOfIndex, opOfIndex, opOfBlock,
    posIndOfIndex, relativeIndex, startOfBlock, blockOfIndex, block10, block9,
    block8, block7, block6, block5, block4, block3, block2, block1, block0,
    minMaxBlockSize, absBlockSize, fullBlockSize, bitwiseBlockSize, sextBlockSize,
    p2_16, p2_17, p2_18, p2_19, ZiskFv.Airs.Tables.BinaryTable.OP_ADD,
    ZiskFv.Trusted.OP_ADD]

private def witnessState : PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs.insert
      Register.PC (0#64) }

private def addInput : PureSpec.AddInput :=
  { r1_val := 0#64, r2_val := 0#64, rd := 0, PC := 0#64 }

private def witnessExecRow : List (Interaction.ExecutionBusEntry FGL) :=
  [ { multiplicity := -1, pc := 0, timestamp := 0 },
    { multiplicity := 1, pc := 4, timestamp := 1 } ]

private def memRead0 : Interaction.MemoryBusEntry FGL :=
  { multiplicity := -1, as := 1, ptr := 0, value_0 := 0, value_1 := 0, timestamp := 0 }

private def memRead1 : Interaction.MemoryBusEntry FGL :=
  { multiplicity := -1, as := 1, ptr := 0, value_0 := 0, value_1 := 0, timestamp := 1 }

private def memWrite0 : Interaction.MemoryBusEntry FGL :=
  { multiplicity := 1, as := 1, ptr := 0, value_0 := 0, value_1 := 0, timestamp := 2 }

private def witnessBus : ZiskFv.Compliance.BusRows :=
  { exec_row := witnessExecRow, e0 := memRead0, e1 := memRead1, e2 := memWrite0 }

private theorem inputR1Row :
    addInput.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (staticLookupComponent.rowInput (providerTable.environment providerRow)) := by
  rw [rowInput_provider, a64_zero]
  rfl

private theorem inputR2Row :
    addInput.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (staticLookupComponent.rowInput (providerTable.environment providerRow)) := by
  rw [rowInput_provider, b64_zero]
  rfl

private theorem laneRd :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match witnessMain 0 memWrite0 := by
  simp [ZiskFv.Airs.MemoryBus.register_write_lanes_match, witnessMain, witnessMainRow,
    ZiskFv.AirsClean.Main.validOfRow, memWrite0]

private theorem promises :
    RTypePromises witnessState addInput.r1_val addInput.r2_val addInput.rd addInput.PC
      (PureSpec.execute_RTYPE_add_pure addInput).nextPC
      (regidx.Regidx 0#5) (regidx.Regidx 0#5) (regidx.Regidx 0#5)
      witnessExecRow memRead0 memRead1 memWrite0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp [witnessState, addInput]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private def addZeroEnv : ZiskFv.Compliance.OpEnvelope witnessState witnessMain 0 :=
  ZiskFv.Compliance.OpEnvelope.add_via_binary
    addInput (regidx.Regidx 0#5) (regidx.Regidx 0#5) (regidx.Regidx 0#5)
    witnessBus addPins providerTable providerRow rfl providerTableSpec providerRowMem
    opBusMatch inputR1Row inputR2Row laneRd promises

private theorem addZeroBridge : addZeroEnv.aeneasBridgeTrust := by
  exact ⟨inputR1Row, inputR2Row⟩

private theorem addZeroMemoryConstruction :
    addZeroEnv.memoryTimelineConstructionEvidence := by
  trivial

private theorem addZeroNoKnownDefect :
    ZiskFv.Compliance.Defects.NoKnownDefect addZeroEnv := by
  intro id h_block
  cases id <;>
    simp [ZiskFv.Compliance.Defects.Blocks,
      ZiskFv.Compliance.Defects.MaliciousSignedMulWitnessShape,
      ZiskFv.Compliance.Defects.ArithDivDynamicWitnessShape,
      ZiskFv.Compliance.Defects.FenceKnownGoodShape, addZeroEnv] at h_block

theorem global_theorem_instantiation_add :
    addZeroEnv.exec_eq :=
  ZiskFv.Compliance.zisk_riscv_compliant_program_bus
    addZeroEnv addZeroBridge addZeroMemoryConstruction addZeroNoKnownDefect

#print axioms global_theorem_instantiation_add

end ZiskFv.TrustConsistency
