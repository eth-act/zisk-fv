import ZiskFv.Compliance.DivSpinWitness.Definitions

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option Elab.async false

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.DivSpinWitness

attribute [local simp] mainFixedColumns_segment_l1_first
  mainFixedColumns_segment_l1_nonfirst mainFixedColumns_main_step_eq_index
  mainFixedCapacity

theorem divSpinMain_pcHandshake_addi_x1_x2 :
    transitionBetween divSpinAddiX1Row divSpinAddiX2Row := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween,
    divSpinAddiX1Row, divSpinAddiX2Row,
    divSpinAddiX1RowWithLast, divSpinAddiX2RowWithLast,
    divSpinAddiX1RowTemplate, divSpinAddiX2RowTemplate,
    divSpinAddiX1ProgramRow, divSpinAddiX2ProgramRow, divSpinAddiBits,
    divSpinAddiFree, divSpinAddiBits, ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
    mainRomRowOf,
    ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterRow,
    ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterAccesses,
    ZiskFv.Compliance.RegisterMemBusBalance.withMainRegisterPrevious]

theorem divSpinMain_pcHandshake_addi_x2_div :
    transitionBetween divSpinAddiX2Row divSpinDivRow := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween,
    divSpinAddiX2Row, divSpinAddiX2RowWithLast,
    divSpinAddiX2RowTemplate, divSpinDivRow, divSpinDivRowTemplate,
    divSpinAddiX2ProgramRow, divSpinDivProgramRow, divSpinAddiBits,
    divSpinDivBits, divSpinAddiFree, divSpinAddiBits,
    ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits, mainRomRowOf,
    ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterRow,
    ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterAccesses,
    ZiskFv.Compliance.RegisterMemBusBalance.withMainRegisterPrevious]

theorem divSpinMain_pcHandshake_div_jal :
    transitionBetween divSpinDivRow (divSpinJalRow 3) := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween,
    divSpinDivRow, divSpinJalRow,
    divSpinJalProgramRow, divSpinDivProgramRow, divSpinDivBits,
    ZiskFv.Compliance.AddSpinWitness.addSpinJalRow,
    ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow,
    ZiskFv.Compliance.AddSpinWitness.addSpinJalBits, mainRomRowOf]

theorem divSpinMain_pcHandshake_jal_jal :
    transitionBetween (divSpinJalRow 3) (divSpinJalRow 4) := by
  simp [transitionBetween, sourceCCopyBetween, pcHandshakeBetween,
    divSpinJalRow, divSpinJalProgramRow,
    ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow,
    ZiskFv.Compliance.AddSpinWitness.addSpinJalBits,
    ZiskFv.Compliance.AddSpinWitness.addSpinJalFreeCols, mainRomRowOf]
  ring

theorem divSpinAddiX1Main_proverAssumptions :
    (componentWithRomMemAndOpBus 4 divSpinProgram).circuit.ProverAssumptions
      divSpinAddiX1Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨0, by decide⟩, divSpinAddiBits, MainRomExecKind.external false 6 0,
    { divSpinAddiFree 0 6 with segment_l1 := 1 }, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, divSpinAddiBits,
      ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits]
  · simp [MainRomSourceGuard, divSpinProgram, divSpinAddiX1ProgramRow,
      divSpinAddiBits]
  · simp [MainRomAddressGuard, divSpinAddiBits]
  · simp [divSpinAddiX1Row, divSpinAddiX1RowWithLast,
      divSpinAddiX1RowTemplate, divSpinProgram, divSpinAddiX1ProgramRow,
      divSpinAddiBits, mainRomRowOf, divSpinAddiFree, divSpinRegisterInitial,
      ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterRow,
      ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterAccesses,
      ZiskFv.Compliance.RegisterMemBusBalance.withMainRegisterPrevious]

theorem divSpinAddiX2Main_proverAssumptions :
    (componentWithRomMemAndOpBus 4 divSpinProgram).circuit.ProverAssumptions
      divSpinAddiX2Row emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨1, by decide⟩, divSpinAddiBits, MainRomExecKind.external false 2 0,
    divSpinAddiFree 1 2, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, divSpinAddiBits,
      ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits]
  · simp [MainRomSourceGuard, divSpinProgram, divSpinAddiX2ProgramRow,
      divSpinAddiBits]
  · simp [MainRomAddressGuard, divSpinAddiBits]
  · simp [divSpinAddiX2Row, divSpinAddiX2RowWithLast,
      divSpinAddiX2RowTemplate, divSpinProgram, divSpinAddiX2ProgramRow,
      divSpinAddiBits, mainRomRowOf, divSpinAddiFree, divSpinRegisterInitial,
      ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterRow,
      ZiskFv.Compliance.RegisterMemBusBalance.materializeMainRegisterAccesses,
      ZiskFv.Compliance.RegisterMemBusBalance.withMainRegisterPrevious]

theorem divSpinDivMain_proverAssumptions :
    (componentWithRomMemAndOpBus 4 divSpinProgram).circuit.ProverAssumptions
      divSpinDivRow emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨2, by decide⟩, divSpinDivBits, MainRomExecKind.external false 3 0,
    { a_0 := 6
      a_1 := 0
      b_0 := 2
      b_1 := 0
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := 2
      a_reg_prev_mem_step := divSpinAddiX1RowWithLast.1.timestamp
      b_reg_prev_mem_step := divSpinAddiX2RowWithLast.1.timestamp
      store_reg_prev_mem_step := (divSpinRegisterInitial 3).timestamp
      store_reg_prev_value_0 := (divSpinRegisterInitial 3).value_0
      store_reg_prev_value_1 := (divSpinRegisterInitial 3).value_1 },
    ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [MainRomExecKind.Coherent, divSpinDivBits]
  · simp [MainRomSourceGuard, divSpinProgram, divSpinDivProgramRow,
      divSpinDivBits]
  · simp [MainRomAddressGuard, divSpinDivBits]
  · simp [divSpinDivRow, divSpinDivRowTemplate, divSpinProgram,
      divSpinDivProgramRow, divSpinDivBits, mainRomRowOf, divSpinRegisterInitial,
      ZiskFv.Compliance.RegisterMemBusBalance.withMainRegisterPrevious]

theorem divSpinJalMain_proverAssumptions (step : FGL) :
    (componentWithRomMemAndOpBus 4 divSpinProgram).circuit.ProverAssumptions
      (divSpinJalRow step) emptyData (ProverHint.empty FGL) := by
  refine ⟨⟨3, by decide⟩, ZiskFv.Compliance.AddSpinWitness.addSpinJalBits,
    MainRomExecKind.internalFlag, divSpinJalFreeCols step,
    ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [MainRomExecKind.Coherent, divSpinProgram, divSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalBits, ZiskFv.Trusted.OP_FLAG]
  · simp [MainRomSourceGuard, divSpinProgram, divSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalBits]
  · simp [MainRomAddressGuard,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalBits]
  · simp [divSpinJalRow, divSpinProgram, divSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalBits,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalFreeCols, mainRomRowOf]

private theorem divSpinMain_constraintsHold_materialize
    (index : Nat) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (h_assumptions :
      (componentWithRomMemAndOpBus 4 divSpinProgram).circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 4 divSpinProgram).operations.ConstraintsHold
      (Environment.fromArray
        (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  apply component_constraintsHold_of_proverAssumptions_at_data
    (componentWithRomMemAndOpBus 4 divSpinProgram)
    (Environment.fromArray
      (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
    row emptyData
  · rfl
  · exact eval_mainRawRow_materialize
      index emptyData row h_segment_l1 h_main_step
  · rfl
  · exact h_assumptions

theorem divSpinMainTable_constraints : divSpinMainTable.Constraints := by
  change ∀ arr ∈
      [ mainFixedColumns.materialize 0 (mainRawRow divSpinAddiX1Row)
      , mainFixedColumns.materialize 1 (mainRawRow divSpinAddiX2Row)
      , mainFixedColumns.materialize 2 (mainRawRow divSpinDivRow)
      , mainFixedColumns.materialize 3 (mainRawRow (divSpinJalRow 3))
      , mainFixedColumns.materialize 4 (mainRawRow (divSpinJalRow 4)) ],
      (componentWithRomMemAndOpBus 4 divSpinProgram).operations.ConstraintsHold
        (Environment.fromArray arr emptyData)
  intro arr h_arr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_arr
  rcases h_arr with rfl | rfl | rfl | rfl | rfl
  · exact divSpinMain_constraintsHold_materialize 0 divSpinAddiX1Row
      (by simp [divSpinAddiX1Row, divSpinAddiX1RowWithLast,
        divSpinAddiX1RowTemplate, mainRomRowOf, divSpinAddiFree])
      (by simp [divSpinAddiX1Row, divSpinAddiX1RowWithLast,
        divSpinAddiX1RowTemplate, mainRomRowOf, divSpinAddiFree])
      divSpinAddiX1Main_proverAssumptions
  · exact divSpinMain_constraintsHold_materialize 1 divSpinAddiX2Row
      (by simp [divSpinAddiX2Row, divSpinAddiX2RowWithLast,
        divSpinAddiX2RowTemplate, mainRomRowOf, divSpinAddiFree])
      (by simp [divSpinAddiX2Row, divSpinAddiX2RowWithLast,
        divSpinAddiX2RowTemplate, mainRomRowOf, divSpinAddiFree])
      divSpinAddiX2Main_proverAssumptions
  · exact divSpinMain_constraintsHold_materialize 2 divSpinDivRow
      (by simp [divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf])
      (by simp [divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf])
      divSpinDivMain_proverAssumptions
  · exact divSpinMain_constraintsHold_materialize 3 (divSpinJalRow 3)
      (by simp [divSpinJalRow, mainRomRowOf])
      (by simp [divSpinJalRow, mainRomRowOf])
      (divSpinJalMain_proverAssumptions 3)
  · exact divSpinMain_constraintsHold_materialize 4 (divSpinJalRow 4)
      (by simp [divSpinJalRow, mainRomRowOf])
      (by simp [divSpinJalRow, mainRomRowOf])
      (divSpinJalMain_proverAssumptions 4)

theorem divSpinBoundaryTable_constraints : divSpinBoundaryTable.Constraints :=
  registerBoundaryRowsTableOf_constraints divSpinBoundaryRows

@[simp] theorem divSpinMainTable_length : divSpinMainTable.length = 5 := rfl

theorem divSpinMainTable_transitions : divSpinMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  fin_cases index
  · change transitionBetween _
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 0 (mainRawRow divSpinAddiX1Row)) emptyData)
        (varFromOffset MainRowWithRom 0))
    rw [eval_mainRawRow_materialize 0 emptyData divSpinAddiX1Row
      (by simp [divSpinAddiX1Row, divSpinAddiX1RowTemplate, mainRomRowOf,
        divSpinAddiFree])
      (by simp [divSpinAddiX1Row, divSpinAddiX1RowTemplate, mainRomRowOf,
        divSpinAddiFree])]
    simp [Table.previousEnvironment, divSpinMainTable, mainRowsTable,
      divSpinMainRows, transitionBetween, sourceCCopyBetween, pcHandshakeBetween,
      divSpinAddiX1Row, divSpinAddiX1RowWithLast, divSpinAddiX1RowTemplate,
      divSpinAddiBits, ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
      mainRomRowOf, divSpinAddiFree, divSpinRegisterInitial]
  · change transitionBetween
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 0 (mainRawRow divSpinAddiX1Row)) emptyData)
        (varFromOffset MainRowWithRom 0))
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 1 (mainRawRow divSpinAddiX2Row)) emptyData)
        (varFromOffset MainRowWithRom 0))
    rw [eval_mainRawRow_materialize 0 emptyData divSpinAddiX1Row
        (by simp [divSpinAddiX1Row, divSpinAddiX1RowTemplate, mainRomRowOf,
          divSpinAddiFree])
        (by simp [divSpinAddiX1Row, divSpinAddiX1RowTemplate, mainRomRowOf,
          divSpinAddiFree]),
      eval_mainRawRow_materialize 1 emptyData divSpinAddiX2Row
        (by simp [divSpinAddiX2Row, divSpinAddiX2RowTemplate, mainRomRowOf,
          divSpinAddiFree])
        (by simp [divSpinAddiX2Row, divSpinAddiX2RowTemplate, mainRomRowOf,
          divSpinAddiFree])]
    exact divSpinMain_pcHandshake_addi_x1_x2
  · change transitionBetween
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 1 (mainRawRow divSpinAddiX2Row)) emptyData)
        (varFromOffset MainRowWithRom 0))
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 2 (mainRawRow divSpinDivRow)) emptyData)
        (varFromOffset MainRowWithRom 0))
    rw [eval_mainRawRow_materialize 1 emptyData divSpinAddiX2Row
        (by simp [divSpinAddiX2Row, divSpinAddiX2RowTemplate, mainRomRowOf,
          divSpinAddiFree])
        (by simp [divSpinAddiX2Row, divSpinAddiX2RowTemplate, mainRomRowOf,
          divSpinAddiFree]),
      eval_mainRawRow_materialize 2 emptyData divSpinDivRow
        (by simp [divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf])
        (by simp [divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf])]
    exact divSpinMain_pcHandshake_addi_x2_div
  · change transitionBetween
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 2 (mainRawRow divSpinDivRow)) emptyData)
        (varFromOffset MainRowWithRom 0))
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 3 (mainRawRow (divSpinJalRow 3))) emptyData)
        (varFromOffset MainRowWithRom 0))
    rw [eval_mainRawRow_materialize 2 emptyData divSpinDivRow
        (by simp [divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf])
        (by simp [divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf]),
      eval_mainRawRow_materialize 3 emptyData (divSpinJalRow 3)
        (by simp [divSpinJalRow, mainRomRowOf])
        (by simp [divSpinJalRow, mainRomRowOf])]
    exact divSpinMain_pcHandshake_div_jal
  · change transitionBetween
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 3 (mainRawRow (divSpinJalRow 3))) emptyData)
        (varFromOffset MainRowWithRom 0))
      (Eval.eval
        (Environment.fromArray
          (mainFixedColumns.materialize 4 (mainRawRow (divSpinJalRow 4))) emptyData)
        (varFromOffset MainRowWithRom 0))
    rw [eval_mainRawRow_materialize 3 emptyData (divSpinJalRow 3)
        (by simp [divSpinJalRow, mainRomRowOf])
        (by simp [divSpinJalRow, mainRomRowOf]),
      eval_mainRawRow_materialize 4 emptyData (divSpinJalRow 4)
        (by simp [divSpinJalRow, mainRomRowOf])
        (by simp [divSpinJalRow, mainRomRowOf])]
    exact divSpinMain_pcHandshake_jal_jal

theorem divSpinMainTable_cyclicSuccessorTransitions :
    divSpinMainTable.CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  simp [divSpinMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable,
    componentWithRomMemAndOpBus]

def divSpinEnsemble : Ensemble FGL unit :=
  (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble 4 divSpinProgram).ensemble

def divSpinTables : List (Table FGL) :=
  [ divSpinBoundaryTable
  , emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlign.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component
  , emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component
  , emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
  -- bus-102: five of the fifteen pulls are active -- each ADDI row's store (2 and 6) and all
  -- three of the DIV row's slots (a 5, b 2, c 10). Both JAL rows emit at multiplicity 0.
  , registerStepRangeRowsTable [2, 6, 5, 2, 10]
  , emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
  , emptyComponentTable ZiskFv.AirsClean.ArithDiv.component
  , divSpinArithTable
  , emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  , divSpinRemainderBoundTable
  , divSpinBinaryAddTable
  , divSpinMainTable ]

def divSpinWitness : EnsembleWitness divSpinEnsemble where
  tables := divSpinTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [divSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
      divSpinTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
      SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable, registerStepRangeRowsTable,
      divSpinMainTable, mainRowsTable]
  same_circuits := by
    intro i hi
    have hi' : i < 15 := by
      simpa [divSpinTables] using hi
    interval_cases i <;>
      simp [divSpinEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
        divSpinTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
        SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable, registerStepRangeRowsTable,
        divSpinBoundaryTable, registerBoundaryRowsTableOf, emptyComponentTable,
        divSpinArithTable, divSpinRemainderBoundTable, binarySingleRowTable,
        divSpinBinaryAddTable, binaryAddRowsTable, divSpinMainTable, mainRowsTable]
  same_data := by
    intro table h_table
    simp [divSpinTables, divSpinBoundaryTable, registerBoundaryRowsTableOf,
      emptyComponentTable, divSpinArithTable, divSpinRemainderBoundTable,
      binarySingleRowTable, divSpinBinaryAddTable, binaryAddRowsTable,
      divSpinMainTable, mainRowsTable] at h_table
    rcases h_table with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl

theorem divSpinEnsemble_verifier :
    divSpinEnsemble.verifier = .empty FGL unit :=
  (ZiskFv.AirsClean.FullEnsemble.fullRv64imSoundEnsemble
    4 divSpinProgram).verifier_empty

theorem divSpinWitness_table_constraints :
    ∀ table ∈ divSpinWitness.tables, table.Constraints := by
  intro table h_table
  simp [divSpinWitness, divSpinTables] at h_table
  rcases h_table with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact divSpinBoundaryTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRangeSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRomSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · refine registerStepRangeRowsTable_constraints _ ?_
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;>
      simp [AirsClean.RangeTables.rangeTable24, AirsClean.RangeTables.rangeStaticTable]
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.SpecifiedRangesSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · rw [Table.Constraints]
    intro arr h_arr
    change arr ∈ [divSpinArithRowArray] at h_arr
    simp only [List.mem_singleton] at h_arr
    subst arr
    change ZiskFv.AirsClean.ArithMul.componentComplete.operations.ConstraintsHold
      (Environment.fromInput divSpinArithRow emptyData)
    exact divSpinArithRow_constraints
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  · exact divSpinRemainderBoundTable_constraints
  · exact divSpinBinaryAddTable_constraints
  · exact divSpinMainTable_constraints

theorem divSpinWitness_constraints : divSpinWitness.Constraints :=
  divSpinWitness.constraints_of_tables divSpinEnsemble_verifier
    divSpinWitness_table_constraints

theorem divSpinWitness_transitions : divSpinWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [divSpinWitness, divSpinTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [divSpinBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · rw [Table.TransitionConstraints]
      intro index
      simp [registerStepRangeRowsTable, ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithDiv.component
    · rw [Table.TransitionConstraints]
      intro index
      simp [divSpinArithTable, ZiskFv.AirsClean.ArithMul.componentComplete]
    · exact emptyComponentTable_transitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [divSpinRemainderBoundTable, binarySingleRowTable,
        ZiskFv.AirsClean.Binary.staticLookupComponent]
    · rw [Table.TransitionConstraints]
      intro index
      simp [divSpinBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact divSpinMainTable_transitions

theorem divSpinWitness_cyclicSuccessorTransitions :
    divSpinWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp [divSpinWitness, divSpinTables] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [divSpinBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [registerStepRangeRowsTable, ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.ArithDiv.component
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [divSpinArithTable, ZiskFv.AirsClean.ArithMul.componentComplete]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [divSpinRemainderBoundTable, binarySingleRowTable,
        ZiskFv.AirsClean.Binary.staticLookupComponent]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [divSpinBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact divSpinMainTable_cyclicSuccessorTransitions


end ZiskFv.Compliance.DivSpinWitness

