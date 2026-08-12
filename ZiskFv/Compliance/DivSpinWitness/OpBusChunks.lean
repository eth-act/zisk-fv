import ZiskFv.Compliance.DivSpinWitness.OpBusStaticInteractions

open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.DivSpinWitness

def divSpinOpBusTables0 : List (Table FGL) :=
  [divSpinBoundaryTable,
    emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlign.component]

def divSpinOpBusTables1 : List (Table FGL) :=
  [emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component,
    emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus,
    registerStepRangeRowsTable [2, 6, 5, 2, 10],
    emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component]

def divSpinOpBusTables2 : List (Table FGL) :=
  [emptyComponentTable ZiskFv.AirsClean.ArithDiv.component,
    divSpinArithTable,
    emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent]

def divSpinOpBusTables3 : List (Table FGL) :=
  [divSpinRemainderBoundTable, divSpinBinaryAddTable, divSpinMainTable]

theorem divSpinTables_opBusChunks :
    divSpinTables =
      divSpinOpBusTables0 ++ divSpinOpBusTables1 ++
        divSpinOpBusTables2 ++ divSpinOpBusTables3 := rfl

theorem divSpinOpBusTables0_flatMap :
    divSpinOpBusTables0.flatMap (·.interactionsWith OpBusChannel.toRaw) = [] := by
  simp only [divSpinOpBusTables0, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, divSpinBoundaryTable_opBusInteractions,
    divSpinMemAlignReadByte_opBus_nil, divSpinMemAlignByte_opBus_nil,
    divSpinMemAlign_opBus_nil, List.nil_append]

theorem divSpinOpBusTables1_flatMap :
    divSpinOpBusTables1.flatMap (·.interactionsWith OpBusChannel.toRaw) = [] := by
  simp only [divSpinOpBusTables1, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, divSpinMemAlignRangeSlice_opBus_nil,
    divSpinMemAlignRomSlice_opBus_nil, divSpinMem_opBus_nil,
    registerStepRangeRowsTable_interactionsWith_opBus_nil,
    divSpinSpecifiedRangesSlice_opBus_nil, List.nil_append]

theorem divSpinOpBusTables2_flatMap :
    divSpinOpBusTables2.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [divSpinArithPrimaryInteraction, divSpinArithRemainderInteraction] := by
  simp only [divSpinOpBusTables2, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, divSpinArithDiv_opBus_nil, divSpinArithTable_opBusInteractions,
    divSpinBinaryExtension_opBus_nil, List.nil_append]

theorem divSpinOpBusTables3_flatMap :
    divSpinOpBusTables3.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [ binaryOpBusInteraction divSpinRemainderBoundRow
      , binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 6)
      , binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 2)
      , mainOpBusInteraction divSpinAddiX1Row
      , mainOpBusInteraction divSpinAddiX2Row
      , mainOpBusInteraction divSpinDivRow
      , mainOpBusInteraction (divSpinJalRow 3)
      , mainOpBusInteraction (divSpinJalRow 4) ] := by
  simp only [divSpinOpBusTables3, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, divSpinRemainderBoundTable_opBusInteractions,
    divSpinBinaryAddTable_opBusInteractions, divSpinMainTable_opBusInteractions,
    divSpinBinaryAddRows, divSpinMainRows, List.map_cons, List.map_nil]
  rfl

end ZiskFv.Compliance.DivSpinWitness
