import ZiskFv.Compliance.DivSpinWitness.OpBusStaticInteractions

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinOpBus_interactions :
    divSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) =
      [ divSpinArithPrimaryInteraction
      , divSpinArithRemainderInteraction
      , binaryOpBusInteraction divSpinRemainderBoundRow
      , binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 6)
      , binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 2)
      , mainOpBusInteraction divSpinAddiX1Row
      , mainOpBusInteraction divSpinAddiX2Row
      , mainOpBusInteraction divSpinDivRow
      , mainOpBusInteraction (divSpinJalRow 3)
      , mainOpBusInteraction (divSpinJalRow 4) ] := by
  rw [divSpinWitness_tables]
  simp only [divSpinTables, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [divSpinBoundaryTable_opBusInteractions,
    emptyComponentTable_interactionsWith, List.nil_append]
  rw [divSpinArithTable_opBusInteractions,
    divSpinRemainderBoundTable_opBusInteractions,
    divSpinBinaryAddTable_opBusInteractions,
    divSpinMainTable_opBusInteractions]
  simp [divSpinBinaryAddRows, divSpinMainRows]

end ZiskFv.Compliance.DivSpinWitness
