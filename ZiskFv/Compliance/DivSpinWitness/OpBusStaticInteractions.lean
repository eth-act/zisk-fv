import ZiskFv.Compliance.DivSpinWitness.OpBusEmptyInteractions

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinWitness_tables : divSpinWitness.tables = divSpinTables := rfl

theorem divSpinBoundaryTable_opBusInteractions :
    divSpinBoundaryTable.interactionsWith OpBusChannel.toRaw = [] :=
  ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil rfl

theorem divSpinRemainderBoundTable_opBusInteractions :
    divSpinRemainderBoundTable.interactionsWith OpBusChannel.toRaw =
      [binaryOpBusInteraction divSpinRemainderBoundRow] :=
  binarySingleRowTable_interactionsWith_opBus _

theorem divSpinBinaryAddTable_opBusInteractions :
    divSpinBinaryAddTable.interactionsWith OpBusChannel.toRaw =
      divSpinBinaryAddRows.flatMap (fun row => [binaryAddOpBusInteraction row]) :=
  binaryAddRowsTable_interactionsWith_opBus _

end ZiskFv.Compliance.DivSpinWitness
