import ZiskFv.Compliance.DivSpinWitness.OpBusMainInteractions

open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinMemAlignReadByte_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinMemAlignByte_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinMemAlign_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.MemAlign.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinMemAlignRangeSlice_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinMemAlignRomSlice_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinMem_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinSpecifiedRangesSlice_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinArithDiv_opBus_nil :
    (emptyComponentTable ZiskFv.AirsClean.ArithDiv.component).interactionsWith
      OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

theorem divSpinBinaryExtension_opBus_nil :
    (emptyComponentTable
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent).interactionsWith
        OpBusChannel.toRaw = [] :=
  emptyComponentTable_interactionsWith _ _

end ZiskFv.Compliance.DivSpinWitness
