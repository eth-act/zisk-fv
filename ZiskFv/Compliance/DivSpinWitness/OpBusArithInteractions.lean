import ZiskFv.Compliance.DivSpinWitness.Constraints

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

def divSpinArithPrimaryInteraction : Interaction FGL where
  channel := OpBusChannel.toRaw
  mult := 1
  msg :=
    (toElements
      (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage divSpinArithRow)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def divSpinArithRemainderInteraction : Interaction FGL where
  channel := OpBusChannel.toRaw
  mult :=
    -(divSpinArithRow.flags.div *
      (1 - divSpinArithRow.flags.div_by_zero))
  msg :=
    (toElements
      (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage
        divSpinArithRow)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

theorem divSpinArithTable_opBusInteractions :
    divSpinArithTable.interactionsWith OpBusChannel.toRaw =
      [divSpinArithPrimaryInteraction, divSpinArithRemainderInteraction] := by
  rw [Table.interactionsWith]
  change List.flatMap
      (fun row =>
        ZiskFv.AirsClean.ArithMul.componentComplete.operations.interactionValuesWith
          OpBusChannel.toRaw (divSpinArithTable.environment row))
      divSpinArithTable.table =
    [divSpinArithPrimaryInteraction, divSpinArithRemainderInteraction]
  change List.flatMap _ [divSpinArithRowArray] = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    ZiskFv.AirsClean.ArithMul.componentComplete.operations.interactionValuesWith
        OpBusChannel.toRaw (Environment.fromArray divSpinArithRowArray emptyData) =
      [divSpinArithPrimaryInteraction, divSpinArithRemainderInteraction]
  have h_input :
      Eval.eval (Environment.fromArray divSpinArithRowArray emptyData)
          ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar =
        divSpinArithRow := by
    simpa [divSpinArithRowArray, Environment.fromInput] using
      ProvableType.eval_fromInput_varFromOffset_zero divSpinArithRow emptyData
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.ArithMul.componentComplete_interactionsWith_opBus]
  simp only [List.map_cons, List.map_nil]
  congr 1
  · simp only [divSpinArithPrimaryInteraction, AbstractInteraction.eval,
      ChannelInteraction.toRaw, Channel.pushed, pushed]
    congr 1
    rw [← ProvableType.toElements_eval,
      ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr, h_input]
  · simp only [divSpinArithRemainderInteraction, AbstractInteraction.eval,
      ChannelInteraction.toRaw, Channel.emitted, emitted]
    congr 1
    congr 1
    rw [← ProvableType.toElements_eval,
      ZiskFv.AirsClean.ArithMul.eval_remainderBoundOpBusMessageExpr, h_input]

end ZiskFv.Compliance.DivSpinWitness
