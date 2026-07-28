import ZiskFv.Compliance.DivSpinWitness.OpBusArithInteractions

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

private theorem divSpinMainOpBusInteractionsAt
    (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input :
      Eval.eval env (componentWithRomMemAndOpBus 4 divSpinProgram).rowInputVar = row) :
    (componentWithRomMemAndOpBus 4 divSpinProgram).operations.interactionValuesWith
        OpBusChannel.toRaw env = [mainOpBusInteraction row] := by
  let rowVar := (componentWithRomMemAndOpBus 4 divSpinProgram).rowInputVar
  have h_core : Eval.eval env rowVar.core = row.core := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
    exact congrArg MainRowWithRom.core h_input
  have h_field :=
    ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op env rowVar.core
  have h_msg_eval :
      Eval.eval env (opBusMessageExpr rowVar.core) = opBusMessage row.core := by
    rw [eval_opBusMessageExpr, h_core]
  rw [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  simp only [List.map_cons, List.map_nil]
  congr 1
  simp [mainOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env (-rowVar.core.is_external_op) = -row.core.is_external_op
    simp [Expression.eval, h_field, h_core]
  constructor
  · rw [toElements_eval_toArray]
    change (toElements (Eval.eval env (opBusMessageExpr rowVar.core))).toArray =
      (toElements (opBusMessage row.core)).toArray
    rw [h_msg_eval]
  · rfl

theorem divSpinMainTable_opBusInteractions :
    divSpinMainTable.interactionsWith OpBusChannel.toRaw =
      divSpinMainRows.map mainOpBusInteraction := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    (componentWithRomMemAndOpBus 4 divSpinProgram).operations.interactionValuesWith
      OpBusChannel.toRaw (Environment.fromArray row emptyData))
    (divSpinMainRows.map mainRawRow |>.mapIdx mainFixedColumns.materialize) = _
  simp only [divSpinMainRows, List.map_cons, List.map_nil, List.mapIdx_cons,
    List.mapIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [divSpinMainOpBusInteractionsAt _ divSpinAddiX1Row
      (eval_mainRawRow_materialize 0 emptyData divSpinAddiX1Row (by rfl) (by rfl)),
    divSpinMainOpBusInteractionsAt _ divSpinAddiX2Row
      (eval_mainRawRow_materialize 1 emptyData divSpinAddiX2Row (by rfl) (by rfl)),
    divSpinMainOpBusInteractionsAt _ divSpinDivRow
      (eval_mainRawRow_materialize 2 emptyData divSpinDivRow (by rfl) (by rfl)),
    divSpinMainOpBusInteractionsAt _ (divSpinJalRow 3)
      (eval_mainRawRow_materialize 3 emptyData (divSpinJalRow 3) (by rfl) (by rfl)),
    divSpinMainOpBusInteractionsAt _ (divSpinJalRow 4)
      (eval_mainRawRow_materialize 4 emptyData (divSpinJalRow 4) (by rfl) (by rfl))]
  rfl

end ZiskFv.Compliance.DivSpinWitness
