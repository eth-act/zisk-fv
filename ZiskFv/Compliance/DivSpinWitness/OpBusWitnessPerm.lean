import ZiskFv.Compliance.DivSpinWitness.OpBusReordered

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

private theorem divSpinPerm_move_front {α : Type} (x : α)
    (pre post : List α) :
    List.Perm (pre ++ x :: post) (x :: pre ++ post) := by
  induction pre with
  | nil => rfl
  | cons head pre ih =>
      exact (List.Perm.cons head ih).trans (List.Perm.swap head x _).symm

private theorem divSpinTenPerm {α : Type} (a b c d e f g h i j : α) :
    List.Perm [a, b, c, d, e, f, g, h, i, j]
      [a, h, b, c, d, f, e, g, i, j] := by
  have h_move :
      List.Perm [a, b, c, d, e, f, g, h, i, j]
        [a, h, b, c, d, e, f, g, i, j] := by
    exact List.Perm.cons a
      (divSpinPerm_move_front h [b, c, d, e, f, g] [i, j])
  have h_swap :
      List.Perm [a, h, b, c, d, e, f, g, i, j]
        [a, h, b, c, d, f, e, g, i, j] :=
    List.Perm.cons a <| List.Perm.cons h <| List.Perm.cons b <|
      List.Perm.cons c <| List.Perm.cons d <| (List.Perm.swap e f [g, i, j]).symm
  exact h_move.trans h_swap

theorem divSpinWitnessOpBus_perm :
    List.Perm
  (divSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw))
      divSpinReorderedOpBusInteractions := by
  rw [divSpinWitness_tables]
  rw [divSpinTables_opBusChunks]
  simp only [List.flatMap_append]
  rw [divSpinOpBusTables0_flatMap, divSpinOpBusTables1_flatMap,
    divSpinOpBusTables2_flatMap, divSpinOpBusTables3_flatMap]
  simp only [List.nil_append]
  unfold divSpinReorderedOpBusInteractions
  exact divSpinTenPerm _ _ _ _ _ _ _ _ _ _

end ZiskFv.Compliance.DivSpinWitness
