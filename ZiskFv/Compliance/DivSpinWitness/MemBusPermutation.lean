import ZiskFv.Compliance.DivSpinWitness.MemBusReduced

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

private theorem move_front {α : Type} (x : α) (pre post : List α) :
    List.Perm (pre ++ x :: post) (x :: (pre ++ post)) := by
  induction pre with
  | nil => rfl
  | cons head pre ih =>
      exact (List.Perm.cons head ih).trans (List.Perm.swap head x _).symm

private theorem move_front₂ {α : Type} (x : α) (a b post : List α) :
    List.Perm (a ++ (b ++ x :: post)) (x :: (a ++ (b ++ post))) := by
  simpa only [List.append_assoc] using move_front x (a ++ b) post

private theorem chronological_perm_histories {α : Type}
    (b1 r1 b2 r2 b3 r3 c1p c1m c2p c2m a1p a1m b2p b2m c3p c3m : α)
    (idle : List α) :
    List.Perm
      ([b1, r1, b2, r2, b3, r3] ++ idle ++
        [c1p, c1m, c2p, c2m, a1p, a1m, b2p, b2m, c3p, c3m])
      ([b1, r1, c1p, c1m, a1p, a1m] ++
        [b2, r2, c2p, c2m, b2p, b2m] ++ [b3, r3, c3p, c3m] ++ idle) := by
  simp only [List.append_assoc]
  refine List.Perm.cons b1 <| List.Perm.cons r1 <|
    (move_front c1p ([b2, r2, b3, r3] ++ idle)
      [c1m, c2p, c2m, a1p, a1m, b2p, b2m, c3p, c3m]).trans
      (List.Perm.cons c1p ?_)
  refine (move_front c1m ([b2, r2, b3, r3] ++ idle)
      [c2p, c2m, a1p, a1m, b2p, b2m, c3p, c3m]).trans
    (List.Perm.cons c1m ?_)
  refine (move_front₂ a1p ([b2, r2, b3, r3] ++ idle) [c2p, c2m]
      [a1m, b2p, b2m, c3p, c3m]).trans
    (List.Perm.cons a1p ?_)
  refine (move_front₂ a1m ([b2, r2, b3, r3] ++ idle) [c2p, c2m]
      [b2p, b2m, c3p, c3m]).trans
    (List.Perm.cons a1m ?_)
  refine List.Perm.cons b2 <| List.Perm.cons r2 <|
    (move_front c2p ([b3, r3] ++ idle) [c2m, b2p, b2m, c3p, c3m]).trans
      (List.Perm.cons c2p ?_)
  refine (move_front c2m ([b3, r3] ++ idle) [b2p, b2m, c3p, c3m]).trans
      (List.Perm.cons c2m ?_)
  refine (move_front b2p ([b3, r3] ++ idle) [b2m, c3p, c3m]).trans
      (List.Perm.cons b2p ?_)
  refine (move_front b2m ([b3, r3] ++ idle) [c3p, c3m]).trans
      (List.Perm.cons b2m ?_)
  refine List.Perm.cons b3 <| List.Perm.cons r3 <|
    (move_front c3p idle [c3m]).trans (List.Perm.cons c3p ?_)
  refine (move_front c3m idle []).trans (List.Perm.cons c3m ?_)
  simpa using List.Perm.refl idle

theorem divSpinMemBusNonzeroChronological_perm_core :
    List.Perm divSpinMemBusNonzeroChronological divSpinMemBusCore := by
  change List.Perm
    ([ registerBoundaryBootInteraction divSpinBoundaryRowX1
     , registerBoundaryReloadInteraction divSpinBoundaryRowX1
     , registerBoundaryBootInteraction divSpinBoundaryRowX2
     , registerBoundaryReloadInteraction divSpinBoundaryRowX2
     , registerBoundaryBootInteraction divSpinBoundaryRowX3
     , registerBoundaryReloadInteraction divSpinBoundaryRowX3 ] ++
      divSpinIdleBoundaryInteractions ++
      [ mainCRegPreInteraction divSpinAddiX1Row
      , mainCMemInteraction divSpinAddiX1Row
      , mainCRegPreInteraction divSpinAddiX2Row
      , mainCMemInteraction divSpinAddiX2Row
      , mainARegPreInteraction divSpinDivRow
      , mainAMemInteraction divSpinDivRow
      , mainBRegPreInteraction divSpinDivRow
      , mainBMemInteraction divSpinDivRow
      , mainCRegPreInteraction divSpinDivRow
      , mainCMemInteraction divSpinDivRow ])
    ([ registerBoundaryBootInteraction divSpinBoundaryRowX1
     , registerBoundaryReloadInteraction divSpinBoundaryRowX1
     , mainCRegPreInteraction divSpinAddiX1Row
     , mainCMemInteraction divSpinAddiX1Row
     , mainARegPreInteraction divSpinDivRow
     , mainAMemInteraction divSpinDivRow ] ++
      [ registerBoundaryBootInteraction divSpinBoundaryRowX2
      , registerBoundaryReloadInteraction divSpinBoundaryRowX2
      , mainCRegPreInteraction divSpinAddiX2Row
      , mainCMemInteraction divSpinAddiX2Row
      , mainBRegPreInteraction divSpinDivRow
      , mainBMemInteraction divSpinDivRow ] ++
      [ registerBoundaryBootInteraction divSpinBoundaryRowX3
      , registerBoundaryReloadInteraction divSpinBoundaryRowX3
      , mainCRegPreInteraction divSpinDivRow
      , mainCMemInteraction divSpinDivRow ] ++
      divSpinIdleBoundaryInteractions)
  exact chronological_perm_histories _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end ZiskFv.Compliance.DivSpinWitness
