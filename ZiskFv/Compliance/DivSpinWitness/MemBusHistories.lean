import ZiskFv.Compliance.DivSpinWitness.MemBusMainInteractions

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.MemoryBus (MemBusMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.DivSpinWitness

def divSpinX1Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage divSpinBoundaryRowX1)
    [cMemMessage divSpinAddiX1Row, aMemMessage divSpinDivRow]

def divSpinX2Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage divSpinBoundaryRowX2)
    [cMemMessage divSpinAddiX2Row, bMemMessage divSpinDivRow]

def divSpinX3Telescope : List (Interaction FGL) :=
  registerTelescopingInteractions
    (ZiskFv.AirsClean.RegisterBoundary.bootMessage divSpinBoundaryRowX3)
    [cMemMessage divSpinDivRow]

def divSpinIdleBoundaryMessages : List (MemBusMessage FGL) :=
  (List.range 28).map fun i =>
    ZiskFv.AirsClean.RegisterBoundary.bootMessage
      (boundaryRowIdle ((i + 4 : Nat) : FGL))

def divSpinIdleBoundaryInteractions : List (Interaction FGL) :=
  (List.range 28).flatMap fun i =>
    registerBoundaryMemBusInteractions
      (boundaryRowIdle ((i + 4 : Nat) : FGL))

theorem divSpinX1Telescope_balanced :
    BalancedInteractions divSpinX1Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem divSpinX2Telescope_balanced :
    BalancedInteractions divSpinX2Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem divSpinX3Telescope_balanced :
    BalancedInteractions divSpinX3Telescope := by
  apply registerTelescopingInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

theorem divSpinIdleBoundaryInteractions_eq_paired :
    divSpinIdleBoundaryInteractions =
      pairedInteractions divSpinIdleBoundaryMessages := by
  unfold divSpinIdleBoundaryInteractions divSpinIdleBoundaryMessages
  generalize List.range 28 = indices
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.map_cons, pairedInteractions]
      rw [ih]
      congr 1

theorem divSpinIdleBoundaryInteractions_balanced :
    BalancedInteractions divSpinIdleBoundaryInteractions := by
  rw [divSpinIdleBoundaryInteractions_eq_paired]
  apply pairedInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

def divSpinMemBusCore : List (Interaction FGL) :=
  divSpinX1Telescope ++ divSpinX2Telescope ++ divSpinX3Telescope ++
    divSpinIdleBoundaryInteractions

theorem divSpinMemBusCore_balanced :
    BalancedInteractions divSpinMemBusCore := by
  unfold divSpinMemBusCore
  have h12 := balancedInteractions_append_of_balanced
    divSpinX1Telescope_balanced divSpinX2Telescope_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  have h123 := balancedInteractions_append_of_balanced
    h12 divSpinX3Telescope_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)
  exact balancedInteractions_append_of_balanced
    h123 divSpinIdleBoundaryInteractions_balanced (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      decide)

end ZiskFv.Compliance.DivSpinWitness
