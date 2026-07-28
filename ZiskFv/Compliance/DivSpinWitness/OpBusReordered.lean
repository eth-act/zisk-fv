import ZiskFv.Compliance.DivSpinWitness.OpBusJal
import ZiskFv.Compliance.DivSpinWitness.OpBusChunks

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.DivSpinWitness

def divSpinReorderedOpBusInteractions : List (Interaction FGL) :=
  [divSpinArithPrimaryInteraction, mainOpBusInteraction divSpinDivRow] ++
    ([divSpinArithRemainderInteraction, binaryOpBusInteraction divSpinRemainderBoundRow] ++
      ([binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 6),
          mainOpBusInteraction divSpinAddiX1Row] ++
        ([binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 2),
            mainOpBusInteraction divSpinAddiX2Row] ++
          [mainOpBusInteraction (divSpinJalRow 3),
            mainOpBusInteraction (divSpinJalRow 4)])))

theorem divSpinReorderedOpBus_balanced :
    BalancedInteractions divSpinReorderedOpBusInteractions := by
  unfold divSpinReorderedOpBusInteractions
  exact balancedInteractions_append_of_balanced divSpinArithPrimary_balanced
    (balancedInteractions_append_of_balanced divSpinRemainderBound_balanced
      (balancedInteractions_append_of_balanced divSpinAddiX1_balanced
        (balancedInteractions_append_of_balanced divSpinAddiX2_balanced
          divSpinJalOpBus_balanced (by
            left
            rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
            norm_num))
        (by
          left
          rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
          norm_num))
      (by
        left
        rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
        norm_num))
    (by
      left
      rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
      norm_num)

end ZiskFv.Compliance.DivSpinWitness
