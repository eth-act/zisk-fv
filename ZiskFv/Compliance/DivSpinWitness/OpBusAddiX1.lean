import ZiskFv.Compliance.DivSpinWitness.OpBusRemainder

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinAddiX1_balanced :
    BalancedInteractions
      [binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 6),
        mainOpBusInteraction divSpinAddiX1Row] :=
  divSpinOpBusPair_balanced _ _ (by decide) (by decide)

end ZiskFv.Compliance.DivSpinWitness
