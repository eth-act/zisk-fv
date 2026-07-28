import ZiskFv.Compliance.DivSpinWitness.OpBusAddiX1

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinAddiX2_balanced :
    BalancedInteractions
      [binaryAddOpBusInteraction (ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 0 2),
        mainOpBusInteraction divSpinAddiX2Row] :=
  divSpinOpBusPair_balanced _ _ (by decide) (by decide)

end ZiskFv.Compliance.DivSpinWitness
