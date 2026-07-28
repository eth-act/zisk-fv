import ZiskFv.Compliance.DivSpinWitness.OpBusPairBase

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinArithPrimary_balanced :
    BalancedInteractions
      [divSpinArithPrimaryInteraction, mainOpBusInteraction divSpinDivRow] :=
  divSpinOpBusPair_balanced _ _ (by decide) (by decide)

end ZiskFv.Compliance.DivSpinWitness
