import ZiskFv.Compliance.DivSpinWitness.OpBusArithPrimary

open Goldilocks
open Air.Flat
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinRemainderBound_balanced :
    BalancedInteractions
      [divSpinArithRemainderInteraction,
        binaryOpBusInteraction divSpinRemainderBoundRow] :=
  divSpinOpBusPair_balanced _ _ (by decide) (by decide)

end ZiskFv.Compliance.DivSpinWitness
