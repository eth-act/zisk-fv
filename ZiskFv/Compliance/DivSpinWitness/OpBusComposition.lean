import ZiskFv.Compliance.DivSpinWitness.OpBusWitnessPerm

open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinWitness_opBus_balanced :
    BalancedInteractions
      (divSpinWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) :=
  balancedInteractions_of_perm divSpinReorderedOpBus_balanced
    divSpinWitnessOpBus_perm.symm

end ZiskFv.Compliance.DivSpinWitness
