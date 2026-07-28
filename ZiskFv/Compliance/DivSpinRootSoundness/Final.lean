import ZiskFv.Compliance.DivSpinRootSoundness.DefectExclusions

open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness

namespace ZiskFv.Compliance.DivSpinRootSoundness

theorem divSpinRootSoundness :
    ∀ i : Fin 4,
      StepSound divSpinAcceptedTrace divSpinSailTrace i (divSpinZiskStep i) :=
  root_soundness 4 divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep
    divSpinProgramDecodes divSpinInputsAgree divSpinBootSeed
    divSpinOutsideDefectRegion

theorem divSpinAddiX1StepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinAddiX1Index
      (divSpinZiskStep divSpinAddiX1Index) :=
  divSpinRootSoundness divSpinAddiX1Index

theorem divSpinAddiX2StepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinAddiX2Index
      (divSpinZiskStep divSpinAddiX2Index) :=
  divSpinRootSoundness divSpinAddiX2Index

theorem divSpinDivStepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinDivIndex
      (divSpinZiskStep divSpinDivIndex) :=
  divSpinRootSoundness divSpinDivIndex

theorem divSpinJalStepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinJalIndex
      (divSpinZiskStep divSpinJalIndex) :=
  divSpinRootSoundness divSpinJalIndex

end ZiskFv.Compliance.DivSpinRootSoundness
