import ZiskFv.Compliance.DivSpinRootSoundness.DefectExclusions

open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness

namespace ZiskFv.Compliance.DivSpinRootSoundness

theorem divSpinRootSoundness :
    ∀ i : Fin 4,
      StepSound divSpinAcceptedTrace divSpinSailTrace i (divSpinZiskStep i)
        (rowDecode_of_programDecode divSpinAcceptedTrace i (divSpinProgramDecodes i)) :=
  root_soundness 4 divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep
    divSpinProgramDecodes divSpinInputsAgree divSpinBootSeed
    divSpinOutsideDefectRegion

theorem divSpinAddiX1StepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinAddiX1Index
      (divSpinZiskStep divSpinAddiX1Index)
      (rowDecode_of_programDecode divSpinAcceptedTrace divSpinAddiX1Index
        (divSpinProgramDecodes divSpinAddiX1Index)) :=
  divSpinRootSoundness divSpinAddiX1Index

theorem divSpinAddiX2StepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinAddiX2Index
      (divSpinZiskStep divSpinAddiX2Index)
      (rowDecode_of_programDecode divSpinAcceptedTrace divSpinAddiX2Index
        (divSpinProgramDecodes divSpinAddiX2Index)) :=
  divSpinRootSoundness divSpinAddiX2Index

theorem divSpinDivStepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinDivIndex
      (divSpinZiskStep divSpinDivIndex)
      (rowDecode_of_programDecode divSpinAcceptedTrace divSpinDivIndex
        (divSpinProgramDecodes divSpinDivIndex)) :=
  divSpinRootSoundness divSpinDivIndex

theorem divSpinJalStepSound :
    StepSound divSpinAcceptedTrace divSpinSailTrace divSpinJalIndex
      (divSpinZiskStep divSpinJalIndex)
      (rowDecode_of_programDecode divSpinAcceptedTrace divSpinJalIndex
        (divSpinProgramDecodes divSpinJalIndex)) :=
  divSpinRootSoundness divSpinJalIndex

end ZiskFv.Compliance.DivSpinRootSoundness
