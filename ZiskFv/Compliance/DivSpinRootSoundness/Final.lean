import ZiskFv.Compliance.DivSpinRootSoundness.DefectExclusions

open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness

namespace ZiskFv.Compliance.DivSpinRootSoundness

/-- #330 Phase 7: each executed step's producer entry is its own row's successor `pc`. Only a
    two-row unaligned JALR lowering can break this, and only at a step that has a successor. -/
def divSpinRowsAligned :
    StepRowsAligned divSpinAcceptedTrace divSpinZiskStep
      (fun i => rowDecode_of_programDecode divSpinAcceptedTrace i (divSpinProgramDecodes i)) := by
  intro j h
  have h' : j + 1 < 4 := h
  have hj : j < 4 - 1 := by omega
  interval_cases j <;> rfl

/-- The two root PC premises for this witness: boot agreement, and the Sail-internal retire law.
    `sailRetireChain_of_inputsAgree` builds the latter from the per-row `InputsAgree` family this
    witness already proves — no new content, and no hand-evaluated Sail execution. -/
def divSpinPcChain : SegmentPcChain divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep where
  toSailRetireChain :=
    sailRetireChain_of_inputsAgree
      (fun i => rowDecode_of_programDecode divSpinAcceptedTrace i (divSpinProgramDecodes i))
      divSpinInputsAgree divSpinBootSeed divSpinOutsideDefectRegion (fun i => sorry) divSpinRowsAligned
  boot := (pcSeed_of_inputsAgree divSpinInputsAgree).boot

theorem divSpinRootSoundness :
    ∀ i : Fin 4,
      StepSound divSpinAcceptedTrace divSpinSailTrace i (divSpinZiskStep i)
        (rowDecode_of_programDecode divSpinAcceptedTrace i (divSpinProgramDecodes i)) :=
  stepSound_of_programDecodes 4 divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep
    divSpinProgramDecodes divSpinInputsAgreeCore divSpinPcChain divSpinRowsAligned
    divSpinBootSeed divSpinOutsideDefectRegion (fun i => sorry)

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
