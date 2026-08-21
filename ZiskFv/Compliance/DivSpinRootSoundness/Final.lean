import ZiskFv.Compliance.DivSpinRootSoundness.DefectExclusions

open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.Trusted

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

private theorem divSpinAcceptedMainRowAt_zero :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable 0 = divSpinAddiX1Row := by
  simpa [divSpinAddiX1Index, divSpinMainRows] using
    divSpinAcceptedMainRowAt divSpinAddiX1Index

private theorem divSpinAcceptedMainRowAt_one :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable 1 = divSpinAddiX2Row := by
  simpa [divSpinAddiX2Index, divSpinMainRows] using
    divSpinAcceptedMainRowAt divSpinAddiX2Index

private theorem divSpinAcceptedMainRowAt_two :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable 2 = divSpinDivRow := by
  simpa [divSpinDivIndex, divSpinMainRows] using divSpinAcceptedMainRowAt divSpinDivIndex

private theorem divSpinAcceptedMainRowAt_three :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable 3 = divSpinJalRow 3 := by
  simpa [divSpinJalIndex, divSpinMainRows] using divSpinAcceptedMainRowAt divSpinJalIndex

private def divLaneBridgeNoSources (i : Fin 4)
    (ha : (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable i.val).rom.a_src_reg ≠ 1)
    (hb : (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable i.val).rom.b_src_reg ≠ 1) :
    LaneBridge divSpinAcceptedTrace (divSpinSailTrace i) i.val where
  a_lo := by intro _ _ h _; exact (ha h).elim
  a_hi := by intro _ _ h _; exact (ha h).elim
  b_lo := by intro _ _ h _; exact (hb h).elim
  b_hi := by intro _ _ h _; exact (hb h).elim

private def divLaneBridgeABSources (i : Fin 4) (ra rb : Fin 32)
    (haoffset : Transpiler.wrap_to_regidx
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable i.val).rom.a_offset_imm0 = ra)
    (hboffset : Transpiler.wrap_to_regidx
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable i.val).rom.b_offset_imm0 = rb)
    (ha0 : (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable).a_0 i.val = lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (divSpinSailTrace i)).xreg ra))
    (ha1 : (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable).a_1 i.val = lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (divSpinSailTrace i)).xreg ra))
    (hb0 : (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable).b_0 i.val = lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (divSpinSailTrace i)).xreg rb))
    (hb1 : (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
      divSpinAcceptedTrace.mainTable).b_1 i.val = lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (divSpinSailTrace i)).xreg rb)) :
    LaneBridge divSpinAcceptedTrace (divSpinSailTrace i) i.val where
  a_lo := by intro r _ _ h; simpa [haoffset.symm.trans h] using ha0
  a_hi := by intro r _ _ h; simpa [haoffset.symm.trans h] using ha1
  b_lo := by intro r _ _ h; simpa [hboffset.symm.trans h] using hb0
  b_hi := by intro r _ _ h; simpa [hboffset.symm.trans h] using hb1

def divSpinLaneBridge : ∀ i : Fin 4,
    LaneBridge divSpinAcceptedTrace (divSpinSailTrace i) i.val
  | ⟨0, _⟩ => divLaneBridgeNoSources divSpinAddiX1Index
      (by simp [divSpinAddiX1Index, divSpinAcceptedMainRowAt_zero,
        divSpinAddiX1Row, divSpinAddiX1RowTemplate, divSpinAddiBits,
        ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
        ZiskFv.AirsClean.Main.mainRomRowOf, ZiskFv.AirsClean.boolF])
      (by simp [divSpinAddiX1Index, divSpinAcceptedMainRowAt_zero,
        divSpinAddiX1Row, divSpinAddiX1RowTemplate, divSpinAddiBits,
        ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
        ZiskFv.AirsClean.Main.mainRomRowOf, ZiskFv.AirsClean.boolF])
  | ⟨1, _⟩ => divLaneBridgeNoSources divSpinAddiX2Index
      (by simp [divSpinAddiX2Index, divSpinAcceptedMainRowAt_one,
        divSpinAddiX2Row, divSpinAddiX2RowTemplate, divSpinAddiBits,
        ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
        ZiskFv.AirsClean.Main.mainRomRowOf, ZiskFv.AirsClean.boolF])
      (by simp [divSpinAddiX2Index, divSpinAcceptedMainRowAt_one,
        divSpinAddiX2Row, divSpinAddiX2RowTemplate, divSpinAddiBits,
        ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
        ZiskFv.AirsClean.Main.mainRomRowOf, ZiskFv.AirsClean.boolF])
  | ⟨2, _⟩ => divLaneBridgeABSources divSpinDivIndex
      (regidx_to_fin x1) (regidx_to_fin x2)
      (by
        simp only [divSpinDivIndex]
        rw [divSpinAcceptedMainRowAt_two]
        change Transpiler.wrap_to_regidx (1 : FGL) = regidx_to_fin x1
        norm_num [Transpiler.wrap_to_regidx, Transpiler.regidxOfBitVec5, x1,
          regidx_to_fin]
        apply Fin.ext
        norm_num)
      (by
        simp only [divSpinDivIndex]
        rw [divSpinAcceptedMainRowAt_two]
        change Transpiler.wrap_to_regidx (2 : FGL) = regidx_to_fin x2
        norm_num [Transpiler.wrap_to_regidx, Transpiler.regidxOfBitVec5, x2,
          regidx_to_fin]
        apply Fin.ext
        norm_num)
      (by
        rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          divSpinAcceptedTrace.program divSpinAcceptedTrace.mainTable 2).core.a_0 = _
        rw [divSpinAcceptedMainRowAt_two]
        rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
          (divSpinSailTrace divSpinDivIndex) (regidx_to_fin x1) (6#64) divSpinReadX1Div]
        norm_num [divSpinDivRow, divSpinDivRowTemplate,
          ZiskFv.AirsClean.Main.mainRomRowOf, lane_lo]
        decide)
      (by
        rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          divSpinAcceptedTrace.program divSpinAcceptedTrace.mainTable 2).core.a_1 = _
        rw [divSpinAcceptedMainRowAt_two]
        rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
          (divSpinSailTrace divSpinDivIndex) (regidx_to_fin x1) (6#64) divSpinReadX1Div]
        norm_num [divSpinDivRow, divSpinDivRowTemplate,
          ZiskFv.AirsClean.Main.mainRomRowOf, lane_hi])
      (by
        rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_b_0]
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          divSpinAcceptedTrace.program divSpinAcceptedTrace.mainTable 2).core.b_0 = _
        rw [divSpinAcceptedMainRowAt_two]
        rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
          (divSpinSailTrace divSpinDivIndex) (regidx_to_fin x2) (2#64) divSpinReadX2Div]
        norm_num [divSpinDivRow, divSpinDivRowTemplate,
          ZiskFv.AirsClean.Main.mainRomRowOf, lane_lo]
        decide)
      (by
        rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_b_1]
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          divSpinAcceptedTrace.program divSpinAcceptedTrace.mainTable 2).core.b_1 = _
        rw [divSpinAcceptedMainRowAt_two]
        rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
          (divSpinSailTrace divSpinDivIndex) (regidx_to_fin x2) (2#64) divSpinReadX2Div]
        norm_num [divSpinDivRow, divSpinDivRowTemplate,
          ZiskFv.AirsClean.Main.mainRomRowOf, lane_hi])
  | ⟨3, _⟩ => divLaneBridgeNoSources divSpinJalIndex
      (by simp [divSpinJalIndex, divSpinAcceptedMainRowAt_three, divSpinJalRow,
        ZiskFv.Compliance.AddSpinWitness.addSpinJalBits,
        ZiskFv.AirsClean.Main.mainRomRowOf, ZiskFv.AirsClean.boolF])
      (by simp [divSpinJalIndex, divSpinAcceptedMainRowAt_three, divSpinJalRow,
        ZiskFv.Compliance.AddSpinWitness.addSpinJalBits,
        ZiskFv.AirsClean.Main.mainRomRowOf, ZiskFv.AirsClean.boolF])

/-- The two root PC premises for this witness: boot agreement, and the Sail-internal retire law.
    `sailRetireChain_of_inputsAgree` builds the latter from the per-row `InputsAgree` family this
    witness already proves — no new content, and no hand-evaluated Sail execution. -/
def divSpinPcChain : SegmentPcChain divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep where
  toSailRetireChain :=
    sailRetireChain_of_inputsAgree
      (fun i => rowDecode_of_programDecode divSpinAcceptedTrace i (divSpinProgramDecodes i))
      divSpinInputsAgree divSpinBootSeed divSpinOutsideDefectRegion
        divSpinLaneBridge divSpinRowsAligned
  boot := (pcSeed_of_inputsAgree divSpinInputsAgree).boot

theorem divSpinRootSoundness :
    ∀ i : Fin 4,
      StepSound divSpinAcceptedTrace divSpinSailTrace i (divSpinZiskStep i)
        (rowDecode_of_programDecode divSpinAcceptedTrace i (divSpinProgramDecodes i)) :=
  stepSound_of_programDecodes 4 divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep
    divSpinProgramDecodes divSpinInputsAgreeCore divSpinPcChain divSpinRowsAligned
    divSpinBootSeed divSpinOutsideDefectRegion divSpinLaneBridge

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
