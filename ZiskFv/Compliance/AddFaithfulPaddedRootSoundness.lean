import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingAddFaithfulNonvacuity
import ZiskFv.Soundness

/-!
# Non-vacuous raw-program `root_soundness` instantiation (#320)

This applies the public `ZiskFv.Compliance.root_soundness` theorem — the raw-program-decode
entrypoint, NOT `stepSound_of_programDecodes` — to `addFaithfulAcceptedTrace`
(`AddFaithfulPaddedWitness.lean`) via the genuine raw-program binding
(`RawProgramBindingAddFaithfulNonvacuity.lean`). The executed step (`numInstructions = 1`) is real
(`i = 0`, not `Fin 0`), so the conclusion is non-vacuous: this is the first in-tree instantiation of
`root_soundness` that actually lifts through `programDecode_of_rawProgramDecode` for a real
executed step.
-/

set_option maxRecDepth 10000

open Goldilocks
open Air.Flat
open ZiskFv.Compliance
open ZiskFv.Compliance.AddFaithfulPaddedWitness
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.AddFaithfulPaddedRootSoundness

def x1 : regidx := regidx.Regidx (1#5)

def addFaithfulAddIndex : Fin 1 := ⟨0, by decide⟩

def addFaithfulAddClaim : Claim_add addFaithfulAcceptedTrace addFaithfulAddIndex where
  r1 := x1
  r2 := x1
  rd := x1

def addFaithfulZiskStep : ∀ i : Fin 1, ZiskStep addFaithfulAcceptedTrace i
  | ⟨0, _⟩ => .add addFaithfulAddClaim

def addFaithfulMisa : RegisterType Register.misa := 0#64

def addFaithfulRegs (pc : BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.misa addFaithfulMisa
  regs2.insert (reg_of_fin (regidx_to_fin x1)) (0#64)

def addFaithfulState (pc : BitVec 64) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := addFaithfulRegs pc
    mem := {} }

/-- The Sail side of this witness (#343). Not a hand-written family of states: the execution Sail's
    own semantics generates from `addFaithfulState (0#64)`. A one-instruction execution has no chain
    step, so it reduces to the initial state at its single index — but it is now the *generated*
    trace, which is what `root_soundness` consumes. -/
noncomputable def addFaithfulSailTrace : SailTrace 1 :=
  chainedSailTrace addFaithfulZiskStep (addFaithfulState (0#64))

theorem addFaithfulRowsOf_empty_readSound :
    MemoryBusRowsPrefixReadSound
      ({} : Std.ExtHashMap Nat (BitVec 8))
      ((List.range addFaithfulAcceptedTrace.numInstructions).flatMap (fun _ => [])) := by
  change MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8)) []
  intro priorRows entry laterRows h_split h_selected
  simp at h_split

def addFaithfulBootSeed :
    BootSegmentMemorySeed addFaithfulAcceptedTrace addFaithfulSailTrace addFaithfulZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by
    intro h
    rfl
  step := by
    intro j h
    change j + 1 < 1 at h
    omega
  readSoundInputs := fun h => absurd h addFaithfulWitness_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_nonempty
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_nonempty
  placement := by
    intro i
    fin_cases i
    simp [MemoryOpPlacement, addFaithfulZiskStep]

private theorem addFaithfulAcceptedTrace_program :
    addFaithfulAcceptedTrace.program = addFaithfulProgram := rfl

private theorem addFaithfulMainRowAt_zero :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addFaithfulProgram
      addFaithfulMainTable 0 = addX1Row := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by norm_num [addFaithfulMainTable, mainRowsTable, addFaithfulMainRows])]
  simpa [Table.environmentAt] using addFaithfulMainTable_evalAt_zero

private theorem addFaithfulMainPc_add :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
        addFaithfulAcceptedTrace.mainTable).pc addFaithfulAddIndex.val = 0 := by
  rw [addFaithfulAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulProgram
      addFaithfulMainTable).pc 0 = 0
  simp [addFaithfulMainRowAt_zero, addX1Row]

private theorem addFaithfulReadX1_add :
    read_xreg (regidx_to_fin x1) (addFaithfulSailTrace addFaithfulAddIndex) =
      EStateM.Result.ok (0#64) (addFaithfulSailTrace addFaithfulAddIndex) := by
  simp [addFaithfulSailTrace, addFaithfulAddIndex, addFaithfulState, addFaithfulRegs, x1,
    regidx_to_fin, read_xreg, reg_of_fin]

def addFaithfulAddInput : PureSpec.AddInput where
  r1_val := 0#64
  r2_val := 0#64
  rd := regidx_to_fin x1
  PC := 0#64

private theorem addFaithfulAddLaneLo
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      (field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulProgram
          addFaithfulMainTable) 0) = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
        addFaithfulAcceptedTrace.mainTable) addFaithfulAddIndex.val =
      lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addFaithfulSailTrace addFaithfulAddIndex)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addFaithfulSailTrace addFaithfulAddIndex) (regidx_to_fin x1) (0#64) addFaithfulReadX1_add]
  rw [addFaithfulAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulProgram
      addFaithfulMainTable) 0 = _
  rw [h_field]
  simp [lane_lo]

private theorem addFaithfulAddLaneHi
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      (field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulProgram
          addFaithfulMainTable) 0) = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
        addFaithfulAcceptedTrace.mainTable) addFaithfulAddIndex.val =
      lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addFaithfulSailTrace addFaithfulAddIndex)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addFaithfulSailTrace addFaithfulAddIndex) (regidx_to_fin x1) (0#64) addFaithfulReadX1_add]
  rw [addFaithfulAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulProgram
      addFaithfulMainTable) 0 = _
  rw [h_field]
  simp [lane_hi]

def addFaithfulAddInputs :
    Inputs_add addFaithfulAcceptedTrace addFaithfulSailTrace addFaithfulAddIndex
      addFaithfulAddClaim where
  add_input := addFaithfulAddInput
  h_input_r1 := by
    simpa [addFaithfulAddInput, addFaithfulAddClaim] using addFaithfulReadX1_add
  h_input_r2 := by
    simpa [addFaithfulAddInput, addFaithfulAddClaim] using addFaithfulReadX1_add
  h_input_pc := by
    simp [addFaithfulAddInput, addFaithfulSailTrace, addFaithfulAddIndex, addFaithfulState,
      addFaithfulRegs, x1, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := by
    rfl
  h_a_lo_t := by
    change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
          addFaithfulAcceptedTrace.mainTable).a_0 addFaithfulAddIndex.val =
        lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (addFaithfulSailTrace addFaithfulAddIndex)).xreg (regidx_to_fin x1))
    exact addFaithfulAddLaneLo (fun m i => m.a_0 i)
      (by simp [addFaithfulMainRowAt_zero, addX1Row])
  h_a_hi_t := by
    change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
          addFaithfulAcceptedTrace.mainTable).a_1 addFaithfulAddIndex.val =
        lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (addFaithfulSailTrace addFaithfulAddIndex)).xreg (regidx_to_fin x1))
    exact addFaithfulAddLaneHi (fun m i => m.a_1 i)
      (by simp [addFaithfulMainRowAt_zero, addX1Row])
  h_b_lo_t := by
    change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
          addFaithfulAcceptedTrace.mainTable).b_0 addFaithfulAddIndex.val =
        lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (addFaithfulSailTrace addFaithfulAddIndex)).xreg (regidx_to_fin x1))
    exact addFaithfulAddLaneLo (fun m i => m.b_0 i)
      (by simp [addFaithfulMainRowAt_zero, addX1Row])
  h_b_hi_t := by
    change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
          addFaithfulAcceptedTrace.mainTable).b_1 addFaithfulAddIndex.val =
        lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (addFaithfulSailTrace addFaithfulAddIndex)).xreg (regidx_to_fin x1))
    exact addFaithfulAddLaneHi (fun m i => m.b_1 i)
      (by simp [addFaithfulMainRowAt_zero, addX1Row])
  h_pc_bridge := by
    rw [addFaithfulAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulProgram
          addFaithfulMainTable).pc 0).val = _
    simp [addFaithfulMainRowAt_zero, addX1Row, addFaithfulAddInput]

def addFaithfulInputsAgree :
    ∀ i : Fin 1, InputsAgree addFaithfulAcceptedTrace addFaithfulSailTrace i (addFaithfulZiskStep i)
  | ⟨0, _⟩ => addFaithfulAddInputs

/-- The two root PC premises for this witness, from the per-row family above
    (`pcSeed_of_inputsAgree` / `inputsAgreeCore_of_inputsAgree`). -/
def addFaithfulPcSeed : SegmentPcSeed addFaithfulAcceptedTrace addFaithfulSailTrace :=
  pcSeed_of_inputsAgree addFaithfulInputsAgree

noncomputable def addFaithfulInputsAgreeCore :
    ∀ i : Fin 1,
      InputsAgreeCore addFaithfulAcceptedTrace addFaithfulSailTrace i (addFaithfulZiskStep i) :=
  fun i => inputsAgreeCore_of_inputsAgree i (addFaithfulZiskStep i) (addFaithfulInputsAgree i)

def addFaithfulAddOutsideDefectRegion :
    RowOutsideDefectRegion addFaithfulAcceptedTrace addFaithfulAddIndex
      (addFaithfulZiskStep addFaithfulAddIndex) := by
  unfold RowOutsideDefectRegion addFaithfulZiskStep MainSequentialPcDomain mainPcVal
  rw [addFaithfulMainPc_add]
  change 0 < GL_prime - 4
  norm_num

def addFaithfulOutsideDefectRegion :
    ∀ i : Fin 1, RowOutsideDefectRegion addFaithfulAcceptedTrace i (addFaithfulZiskStep i)
  | ⟨0, _⟩ => addFaithfulAddOutsideDefectRegion

/-! ## The raw-program decode evidence for the one executed step -/

open ZiskFv.Compliance.RawProgramBinding in
theorem addFaithfulRawDecode :
    RawProgramDecode_add addFaithfulAcceptedTrace addFaithfulAddIndex addFaithfulAddClaim
      addFaithfulAddr addFaithfulRawProgram where
  h_idx := by
    rw [addFaithfulAcceptedTrace_mainTable_eq]
    change 0 + 1 < addFaithfulMainTable.table.length
    norm_num [addFaithfulMainTable, mainRowsTable, addFaithfulMainRows]
  hrd0 := by simp [addFaithfulAddClaim, x1, regidx_to_fin]
  hrs10 := by simp [addFaithfulAddClaim, x1, regidx_to_fin]
  hrs20 := by simp [addFaithfulAddClaim, x1, regidx_to_fin]
  hLine := by
    intro j hline
    change Fin 2 at j
    fin_cases j
    · refine ⟨⟨0, by decide⟩, rfl, ?_⟩
      simp only [addFaithfulRawProgram, addFaithfulAddClaim, x1, regidx_to_fin]
      decide
    · rw [addFaithfulMainPc_add] at hline
      rw [addFaithfulAcceptedTrace_program] at hline
      simp only [addFaithfulAcceptedTrace, addFaithfulProgram, addFaithfulRow1ProgramRow,
        RegisterMemBusBalance.addX1ProgramRow] at hline
      exact absurd hline (by decide)

open ZiskFv.Compliance.RawProgramBinding in
def addFaithfulRawProgramDecodes :
    ∀ i : Fin 1,
      RawProgramDecode addFaithfulAcceptedTrace i (addFaithfulZiskStep i)
        addFaithfulStart addFaithfulAddr addFaithfulRawProgram
  | ⟨0, _⟩ => ⟨⟨addFaithfulRawDecode⟩⟩

open ZiskFv.Compliance.RawProgramBinding in
/-- #330 Phase 7: vacuous here — a one-instruction execution has no step with a successor. -/
def addFaithfulRowsAligned :
    StepRowsAligned addFaithfulAcceptedTrace addFaithfulZiskStep
      (fun i => rowDecode_of_programDecode addFaithfulAcceptedTrace i
        (programDecode_of_rawProgramDecode addFaithfulAcceptedTrace i (addFaithfulZiskStep i)
          addFaithfulStart addFaithfulAddr addFaithfulRawProgram
          addFaithfulProgramRowsBinding (addFaithfulRawProgramDecodes i))) := by
  intro j h
  have h' : j + 1 < 1 := h
  omega

/-- The single root PC premise (#343): boot agreement at row `0`. The retire law that used to sit
    beside it is no longer a premise — `root_soundness` gets it from
    `chainedSailTrace_retireChain`. -/
def addFaithfulPcBoot : ∀ (_ : 0 < 1),
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addFaithfulAcceptedTrace.program
        addFaithfulAcceptedTrace.mainTable).pc 0).val
      = ((addFaithfulState (0#64)).regs.get? Register.PC).elim 0 BitVec.toNat :=
  (pcSeed_of_inputsAgree addFaithfulInputsAgree).boot

open ZiskFv.Compliance.RawProgramBinding in
theorem addFaithfulPaddedRawRootSoundness :
    ∀ i : Fin 1,
      StepSound addFaithfulAcceptedTrace addFaithfulSailTrace i (addFaithfulZiskStep i)
        (rowDecode_of_programDecode addFaithfulAcceptedTrace i
          (programDecode_of_rawProgramDecode addFaithfulAcceptedTrace i (addFaithfulZiskStep i)
            addFaithfulStart addFaithfulAddr addFaithfulRawProgram
            addFaithfulProgramRowsBinding (addFaithfulRawProgramDecodes i))) :=
  root_soundness 1 2 addFaithfulAcceptedTrace (addFaithfulState (0#64)) addFaithfulZiskStep
    addFaithfulStart addFaithfulAddr addFaithfulRawProgram addFaithfulProgramRowsBinding
    addFaithfulRawProgramDecodes addFaithfulInputsAgreeCore addFaithfulPcBoot
    addFaithfulRowsAligned addFaithfulBootSeed addFaithfulOutsideDefectRegion

#print axioms addFaithfulPaddedRawRootSoundness

end ZiskFv.Compliance.AddFaithfulPaddedRootSoundness
