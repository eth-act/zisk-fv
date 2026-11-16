import ZiskFv.Compliance.TraceLevelExport.CanonicalJalrWorld

/-!
# Two actual source-start JALR steps in one accepted physical world

Only physical0 and2 are RV instructions. Physical1/3 are their real terminal
AND rows; physical4 is a real lookahead ADD, not an omitted provider request.
The physical SailTrace carries the owning instruction's generated pre-state;
it does not posit executions at the auxiliary rows.
-/

namespace ZiskFv.Compliance.CanonicalJalrWorld

open Goldilocks Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open CanonicalSourceParser CanonicalExecutionRows SerializedExecutionRows RawProgramBinding
open ZiskFv.Compliance.Instantiation
open ZiskFv.Completeness.SailDecode
open AddFaithfulPaddedRootSoundness

/-- Real physical source starts, with no total family of auxiliary ZiskSteps. -/
def worldSourceIndex (i : Fin 2) : Fin 4 := ⟨2 * i.val, by omega⟩

def worldStart : Fin 1 → Fin worldTrace.programLength := fun _ => 0

theorem worldProgramRowsBinding :
    ProgramRowsBinding worldTrace worldStart (fun _ => 0) repeatJalrRawProgram := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' h
    fin_cases k; fin_cases k'; rfl
  · intro k
    fin_cases k; decide
  · intro k
    fin_cases k; decide
  · intro k k' h
    fin_cases k; fin_cases k'; exact absurd h (by decide)
  · intro k
    fin_cases k
    simp only [worldStart, repeatJalrRawProgram]
    rw [worldProgram_actual_source]
    exact ⟨rfl, by decide, rfl⟩
  · intro j
    fin_cases j
    · exact ⟨0, Or.inl rfl⟩
    · refine ⟨0, Or.inr ⟨worldAndProgramRow, ?_, rfl⟩⟩
      simpa only [repeatJalrRawProgram] using congrArg Prod.snd worldProgram_actual_source

private def worldMainIndex (i : Fin 5) : Fin worldTrace.mainTable.table.length :=
  Fin.cast (congrArg (fun table : Table FGL => table.table.length)
    worldTrace_mainTable_eq).symm i

private theorem worldMainGet (i : Fin 5) :
    worldTrace.mainTable.table.get (worldMainIndex i) = worldMainTable.table.get i := by
  simp [worldMainIndex, worldTrace_mainTable_eq]

private theorem worldMainAt (i : Fin 5) :
    mainRowWithRomAt worldTrace (worldMainIndex i) = worldMainRows[i.val]'i.isLt := by
  unfold mainRowWithRomAt
  rw [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get, worldMainGet]
  rw [worldTrace_mainTable_eq]
  convert worldMainTable_evalAt i using 1

@[simp] private theorem worldMainRaw0 :
    mainTableRowAtOrZero worldTrace.program worldTrace.mainTable 0 = worldRow0 := by
  simpa [mainRowWithRomAt, worldMainIndex, worldMainRows] using worldMainAt 0
@[simp] private theorem worldMainRaw1 :
    mainTableRowAtOrZero worldTrace.program worldTrace.mainTable 1 = worldRow1 := by
  simpa [mainRowWithRomAt, worldMainIndex, worldMainRows] using worldMainAt 1
@[simp] private theorem worldMainRaw2 :
    mainTableRowAtOrZero worldTrace.program worldTrace.mainTable 2 = worldRow2 := by
  simpa [mainRowWithRomAt, worldMainIndex, worldMainRows] using worldMainAt 2
@[simp] private theorem worldMainRaw3 :
    mainTableRowAtOrZero worldTrace.program worldTrace.mainTable 3 = worldRow3 := by
  simpa [mainRowWithRomAt, worldMainIndex, worldMainRows] using worldMainAt 3
@[simp] private theorem worldMainRaw4 :
    mainTableRowAtOrZero worldTrace.program worldTrace.mainTable 4 = worldRow4 := by
  simpa [mainRowWithRomAt, worldMainIndex, worldMainRows] using worldMainAt 4

def worldClaim (i : Fin 2) : Claim_jalr worldTrace (worldSourceIndex i) where
  imm := 1#12
  rs1 := .Regidx (2#5)
  rd := .Regidx (1#5)
  offset_bv := 0#64

/-- Both raw certificates use the same actual ROM/provider world. -/
def worldRawDecode (i : Fin 2) :
    RawProgramDecode worldTrace (worldSourceIndex i) (.jalr (worldClaim i))
      worldStart (fun _ => 0) repeatJalrRawProgram := by
  refine ⟨⟨RawProgramDecode_jalr.unaligned {
    raw := jalrExpansionRaw
    h_raw := rfl
    h_rows := ⟨jalrExpansionRows, jalrExpansionRows_spec.1, jalrExpansionRows_spec.2⟩
    h_offset_zero := rfl
    h_idx2 := ?_
    h_flag_add := ?_
    h_flag := ?_
    h_a_mask_lo := ?_
    h_a_mask_hi := ?_
    h_c1_zero := ?_
    h_offset_even := by decide
    h_target_nonneg := ?_
    h_target_lt := ?_
    hLineAdd := ?_
    hLineAnd := ?_ }⟩⟩
  · fin_cases i <;> norm_num [worldSourceIndex, worldTrace_mainTable_eq,
      worldMainTable, AddSpinWitness.mainRowsTable, worldMainRows]
  · fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, mainRomRowOf]
  · fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow1, worldRow3,
      worldRow1Template, worldRow3Template, mainRomRowOf]
  · fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow1, worldRow3,
      worldRow1Template, worldRow3Template, mainRomRowOf]
  · fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow1, worldRow3,
      worldRow1Template, worldRow3Template, mainRomRowOf]
  · fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow1, worldRow3,
      worldRow1Template, worldRow3Template, mainRomRowOf]
  · fin_cases i <;> norm_num [worldSourceIndex, mainOfTable, worldClaim,
      worldRow1, worldRow3, worldRow1Template, worldRow3Template, mainRomRowOf]
  · fin_cases i <;> norm_num [worldSourceIndex, mainOfTable, worldClaim,
      worldRow1, worldRow3, worldRow1Template, worldRow3Template, mainRomRowOf, GL_prime]
  · intro j hline
    fin_cases i <;> fin_cases j
    all_goals simp [worldSourceIndex, mainOfTable, worldTrace, worldProgram,
      worldAddProgramRow, worldAndProgramRow, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, mainRomRowOf] at hline
    all_goals exact ⟨0, rfl, rfl, rfl⟩
  · intro j hline
    fin_cases i <;> fin_cases j
    all_goals simp [worldSourceIndex, mainOfTable, worldTrace, worldProgram,
      worldAddProgramRow, worldAndProgramRow, worldRow1, worldRow3,
      worldRow1Template, worldRow3Template, mainRomRowOf] at hline
    all_goals exact ⟨0, rfl, rfl, rfl⟩

noncomputable def worldRowDecode (i : Fin 2) :
    RowDecode worldTrace (worldSourceIndex i) (.jalr (worldClaim i)) :=
  rowDecode_of_programDecode worldTrace (worldSourceIndex i)
    (programDecode_of_rawProgramDecode worldTrace (worldSourceIndex i) (.jalr (worldClaim i))
      worldStart (fun _ => 0) repeatJalrRawProgram worldProgramRowsBinding (worldRawDecode i))

/-- Owner pre-states; no execution is claimed at the auxiliary physical rows. -/
noncomputable def worldSailTrace : SailTrace 4 := fun r =>
  if r.val < 2 then repeatJalrInit else repeatJalrSecond

private theorem worldStateReads (i : Fin 2) :
    (worldSailTrace (worldSourceIndex i)).regs.get? Register.PC = some (0#64) ∧
    (worldSailTrace (worldSourceIndex i)).regs.get? Register.misa = some (4096#64) ∧
    read_xreg (2 : Fin 32) (worldSailTrace (worldSourceIndex i)) =
      EStateM.Result.ok (0#64) (worldSailTrace (worldSourceIndex i)) ∧
    Sail.readReg Register.cur_privilege (worldSailTrace (worldSourceIndex i)) =
      EStateM.Result.ok Privilege.Machine (worldSailTrace (worldSourceIndex i)) ∧
    Sail.readReg Register.mseccfg (worldSailTrace (worldSourceIndex i)) =
      EStateM.Result.ok (0#64) (worldSailTrace (worldSourceIndex i)) := by
  fin_cases i <;>
    simp [worldSailTrace, worldSourceIndex, repeatJalrSecond, retirePC, repeatJalrPost,
      repeatJalrInit, withMEnabled, write_reg_state, addFaithfulState, addFaithfulRegs,
      addFaithfulZeroRegs, addFaithfulMisa, x1, regidx_to_fin, read_xreg, reg_of_fin,
      Sail.readReg, PreSail.readReg, Std.ExtDHashMap.get?_insert]

private def worldInput : PureSpec.JalrInput :=
  { imm := 1#12, rs1_val := 0#64, rd := 1, PC := 0#64 }

/-- All current input/platform facts are DERIVED for the concrete generated states. -/
noncomputable def worldInputs (i : Fin 2) :
    Inputs_jalr worldTrace worldSailTrace (worldSourceIndex i) (worldClaim i) where
  jalr_input := worldInput
  misa_val := 4096#64
  mseccfg := 0#64
  h_rs1_start := by
    fin_cases i <;> norm_num [worldInput, worldSourceIndex, mainOfTable,
      worldRow0, worldRow2, worldRow0Template, worldRow2Template, mainRomRowOf]
  h_input_rd := rfl
  h_input_pc := (worldStateReads i).1
  h_input_misa := (worldStateReads i).2.1
  h_misa_c := by decide
  h_success := by decide
  h_input_imm := rfl
  h_input_rs1 := by simpa [worldClaim, regidx_to_fin] using (worldStateReads i).2.2.1
  h_cur_privilege := (worldStateReads i).2.2.2.1
  h_mseccfg := (worldStateReads i).2.2.2.2
  h_pc_bridge := by
    fin_cases i <;> norm_num [worldInput, worldSourceIndex, mainOfTable,
      worldRow0, worldRow2, worldRow0Template, worldRow2Template, mainRomRowOf]

private theorem worldLanes (i : Fin 2) :
    LaneBridge worldTrace (worldSailTrace (worldSourceIndex i)) (worldSourceIndex i).val := by
  have registerZero := ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (worldSailTrace (worldSourceIndex i)) (2 : Fin 32) (0#64) (worldStateReads i).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr selector pointer
    fin_cases i <;> norm_num [worldSourceIndex, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, worldAddBits, JalrSpinWitness.jalrAddBits,
      mainRomRowOf] at selector
  · intro r hr selector pointer
    fin_cases i <;> norm_num [worldSourceIndex, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, worldAddBits, JalrSpinWitness.jalrAddBits,
      mainRomRowOf] at selector
  · intro r hr selector pointer
    have r_eq : r = (2 : Fin 32) := by
      fin_cases i <;>
        simpa [worldSourceIndex, worldRow0, worldRow2, worldRow0Template,
          worldRow2Template, worldAddProgramRow, mainRomRowOf,
          Transpiler.wrap_to_regidx] using pointer.symm
    subst r
    rw [registerZero]
    fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, mainRomRowOf, ZiskFv.Trusted.lane_lo]
  · intro r hr selector pointer
    have r_eq : r = (2 : Fin 32) := by
      fin_cases i <;>
        simpa [worldSourceIndex, worldRow0, worldRow2, worldRow0Template,
          worldRow2Template, worldAddProgramRow, mainRomRowOf,
          Transpiler.wrap_to_regidx] using pointer.symm
    subst r
    rw [registerZero]
    fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, mainRomRowOf, ZiskFv.Trusted.lane_hi]

private theorem worldAvoid (i : Fin 2) :
    RowOutsideDefectRegion worldTrace (worldSourceIndex i) (.jalr (worldClaim i)) := by
  constructor
  · fin_cases i <;> norm_num [MainSequentialPcDomain, mainPcVal, worldSourceIndex,
      mainOfTable, worldRow0, worldRow2, worldRow0Template, worldRow2Template,
      mainRomRowOf, GL_prime]
  · intro pc hpc
    have zero : pc = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      fin_cases i <;> simpa [mainPcVal, worldSourceIndex, mainOfTable,
        worldRow0, worldRow2, worldRow0Template, worldRow2Template, mainRomRowOf] using hpc.symm
    subst pc
    decide

/-- Actual two-row physical-channel equality, NOT an assumed firstSound. -/
theorem worldPhysicalStepSound (i : Fin 2) :
    StepSound worldTrace worldSailTrace (worldSourceIndex i) (.jalr (worldClaim i))
      (worldRowDecode i) :=
  stepSound_of_evidence worldTrace worldSailTrace (worldSourceIndex i)
    (.jalr (worldClaim i)) (worldRowDecode i) (worldInputs i) trivial
    (worldAvoid i) (worldLanes i)

/-- The owner states really are generated by actual execute and retire. -/
theorem worldGeneratedHistory :
    SailEncodesToIn repeatJalrInit repeatJalrInstruction (repeatJalrRawProgram 0) ∧
    retirePC (sailStepPost repeatJalrInstruction (worldSailTrace (worldSourceIndex 0))) =
      worldSailTrace (worldSourceIndex 1) ∧
    retirePC (sailStepPost repeatJalrInstruction (worldSailTrace (worldSourceIndex 1))) =
      repeatJalrFinal := by
  refine ⟨repeatJalr_actual_encoder, ?_, ?_⟩
  · simp only [worldSailTrace, worldSourceIndex]
    rw [sailStepPost, repeatJalr_first_execution]
    rfl
  · simp only [worldSailTrace, worldSourceIndex]
    rw [sailStepPost, repeatedJalr_actual_sail_execution.2.2.2.1]
    rfl

/-- Explicit source/physical prefix and lookahead bounds in this SAME world. -/
theorem worldSourceBounds :
    sourceEnd repeatJalrLowerings = 4 ∧
    worldTrace.mainTable.table.length = 5 ∧
    (∀ i : Fin 2, (worldSourceIndex i).val = sourceStart repeatJalrLowerings i) ∧
    (∀ i : Fin 2, (worldSourceIndex i).val + 2 < worldTrace.mainTable.table.length) := by
  refine ⟨repeatJalr_sourceEnd, ?_, ?_, ?_⟩
  · rw [worldTrace_mainTable_eq, Table.table_length]
    rfl
  · intro i
    fin_cases i
    · rfl
    · have next := prefix_succ (sourceWidth repeatJalrLowerings) (0 : Fin 2)
      simpa [worldSourceIndex, sourceStart, sourceWidth, prefix_zero,
        repeatJalrLowerings_width] using next.symm
  · intro i
    rw [worldTrace_mainTable_eq, Table.table_length]
    fin_cases i <;> decide

/-- Parsing is DERIVED from the actual committed source rows and source starts.
The consumed endpoint4 is separate from the physical table height5. -/
theorem worldCanonicalParse :
    canonicalParse worldTrace (fun _ => 0) repeatJalrRawProgram 2 =
      some (List.ofFn (fun i => (⟨repeatJalrSelected i, repeatJalrLowerings i⟩ :
        Σ k, SuccessfulRowLowering (repeatJalrRawProgram k))), 4) := by
  have room : sourceEnd repeatJalrLowerings ≤ worldTrace.mainTable.table.length := by
    rw [worldSourceBounds.1, worldSourceBounds.2.1]
    decide
  have atPc : ∀ i : Fin 2, (mainOfTable worldTrace.program worldTrace.mainTable).pc
      (sourceStart repeatJalrLowerings i) = (0 : FGL) := by
    intro i
    rw [← worldSourceBounds.2.2.1 i]
    fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, mainRomRowOf]
  simpa only [repeatJalr_sourceEnd] using canonicalParse_complete worldTrace worldStart
    (fun _ => 0) repeatJalrRawProgram worldProgramRowsBinding repeatJalrSelected
    repeatJalrLowerings room atPc

/-- All displayed data and proofs refer to this one accepted provider world. -/
theorem worldNonvacuity :
    Nonempty (AcceptedZiskTrace 4) ∧
    ProgramRowsBinding worldTrace worldStart (fun _ => 0) repeatJalrRawProgram ∧
    (∀ i : Fin 2, StepSound worldTrace worldSailTrace (worldSourceIndex i)
      (.jalr (worldClaim i)) (worldRowDecode i)) ∧
    SailEncodesToIn repeatJalrInit repeatJalrInstruction (repeatJalrRawProgram 0) ∧
    (retirePC (sailStepPost repeatJalrInstruction (worldSailTrace (worldSourceIndex 0))) =
      worldSailTrace (worldSourceIndex 1)) ∧
    (∀ k : Fin 32, k ≠ 0 → repeatJalrInit.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64))) :=
  ⟨⟨worldTrace⟩, worldProgramRowsBinding, worldPhysicalStepSound,
    worldGeneratedHistory.1, worldGeneratedHistory.2.1, repeatJalrInit_regBoot⟩

end ZiskFv.Compliance.CanonicalJalrWorld
