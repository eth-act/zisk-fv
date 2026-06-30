import ZiskFv.AirsClean.Main.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean (boolF)
open ZiskFv.AirsClean.Main

private def mainFree : MainFreeCols :=
  { a_0 := 10
    a_1 := 11
    b_0 := 20
    b_1 := 21
    pc := 0
    m32 := 0
    ind_width := 8
    jmp_offset1 := 4
    jmp_offset2 := 8
    store_pc := 0
    im_high_degree_2 := 0
    segment_l1 := 0 }

private def mainRomFree : MainRomFreeCols :=
  { a_0 := 10
    a_1 := 11
    b_0 := 20
    b_1 := 21
    im_high_degree_2 := 0
    segment_l1 := 0
    main_step := 7 }

private def finOne : Fin 1 := ⟨0, by decide⟩

private def externalBits : RomFlagBits :=
  { a_src_imm := false
    a_src_mem := false
    is_precompiled := false
    b_src_imm := false
    b_src_mem := false
    is_external_op := true
    store_pc := false
    store_mem := false
    store_ind := false
    set_pc := false
    m32 := false
    b_src_ind := false
    a_src_reg := true
    b_src_reg := true
    store_reg := true }

private def internalFlagBits : RomFlagBits :=
  { a_src_imm := false
    a_src_mem := false
    is_precompiled := false
    b_src_imm := false
    b_src_mem := false
    is_external_op := false
    store_pc := false
    store_mem := false
    store_ind := false
    set_pc := false
    m32 := false
    b_src_ind := false
    a_src_reg := false
    b_src_reg := false
    store_reg := false }

private def internalCopyBits : RomFlagBits :=
  { a_src_imm := false
    a_src_mem := false
    is_precompiled := false
    b_src_imm := false
    b_src_mem := false
    is_external_op := false
    store_pc := false
    store_mem := false
    store_ind := false
    set_pc := true
    m32 := false
    b_src_ind := false
    a_src_reg := false
    b_src_reg := false
    store_reg := false }

private def romMsgOf (op flags : FGL) : ZiskFv.Channels.ZiskRomBus.ZiskRomMessage FGL :=
  { line := 0
    a_offset_imm0 := 1
    a_imm1 := 2
    b_offset_imm0 := 3
    b_imm1 := 4
    ind_width := 8
    op := op
    store_offset := 5
    jmp_offset1 := 4
    jmp_offset2 := 8
    flags := flags }

private def externalProgram : ZiskFv.AirsClean.ZiskInstructionRom.Program 1 :=
  fun _ => romMsgOf 99 (packFlags externalBits)

private def internalFlagProgram : ZiskFv.AirsClean.ZiskInstructionRom.Program 1 :=
  fun _ => romMsgOf 0 (packFlags internalFlagBits)

private def internalCopyProgram : ZiskFv.AirsClean.ZiskInstructionRom.Program 1 :=
  fun _ => romMsgOf 1 (packFlags internalCopyBits)

private def plainExternalRow : MainRow FGL :=
  mainRowOf (.external 99 true 30 31 0) mainFree

private def plainInternalFlagRow : MainRow FGL :=
  mainRowOf .internalFlag mainFree

private def plainInternalCopyRow : MainRow FGL :=
  mainRowOf (.internalCopyB 42) mainFree

private def romExternalRow : MainRowWithRom FGL :=
  mainRomRowOf (externalProgram finOne) externalBits (.external true 30 31) mainRomFree

private def romInternalFlagRow : MainRowWithRom FGL :=
  mainRomRowOf (internalFlagProgram finOne) internalFlagBits .internalFlag mainRomFree

private def romInternalCopyRow : MainRowWithRom FGL :=
  mainRomRowOf (internalCopyProgram finOne) internalCopyBits .internalCopyB mainRomFree

private theorem plainExternalWitness :
    ∃ row : MainRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  refine ⟨plainExternalRow, ?_⟩
  intro data hint
  refine ⟨.external 99 true 30 31 0, mainFree, ?_⟩
  rfl

private theorem plainInternalFlagWitness :
    ∃ row : MainRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  refine ⟨plainInternalFlagRow, ?_⟩
  intro data hint
  refine ⟨.internalFlag, mainFree, ?_⟩
  rfl

private theorem plainInternalCopyWitness :
    ∃ row : MainRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  refine ⟨plainInternalCopyRow, ?_⟩
  intro data hint
  refine ⟨.internalCopyB 42, mainFree, ?_⟩
  rfl

private theorem romMemExternalWitness :
    ∃ row : MainRowWithRom FGL, ∀ data hint,
      (circuitWithRomAndMemBus 1 externalProgram).ProverAssumptions row data hint := by
  refine ⟨romExternalRow, ?_⟩
  intro data hint
  refine ⟨finOne, externalBits, .external true 30 31, mainRomFree, rfl, ?_, ?_, ?_, rfl⟩
  · simp [MainRomExecKind.Coherent, externalBits]
  · simp [MainRomSourceGuard, externalBits, boolF]
  · simp [MainRomAddressGuard, externalBits, boolF]

private theorem romMemInternalFlagWitness :
    ∃ row : MainRowWithRom FGL, ∀ data hint,
      (circuitWithRomAndMemBus 1 internalFlagProgram).ProverAssumptions row data hint := by
  refine ⟨romInternalFlagRow, ?_⟩
  intro data hint
  refine ⟨finOne, internalFlagBits, .internalFlag, mainRomFree, rfl, ?_, ?_, ?_, rfl⟩
  · simp [MainRomExecKind.Coherent, internalFlagBits, internalFlagProgram, romMsgOf]
  · simp [MainRomSourceGuard, internalFlagBits, boolF]
  · simp [MainRomAddressGuard, internalFlagBits, boolF]

private theorem romMemInternalCopyWitness :
    ∃ row : MainRowWithRom FGL, ∀ data hint,
      (circuitWithRomAndMemBus 1 internalCopyProgram).ProverAssumptions row data hint := by
  refine ⟨romInternalCopyRow, ?_⟩
  intro data hint
  refine ⟨finOne, internalCopyBits, .internalCopyB, mainRomFree, rfl, ?_, ?_, ?_, rfl⟩
  · simp [MainRomExecKind.Coherent, internalCopyBits, internalCopyProgram, romMsgOf]
  · simp [MainRomSourceGuard, internalCopyBits, boolF]
  · simp [MainRomAddressGuard, internalCopyBits, boolF]

private theorem romMemOpExternalWitness :
    ∃ row : MainRowWithRom FGL, ∀ data hint,
      (circuitWithRomMemAndOpBus 1 externalProgram).ProverAssumptions row data hint := by
  refine ⟨romExternalRow, ?_⟩
  intro data hint
  refine ⟨finOne, externalBits, .external true 30 31, mainRomFree, rfl, ?_, ?_, ?_, rfl⟩
  · simp [MainRomExecKind.Coherent, externalBits]
  · simp [MainRomSourceGuard, externalBits, boolF]
  · simp [MainRomAddressGuard, externalBits, boolF]

private theorem romMemOpInternalFlagWitness :
    ∃ row : MainRowWithRom FGL, ∀ data hint,
      (circuitWithRomMemAndOpBus 1 internalFlagProgram).ProverAssumptions row data hint := by
  refine ⟨romInternalFlagRow, ?_⟩
  intro data hint
  refine ⟨finOne, internalFlagBits, .internalFlag, mainRomFree, rfl, ?_, ?_, ?_, rfl⟩
  · simp [MainRomExecKind.Coherent, internalFlagBits, internalFlagProgram, romMsgOf]
  · simp [MainRomSourceGuard, internalFlagBits, boolF]
  · simp [MainRomAddressGuard, internalFlagBits, boolF]

private theorem romMemOpInternalCopyWitness :
    ∃ row : MainRowWithRom FGL, ∀ data hint,
      (circuitWithRomMemAndOpBus 1 internalCopyProgram).ProverAssumptions row data hint := by
  refine ⟨romInternalCopyRow, ?_⟩
  intro data hint
  refine ⟨finOne, internalCopyBits, .internalCopyB, mainRomFree, rfl, ?_, ?_, ?_, rfl⟩
  · simp [MainRomExecKind.Coherent, internalCopyBits, internalCopyProgram, romMsgOf]
  · simp [MainRomSourceGuard, internalCopyBits, boolF]
  · simp [MainRomAddressGuard, internalCopyBits, boolF]

theorem completeness_witness_main :
    (∃ row : MainRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint)
    ∧ (∃ row : MainRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint)
    ∧ (∃ row : MainRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint)
    ∧ (∃ row : MainRowWithRom FGL, ∀ data hint,
        (circuitWithRomAndMemBus 1 externalProgram).ProverAssumptions row data hint)
    ∧ (∃ row : MainRowWithRom FGL, ∀ data hint,
        (circuitWithRomAndMemBus 1 internalFlagProgram).ProverAssumptions row data hint)
    ∧ (∃ row : MainRowWithRom FGL, ∀ data hint,
        (circuitWithRomAndMemBus 1 internalCopyProgram).ProverAssumptions row data hint)
    ∧ (∃ row : MainRowWithRom FGL, ∀ data hint,
        (circuitWithRomMemAndOpBus 1 externalProgram).ProverAssumptions row data hint)
    ∧ (∃ row : MainRowWithRom FGL, ∀ data hint,
        (circuitWithRomMemAndOpBus 1 internalFlagProgram).ProverAssumptions row data hint)
    ∧ (∃ row : MainRowWithRom FGL, ∀ data hint,
        (circuitWithRomMemAndOpBus 1 internalCopyProgram).ProverAssumptions row data hint) := by
  exact ⟨plainExternalWitness, plainInternalFlagWitness, plainInternalCopyWitness,
    romMemExternalWitness, romMemInternalFlagWitness, romMemInternalCopyWitness,
    romMemOpExternalWitness, romMemOpInternalFlagWitness, romMemOpInternalCopyWitness⟩

#print axioms completeness_witness_main

end ZiskFv.TrustConsistency
