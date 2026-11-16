import ZiskFv.Compliance.TraceLevelExport.RawProgramBinding
import ZiskFv.Compliance.AcceptedZiskTrace.MemProviders
import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusSourceExclusivity

/-!
# Complete committed-ROM selector provenance for mutable-memory presence

ProgramRowsBinding covers EVERY committed ROM row, not just executed source
heads. The generic serializer makes b_src_mem and b_src_ind exclusive even for
provider rows outside the architectural source prefix. This file changes no
validator and adds no caller-side provider exclusion.
-/

namespace ZiskFv.Compliance.SourceMutableMemoryPresence.SourceFlags

open Goldilocks Air.Flat
open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.AirsClean.Main
open RawProgramBinding RomDecodeBinding
open ZiskFv.AirsClean.FullEnsemble

private theorem serialized_flag_sources (line : FGL) (raw : BitVec 32) :
    ((romMessagesOfRaw line raw).1.flags = 0 ∨
      ∃ e : aeneas_extract.ZiskInstExtract,
        (romMessagesOfRaw line raw).1.flags = packFlags (romFlagBitsOfExtract e)) ∧
      ∀ row, (romMessagesOfRaw line raw).2 = some row →
        row.flags = 0 ∨ ∃ e : aeneas_extract.ZiskInstExtract,
          row.flags = packFlags (romFlagBitsOfExtract e) := by
  unfold romMessagesOfRaw
  split
  · split_ifs
    · constructor
      · exact Or.inr ⟨_, rfl⟩
      · intro row same
        cases Option.some.inj same
        exact Or.inr ⟨_, rfl⟩
    · constructor
      · exact Or.inr ⟨_, rfl⟩
      · intro row same
        simp at same
  · constructor
    · unfold romMessageOfRaw
      split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    · intro row same
      simp at same

private theorem program_flag_sources
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram) (j : Fin trace.programLength) :
    (trace.program j).flags = 0 ∨ ∃ e : aeneas_extract.ZiskInstExtract,
      (trace.program j).flags = packFlags (romFlagBitsOfExtract e) := by
  obtain ⟨_, _, _, _, rows, covers⟩ := binding
  obtain ⟨k, first | ⟨row, second, position⟩⟩ := covers j
  · rw [first, (rows k).1]
    exact (serialized_flag_sources (addr k) (rawProgram k)).1
  · have source := rows k
    dsimp only at source
    rw [second] at source
    obtain ⟨bound, rowEq⟩ := source.2
    have indexEq : j = ⟨(start k).val + 1, bound⟩ := Fin.ext position
    rw [indexEq, rowEq]
    exact (serialized_flag_sources (addr k) (rawProgram k)).2 row second

private def packedNat (b : RomFlagBits) : Nat :=
  1 + 2 * b.a_src_imm.toNat + 4 * b.a_src_mem.toNat + 8 * b.is_precompiled.toNat +
    16 * b.b_src_imm.toNat + 32 * b.b_src_mem.toNat + 64 * b.is_external_op.toNat +
    128 * b.store_pc.toNat + 256 * b.store_mem.toNat + 512 * b.store_ind.toNat +
    1024 * b.set_pc.toNat + 2048 * b.m32.toNat + 4096 * b.b_src_ind.toNat +
    8192 * b.a_src_reg.toNat + 16384 * b.b_src_reg.toNat + 32768 * b.store_reg.toNat

private theorem boolF_cast (b : Bool) :
    ZiskFv.AirsClean.boolF b = (b.toNat : FGL) := by
  cases b <;> rfl

private theorem packFlags_nonzero (b : RomFlagBits) : packFlags b ≠ 0 := by
  have bitBound (x : Bool) : x.toNat ≤ 1 := by cases x <;> decide
  have b0 := bitBound b.a_src_imm
  have b1 := bitBound b.a_src_mem
  have b2 := bitBound b.is_precompiled
  have b3 := bitBound b.b_src_imm
  have b4 := bitBound b.b_src_mem
  have b5 := bitBound b.is_external_op
  have b6 := bitBound b.store_pc
  have b7 := bitBound b.store_mem
  have b8 := bitBound b.store_ind
  have b9 := bitBound b.set_pc
  have b10 := bitBound b.m32
  have b11 := bitBound b.b_src_ind
  have b12 := bitBound b.a_src_reg
  have b13 := bitBound b.b_src_reg
  have b14 := bitBound b.store_reg
  have positive : 0 < packedNat b := by dsimp only [packedNat]; omega
  have bound : packedNat b < GL_prime := by dsimp only [packedNat]; omega
  have castEq : (packedNat b : FGL) = packFlags b := by
    simp only [packedNat, packFlags, boolF_cast]
    push_cast
    ring
  intro zero
  rw [← castEq] at zero
  have value := congrArg Fin.val zero
  rw [Fin.val_natCast, Nat.mod_eq_of_lt bound] at value
  change packedNat b = 0 at value
  omega

private theorem bool_of_booleanity {x : FGL} (boolean : x * (1 - x) = 0) :
    ∃ b : Bool, x = ZiskFv.AirsClean.boolF b := by
  rcases zero_or_one_of_bool boolean with zero | one
  · exact ⟨false, by simpa [ZiskFv.AirsClean.boolF] using zero⟩
  · exact ⟨true, by simpa [ZiskFv.AirsClean.boolF] using one⟩

/-- All six current-access source selectors come from ONE real committed
serializer row, including for provider rows outside the source prefix. -/
theorem main_memory_selector_source
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    {table : Table FGL} (tableMember : table ∈ trace.witness.allTables)
    (componentEq : table.component = componentWithRomMemAndOpBus trace.programLength trace.program)
    {raw : Array FGL} (rawMember : raw ∈ table.table) :
    let value := eval (table.environment raw)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    ∃ extract : aeneas_extract.ZiskInstExtract,
      value.rom.b_src_mem = ZiskFv.AirsClean.boolF (romFlagBitsOfExtract extract).b_src_mem ∧
      value.rom.b_src_ind = ZiskFv.AirsClean.boolF (romFlagBitsOfExtract extract).b_src_ind ∧
      value.rom.b_src_reg = ZiskFv.AirsClean.boolF (romFlagBitsOfExtract extract).b_src_reg ∧
      value.rom.store_mem = ZiskFv.AirsClean.boolF (romFlagBitsOfExtract extract).store_mem ∧
      value.rom.store_ind = ZiskFv.AirsClean.boolF (romFlagBitsOfExtract extract).store_ind ∧
      value.rom.store_reg = ZiskFv.AirsClean.boolF (romFlagBitsOfExtract extract).store_reg := by
  intro value
  have constraints := trace.constraints_hold table tableMember raw rawMember
  rw [componentEq] at constraints
  have ieo := is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints
    trace.programLength trace.program _ constraints
  obtain ⟨m32, setPc, storePc, aImm, aMem, precompiled, bImm, bMem, storeMem,
    storeInd, bInd, aReg, bReg, storeReg⟩ :=
    romBoolSpec_of_componentWithRomMemAndOpBus_constraints
      trace.programLength trace.program _ constraints
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ :=
    eval_flagBool_bridge (table.environment raw)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
  obtain ⟨d0, p0⟩ := bool_of_booleanity (x := value.core.is_external_op) (e0.symm.trans ieo)
  obtain ⟨d1, p1⟩ := bool_of_booleanity (x := value.core.m32) (e1.symm.trans m32)
  obtain ⟨d2, p2⟩ := bool_of_booleanity (x := value.core.set_pc) (e2.symm.trans setPc)
  obtain ⟨d3, p3⟩ := bool_of_booleanity (x := value.core.store_pc) (e3.symm.trans storePc)
  obtain ⟨d4, p4⟩ := bool_of_booleanity (x := value.rom.a_src_imm) (e4.symm.trans aImm)
  obtain ⟨d5, p5⟩ := bool_of_booleanity (x := value.rom.a_src_mem) (e5.symm.trans aMem)
  obtain ⟨d6, p6⟩ := bool_of_booleanity (x := value.rom.is_precompiled) (e6.symm.trans precompiled)
  obtain ⟨d7, p7⟩ := bool_of_booleanity (x := value.rom.b_src_imm) (e7.symm.trans bImm)
  obtain ⟨d8, p8⟩ := bool_of_booleanity (x := value.rom.b_src_mem) (e8.symm.trans bMem)
  obtain ⟨d9, p9⟩ := bool_of_booleanity (x := value.rom.store_mem) (e9.symm.trans storeMem)
  obtain ⟨d10, p10⟩ := bool_of_booleanity (x := value.rom.store_ind) (e10.symm.trans storeInd)
  obtain ⟨d11, p11⟩ := bool_of_booleanity (x := value.rom.b_src_ind) (e11.symm.trans bInd)
  obtain ⟨d12, p12⟩ := bool_of_booleanity (x := value.rom.a_src_reg) (e12.symm.trans aReg)
  obtain ⟨d13, p13⟩ := bool_of_booleanity (x := value.rom.b_src_reg) (e13.symm.trans bReg)
  obtain ⟨d14, p14⟩ := bool_of_booleanity (x := value.rom.store_reg) (e14.symm.trans storeReg)
  let bits : RomFlagBits :=
    { a_src_imm := d4, a_src_mem := d5, is_precompiled := d6,
      b_src_imm := d7, b_src_mem := d8, is_external_op := d0,
      store_pc := d3, store_mem := d9, store_ind := d10, set_pc := d2,
      m32 := d1, b_src_ind := d11, a_src_reg := d12, b_src_reg := d13, store_reg := d14 }
  have packed : romFlags value = packFlags bits := by
    simp only [romFlags, packFlags, bits, p0, p1, p2, p3, p4, p5, p6, p7,
      p8, p9, p10, p11, p12, p13, p14]
  have image := romSpec_of_componentWithRomMemAndOpBus_constraints
    trace.programLength trace.program _ constraints
  obtain ⟨j, messageEq⟩ := image
  have flagsEq : romFlags value = (trace.program j).flags := by
    have fields := congrArg ZiskFv.Channels.ZiskRomBus.ZiskRomMessage.flags messageEq
    simpa only [eval_romMessageExpr] using fields
  rcases program_flag_sources trace start addr rawProgram binding j with zero | serialized
  · exact False.elim (packFlags_nonzero bits (packed.symm.trans (flagsEq.trans zero)))
  · obtain ⟨extract, source⟩ := serialized
    have bitsEq : bits = romFlagBitsOfExtract extract :=
      packFlags_inj (packed.symm.trans (flagsEq.trans source))
    refine ⟨extract, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← bitsEq]; exact p8
    · rw [← bitsEq]; exact p11
    · rw [← bitsEq]; exact p13
    · rw [← bitsEq]; exact p9
    · rw [← bitsEq]; exact p10
    · rw [← bitsEq]; exact p14

private theorem eq_of_selected {α : Type} [DecidableEq α] {x y : α}
    (selected : ZiskFv.AirsClean.boolF (decide (x = y)) = 1) : x = y := by
  by_cases same : x = y
  · exact same
  · simp [same, ZiskFv.AirsClean.boolF] at selected

theorem main_b_mem_ind_exclusive
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    {table : Table FGL} (tableMember : table ∈ trace.witness.allTables)
    (componentEq : table.component = componentWithRomMemAndOpBus trace.programLength trace.program)
    {raw : Array FGL} (rawMember : raw ∈ table.table) :
    let value := eval (table.environment raw)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    ¬ (value.rom.b_src_mem = 1 ∧ value.rom.b_src_ind = 1) := by
  intro value both
  obtain ⟨extract, mem, ind, _⟩ :=
    main_memory_selector_source trace start addr rawProgram binding tableMember componentEq rawMember
  have sourceMem : extract.b_src = zisk_inst.SRC_MEM := eq_of_selected (mem.symm.trans both.1)
  have sourceInd : extract.b_src = zisk_inst.SRC_IND := eq_of_selected (ind.symm.trans both.2)
  have distinct : zisk_inst.SRC_MEM.val ≠ zisk_inst.SRC_IND.val := by
    norm_num [zisk_inst.SRC_MEM, zisk_inst.SRC_IND]
  exact distinct (congrArg UScalar.val (sourceMem.symm.trans sourceInd))

theorem main_b_ind_sum
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    {table : Table FGL} (tableMember : table ∈ trace.witness.allTables)
    (componentEq : table.component = componentWithRomMemAndOpBus trace.programLength trace.program)
    {raw : Array FGL} (rawMember : raw ∈ table.table) :
    let value := eval (table.environment raw)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    value.rom.b_src_ind = 1 →
      value.rom.b_src_mem + value.rom.b_src_ind + value.rom.b_src_reg = 1 := by
  intro value selected
  obtain ⟨extract, mem, ind, reg, _⟩ :=
    main_memory_selector_source trace start addr rawProgram binding tableMember componentEq rawMember
  have source : extract.b_src = zisk_inst.SRC_IND := eq_of_selected (ind.symm.trans selected)
  rw [mem, ind, reg]
  norm_num [romFlagBitsOfExtract, source, ZiskFv.AirsClean.boolF,
    zisk_inst.SRC_IND, zisk_inst.SRC_MEM, zisk_inst.SRC_REG]

theorem main_store_ind_sum
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    {table : Table FGL} (tableMember : table ∈ trace.witness.allTables)
    (componentEq : table.component = componentWithRomMemAndOpBus trace.programLength trace.program)
    {raw : Array FGL} (rawMember : raw ∈ table.table) :
    let value := eval (table.environment raw)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    value.rom.store_ind = 1 →
      value.rom.store_mem + value.rom.store_ind + value.rom.store_reg = 1 := by
  intro value selected
  obtain ⟨extract, _, _, _, mem, ind, reg⟩ :=
    main_memory_selector_source trace start addr rawProgram binding tableMember componentEq rawMember
  have source : extract.store = zisk_inst.STORE_IND := eq_of_selected (ind.symm.trans selected)
  rw [mem, ind, reg]
  norm_num [romFlagBitsOfExtract, source, ZiskFv.AirsClean.boolF,
    zisk_inst.STORE_IND, zisk_inst.STORE_MEM, zisk_inst.STORE_REG]

/-- Source provenance rules out the store-side Main minus-two self-provider,
which Booleanity alone would leave reachable. -/
theorem not_main_store_provider
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    {requestTable : Table FGL} {requestRow : Array FGL} {request : Interaction FGL}
    {requestMult : Expression FGL}
    {requestMessage : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (evaluated : request =
      ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted requestMult requestMessage).toRaw).eval
        (requestTable.environment requestRow))
    (storeOp : (eval (requestTable.environment requestRow) requestMessage).mem_op = 2)
    {multiplicity addressSpace : FGL} :
    ¬ ActiveMainSelfMemProviderRowMatchSpec trace.program trace.witness requestTable
      requestRow request requestMessage multiplicity addressSpace := by
  intro provider
  rcases provider with
    ⟨interaction, _, sameMessage, nonpull, _, table, tableMember, _,
      raw, rawMember, _, componentEq, branch⟩
  let v := (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
  let value := eval (table.environment raw) v
  have opcode {mult : Expression FGL}
      {message : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
      (providerEval : interaction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mult message).toRaw).eval
          (table.environment raw)) :
      (eval (table.environment raw) message).mem_op = 2 := by
    have rawEq :
        (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mult message).toRaw).eval
          (table.environment raw)).msg =
        (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted requestMult requestMessage).toRaw).eval
          (requestTable.environment requestRow)).msg := by
      rw [← providerEval, ← evaluated]
      exact sameMessage
    exact (memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq rawEq).trans storeOp
  obtain ⟨aMem, aReg, bMem, bInd, bReg, cMem, cInd, cReg⟩ :=
    main_source_flags_boolean componentEq (trace.constraints_hold table tableMember) rawMember
  have exclusive := main_b_mem_ind_exclusive trace start addr rawProgram binding
    tableMember componentEq rawMember
  rcases branch with aPre | aCurrent | bPre | bCurrent | cPre | cCurrent
  · have impossible := opcode aPre.1
    rw [eval_aRegPreMessageExpr] at impossible
    change (3 : FGL) = 2 at impossible
    exact (by decide : (3 : FGL) ≠ 2) impossible
  · have impossible := opcode aCurrent.1
    rw [eval_aMemMessageExpr] at impossible
    change value.rom.a_src_mem + 3 * value.rom.a_src_reg = 2 at impossible
    rcases zero_or_one_of_bool aMem with hm | hm <;>
      rcases zero_or_one_of_bool aReg with hr | hr <;>
      rw [hm, hr] at impossible <;> norm_num at impossible
    all_goals exact absurd impossible (by decide)
  · have impossible := opcode bPre.1
    rw [eval_bRegPreMessageExpr] at impossible
    change (3 : FGL) = 2 at impossible
    exact (by decide : (3 : FGL) ≠ 2) impossible
  · have impossible := opcode bCurrent.1
    rw [eval_bMemMessageExpr] at impossible
    change value.rom.b_src_mem + value.rom.b_src_ind + 3 * value.rom.b_src_reg = 2
      at impossible
    rcases zero_or_one_of_bool bMem with hm | hm <;>
      rcases zero_or_one_of_bool bInd with hi | hi <;>
      rcases zero_or_one_of_bool bReg with hr | hr <;>
      rw [hm, hi, hr] at impossible <;> norm_num at impossible
    all_goals first
      | exact absurd impossible (by decide)
      | exact exclusive ⟨hm, hi⟩
  · have impossible := opcode cPre.1
    rw [eval_cRegPreMessageExpr] at impossible
    change (3 : FGL) = 2 at impossible
    exact (by decide : (3 : FGL) ≠ 2) impossible
  · have operation := opcode cCurrent.1
    rw [eval_cMemMessageExpr] at operation
    change 2 * (value.rom.store_mem + value.rom.store_ind) +
      3 * value.rom.store_reg = 2 at operation
    rcases zero_or_one_of_bool cMem with hm | hm <;>
      rcases zero_or_one_of_bool cInd with hi | hi <;>
      rcases zero_or_one_of_bool cReg with hr | hr <;>
      rw [hm, hi, hr] at operation <;> norm_num at operation
    all_goals first
      | exact absurd operation (by decide)
      | apply nonpull
        rw [cCurrent.1, memBus_emitted_eval_mult]
        change (-1 : FGL) * Expression.eval (table.environment raw)
          (v.rom.store_mem + v.rom.store_ind + v.rom.store_reg) = -1
        have scalarSum :
            Expression.eval (table.environment raw)
                (v.rom.store_mem + v.rom.store_ind + v.rom.store_reg) =
              value.rom.store_mem + value.rom.store_ind + value.rom.store_reg :=
          eval_cSourceSumExpr (table.environment raw) v
        rw [scalarSum]
        change (-1 : FGL) *
          (value.rom.store_mem + value.rom.store_ind + value.rom.store_reg) = -1
        rw [hm, hi, hr]
        norm_num

theorem not_boundary_data_provider
    {n : Nat} (trace : AcceptedZiskTrace n)
    {requestTable : Table FGL} {requestRow : Array FGL} {request : Interaction FGL}
    {requestMult : Expression FGL}
    {requestMessage : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (evaluated : request =
      ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted requestMult requestMessage).toRaw).eval
        (requestTable.environment requestRow))
    (dataOp : (eval (requestTable.environment requestRow) requestMessage).mem_op = 1 ∨
      (eval (requestTable.environment requestRow) requestMessage).mem_op = 2)
    {multiplicity addressSpace : FGL} :
    ¬ ActiveMainRegisterBoundaryProviderRowMatchSpec trace.program trace.witness requestTable
      requestRow request requestMessage multiplicity addressSpace := by
  rintro ⟨provider, _, sameMessage, _, _, table, _, providerMember, componentEq⟩
  rcases exists_registerBoundary_mem_row_eval_of_interaction_mem componentEq providerMember with
    ⟨row, _, providerEval⟩ | ⟨row, _, providerEval⟩
  all_goals
    have rawEq : provider.msg =
        (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted requestMult requestMessage).toRaw).eval
          (requestTable.environment requestRow)).msg := by
      rw [← evaluated]
      exact sameMessage
    rw [providerEval] at rawEq
    have opcode := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq rawEq
    first
    | rw [ZiskFv.AirsClean.RegisterBoundary.eval_bootMessageExpr] at opcode
    | rw [ZiskFv.AirsClean.RegisterBoundary.eval_reloadMessageExpr] at opcode
    change (3 : FGL) = (eval (requestTable.environment requestRow) requestMessage).mem_op at opcode
    rcases dataOp with read | store
    · rw [read] at opcode
      exact (by decide : (3 : FGL) ≠ 1) opcode
    · rw [store] at opcode
      exact (by decide : (3 : FGL) ≠ 2) opcode

end ZiskFv.Compliance.SourceMutableMemoryPresence.SourceFlags
