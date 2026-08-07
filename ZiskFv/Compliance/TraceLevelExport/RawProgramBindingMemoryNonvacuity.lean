import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingLoadStore
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification

/-!
# Raw memory-program binding non-vacuity

An all-empty execution witness can still commit a non-empty ROM image.  This
kernel witness uses that separation to exercise production serialization for
SD, LD at offset zero, and LD at signed offset `-8`, without fabricating a
mutable-memory execution timeline.
-/

open Goldilocks
open Air.Flat
open ZiskFv.Compliance.Extraction
  (defCtx decode_i_bounds decode_s_bounds load_op_typed_ok store_op_typed_ok ind_width_set8
   decode_extract_ok from_inst_full_fields load_static_pins_of)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open Aeneas Aeneas.Std Result zisk_core

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

def memorySdRow : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 2, b_imm1 := 0,
    ind_width := 8, op := 1, store_offset := 0, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := 25089 }

def memoryLdZeroRow : ZiskRomMessage FGL :=
  { line := 4, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
    ind_width := 8, op := 1, store_offset := 3, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := 45057 }

def memoryLdNegativeRow : ZiskRomMessage FGL :=
  { line := 8, a_offset_imm0 := 1, a_imm1 := 0,
    b_offset_imm0 := 18446744069414584313, b_imm1 := 0,
    ind_width := 8, op := 1, store_offset := 4, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := 45057 }

def memoryProgram : Program 3
  | ⟨0, _⟩ => memorySdRow
  | ⟨1, _⟩ => memoryLdZeroRow
  | ⟨2, _⟩ => memoryLdNegativeRow

private def emptyData : ProverData FGL := fun _ _ => #[]

private def memoryWitness : EnsembleWitness (fullRv64imEnsemble 3 memoryProgram).ensemble :=
  EnsembleWitness.ofRows (fullRv64imEnsemble 3 memoryProgram).ensemble emptyData ()
    (fun _ => []) (by intro i row hrow; simp at hrow)
    (by intro i columns hcolumns; simp)

private theorem memoryWitness_verifier :
    (fullRv64imEnsemble 3 memoryProgram).ensemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 3 memoryProgram).verifier_empty

private theorem memoryWitness_mutable_tables_empty (table : Table FGL)
    (hmem : table ∈ memoryWitness.allTables)
    (hcomp : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · exfalso
    rw [hv, EnsembleWitness.verifierTable_component] at hcomp
    have hvnil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 3 memoryProgram
    rw [hcomp,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at hvnil
    exact absurd hvnil (by simp)
  · simp only [memoryWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [EnsembleWitness.tableAt, Table.table]
    split <;> rfl

private theorem memoryWitness_not_mutableMemPresent :
    ¬ MutableMemPresent memoryWitness := by
  intro hpresent
  obtain ⟨table, hmem, hcomp, hlen⟩ := hpresent
  have htable := memoryWitness_mutable_tables_empty table hmem hcomp
  exact absurd hlen (by simp [htable])

private theorem memoryWitness_constraints : memoryWitness.Constraints := by
  refine memoryWitness.constraints_of_tables memoryWitness_verifier ?_
  intro t ht
  simp only [memoryWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
  obtain ⟨i, rfl⟩ := ht
  simp [Air.Flat.Table.Constraints, EnsembleWitness.tableAt, Table.table]
  split <;> simp

private theorem memoryWitness_balanced : memoryWitness.BalancedChannels := by
  refine memoryWitness.balancedChannels_of_tables memoryWitness_verifier ?_
  intro channel _
  have hnil : memoryWitness.tables.flatMap (·.interactionsWith channel) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro t ht
    simp only [memoryWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [Air.Flat.Table.interactionsWith, EnsembleWitness.tableAt, Table.table]
    split <;> simp
  rw [hnil]
  exact balancedInteractions_of_present (Or.symm (Nat.eq_zero_or_pos _)) []
    (by simp) (by simp)

private theorem memoryWitness_transitions : memoryWitness.TransitionConstraints := by
  intro table hmem
  rw [Table.TransitionConstraints]
  intro index
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hverifier | htable
  · subst table
    simp [EnsembleWitness.verifierTable]
  · simp only [memoryWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at htable
    obtain ⟨i, rfl⟩ := htable
    change Fin 0 at index
    exact Fin.elim0 index

private theorem memoryWitness_cyclic :
    memoryWitness.CyclicSuccessorTransitionConstraints := by
  intro table hmem
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hverifier | htable
  · subst table
    simp [EnsembleWitness.verifierTable]
  · simp only [memoryWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at htable
    obtain ⟨i, rfl⟩ := htable
    change Fin 0 at index
    exact Fin.elim0 index

def memoryAcceptedTrace : AcceptedZiskTrace 0 where
  programLength := 3
  program := memoryProgram
  witness := memoryWitness
  constraints_hold := memoryWitness_constraints
  channels_balanced := memoryWitness_balanced
  mem_replay_table := fun h => absurd h memoryWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h memoryWitness_not_mutableMemPresent
  transitions_hold := memoryWitness_transitions
  cyclic_successor_transitions_hold := memoryWitness_cyclic
  main_height := by intro table _ _ i; exact i.elim0

def memoryAddr : Fin memoryAcceptedTrace.programLength → FGL
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 8

def memoryRawProgram : Fin memoryAcceptedTrace.programLength → BitVec 32
  | ⟨0, _⟩ => ZiskFv.Completeness.Rv64imShapes.rawSType 0 2 1 3
  | ⟨1, _⟩ => ZiskFv.Completeness.Rv64imShapes.rawIType 0 1 3 3 0x03
  | ⟨2, _⟩ => ZiskFv.Completeness.Rv64imShapes.rawIType 4088 1 3 4 0x03

private def operandFields (before after : zisk_inst_builder.ZiskInstBuilder) : Prop :=
  after.i.a_src = before.i.a_src
    ∧ after.i.a_use_sp_imm1 = before.i.a_use_sp_imm1
    ∧ after.i.a_offset_imm0 = before.i.a_offset_imm0
    ∧ after.i.b_src = before.i.b_src
    ∧ after.i.b_use_sp_imm1 = before.i.b_use_sp_imm1
    ∧ after.i.b_offset_imm0 = before.i.b_offset_imm0

private theorem operandFields_trans {a b c : zisk_inst_builder.ZiskInstBuilder}
    (hab : operandFields a b) (hbc : operandFields b c) : operandFields a c := by
  rcases hab with ⟨ha1, ha2, ha3, hb1, hb2, hb3⟩
  rcases hbc with ⟨ha1', ha2', ha3', hb1', hb2', hb3'⟩
  exact ⟨ha1'.trans ha1, ha2'.trans ha2, ha3'.trans ha3,
    hb1'.trans hb1, hb2'.trans hb2, hb3'.trans hb3⟩

private theorem operandFields_op_zisk (self z : zisk_inst_builder.ZiskInstBuilder)
    (op : zisk_ops.ZiskOp) (h : self.op_zisk op = ok z) : operandFields self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from, Bind.bind] at h
  obtain ⟨ot, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨b, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨cval, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zot, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨i1, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨mval, _, h4⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hself1
  rw [Result.ok.injEq] at h h4
  subst h
  subst h4
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem operandFields_ind_width (self z : zisk_inst_builder.ZiskInstBuilder)
    (w : Std.U64) (h : self.ind_width w = ok z) : operandFields self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.ind_width] at h
  split at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst z;
       exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    | simp at h

private theorem operandFields_store_ind (self z : zisk_inst_builder.ZiskInstBuilder)
    (off : Std.I64) (usp : Bool) (h : self.store_ind off usp = ok z) :
    operandFields self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_ind] at h
  rw [Result.ok.injEq] at h
  subst z
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem operandFields_j (self z : zisk_inst_builder.ZiskInstBuilder)
    (j1 j2 : Std.I64) (h : self.j j1 j2 = ok z) : operandFields self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j, bind_ok, Bind.bind] at h
  rw [Result.ok.injEq] at h
  subst z
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem operandFields_build (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : self.build = ok z) : operandFields self z := by
  rw [ZiskFv.Compliance.Extraction.build_eq self z h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem op_zisk_copyb_precompiled (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : self.op_zisk zisk_ops.ZiskOp.CopyB = ok z) : z.i.is_precompiled = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.is_m32,
    zisk_ops.ZiskOp.input_size, core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from, Bind.bind] at h
  simp only [bind_ok, Bind.bind] at h
  rw [Result.ok.injEq] at h
  subst z
  norm_num [memoryLdZeroRow, romMessageOfRaw]

private theorem precompiled_pres_ind_width (self z : zisk_inst_builder.ZiskInstBuilder)
    (w : Std.U64) (h : self.ind_width w = ok z) :
    z.i.is_precompiled = self.i.is_precompiled := by
  simp only [zisk_inst_builder.ZiskInstBuilder.ind_width] at h
  split at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst z; rfl)
    | simp at h

private theorem precompiled_pres_store_ind (self z : zisk_inst_builder.ZiskInstBuilder)
    (off : Std.I64) (usp : Bool) (h : self.store_ind off usp = ok z) :
    z.i.is_precompiled = self.i.is_precompiled := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_ind] at h
  rw [Result.ok.injEq] at h
  subst z
  norm_num [memoryLdNegativeRow, romMessageOfRaw]

private theorem precompiled_pres_j (self z : zisk_inst_builder.ZiskInstBuilder)
    (j1 j2 : Std.I64) (h : self.j j1 j2 = ok z) :
    z.i.is_precompiled = self.i.is_precompiled := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j, Bind.bind] at h
  rw [Result.ok.injEq] at h
  subst z
  rfl

theorem memorySdRow_eq_romMessageOfRaw :
    memorySdRow =
      romMessageOfRaw 0 (ZiskFv.Completeness.Rv64imShapes.rawSType 0 2 1 3) := by
  let raw := ZiskFv.Compliance.Decode.toU32
    (ZiskFv.Completeness.Rv64imShapes.rawSType 0 2 1 3)
  obtain ⟨decoded, hdecoded, hopd, hrs1b, hrs2b⟩ :=
    decode_s_bounds raw aeneas_extract.rv64im_decode.RiscvOpcode.Sd
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := by
    rw [show aeneas_extract.rv64im_decode.decode_32_core raw =
        aeneas_extract.rv64im_decode.decode_s raw
          aeneas_extract.rv64im_decode.RiscvOpcode.Sd by
      simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc,
        Bind.bind, bind_ok, ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.toU32_and7, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawSType_opcode 0 2 1 3,
        ZiskFv.Compliance.Decode.rawSType_funct3 0 2 1 3 (by norm_num)]
      all_goals rfl]
    exact hdecoded
  have hraw : raw = 2142243#u32 := by rfl
  rw [hraw] at hdecoded
  rw [aeneas_extract.rv64im_decode.decode_s] at hdecoded
  simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok, Bind.bind] at hdecoded
  obtain ⟨funct3, hfunct3, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  obtain ⟨imm4, himm4, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  obtain ⟨rs1, hrs1, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  obtain ⟨rs2, hrs2, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  obtain ⟨imm11, himm11, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  obtain ⟨immHigh, himmHigh, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  obtain ⟨imm, himm, hdecoded⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdecoded
  change ok 3#u32 = ok funct3 at hfunct3
  change ok 0#u32 = ok imm4 at himm4
  change ok 1#u32 = ok rs1 at hrs1
  change ok 2#u32 = ok rs2 at hrs2
  change ok 0#u32 = ok imm11 at himm11
  simp only [Result.ok.injEq] at hfunct3 himm4 hrs1 hrs2 himm11
  subst funct3
  subst imm4
  subst rs1
  subst rs2
  subst imm11
  change ok 0#u32 = ok immHigh at himmHigh
  simp only [Result.ok.injEq] at himmHigh
  subst immHigh
  change ok 0#i32 = ok imm at himm
  simp only [Result.ok.injEq] at himm
  subst imm
  rw [Result.ok.injEq] at hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm } with hinput
  obtain ⟨ctx, hctx⟩ :=
    store_op_typed_ok { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB
      8#u64 4#u64 (fun _ => ⟨_, rfl⟩) hrs1b hrs2b
  obtain ⟨zib, hzib, hiw, hb, hstore, hstoreOffset, hj1, hj2, hsetPc, hstorePc,
      hop, hm32, ot, hot, hext⟩ :=
    store_op_typed_full_pins { defCtx with extract_marker := () } input
      zisk_ops.ZiskOp.CopyB 8#u64 4#u64 8#u64 ctx ind_width_set8 hctx
  have hctxFields := hctx
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    Bind.bind, bind_ok] at hctxFields
  obtain ⟨ctxBase, hctxBase, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  rw [Result.ok.injEq] at hctxFields
  subst ctx
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at hctxBase
  obtain ⟨z0, hz0, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxBase
  obtain ⟨z1, hz1, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨off, hoff, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨z2, hz2, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨z3, hz3, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨z4, hz4, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨z5, hz5, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨z6, hz6, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨z7, hz7, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  obtain ⟨ctx', hctxInsert, hctxFields⟩ :=
    ZiskFv.Compliance.Extraction.bind_eq_ok_imp hctxFields
  rw [Result.ok.injEq] at hctxFields
  subst hctxFields
  have hctxExtract : ctx'.extract_inst = some z7 :=
    ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ hctxInsert
  have hopFields : operandFields z2 z3 := operandFields_op_zisk z2 z3 _ hz3
  have hiwFields : operandFields z3 z4 := operandFields_ind_width z3 z4 _ hz4
  have hstoreFields : operandFields z4 z5 := operandFields_store_ind z4 z5 _ _ hz5
  have hjFields : operandFields z5 z6 := operandFields_j z5 z6 _ _ hz6
  have hbuildFields : operandFields z6 z7 := operandFields_build z6 z7 hz7
  have hfinalFields : operandFields z2 z7 :=
    operandFields_trans hopFields
      (operandFields_trans hiwFields
        (operandFields_trans hstoreFields (operandFields_trans hjFields hbuildFields)))
  have hpre3 : z3.i.is_precompiled = false := op_zisk_copyb_precompiled z2 z3 hz3
  have hpre4 : z4.i.is_precompiled = false :=
    (precompiled_pres_ind_width z3 z4 _ hz4).trans hpre3
  have hpre5 := precompiled_pres_store_ind z4 z5 _ _ hz5
  have hpre6 := precompiled_pres_j z5 z6 _ _ hz6
  have hpre7 : z7.i.is_precompiled = false := by
    rw [(ZiskFv.Compliance.Extraction.build_eq z6 z7 hz7)]
    exact hpre6.trans (hpre5.trans hpre4)
  simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new, input, ← hdecoded, Result.ok.injEq] at hz0
  have hz1Saved := hz1
  norm_num [input, ← hdecoded, zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm, zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at hz1
  subst z1
  have hoffSaved := hoff
  simp only [input, ← hdecoded] at hoffSaved
  have hoffCalc : UScalar.cast UScalarTy.U64 2#u32 + 0#u64 = ok 2#u64 := by rfl
  rw [hoffCalc] at hoffSaved
  rw [Result.ok.injEq] at hoffSaved
  subst off
  norm_num [input, ← hdecoded] at hoff
  have hz2Saved := hz2
  norm_num [input, ← hdecoded, zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm, zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at hz2Saved
  subst z2
  norm_num [input, ← hdecoded, zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm, zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at hz2
  have hzibEq : zib = z7 := by
    rw [hctxExtract] at hzib
    exact Option.some.inj hzib.symm
  subst z7
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, haSrc, haUseSp, haOffset, hbSrc, hbUseSp, hbOffset, hrowWidth,
      hrowOp, hrowStore, hrowStoreOffset, hrowJmp1, hrowJmp2, hrowSetPc, hrowStorePc,
      hrowExternal, hrowM32⟩ := from_inst_full_fields zib.i
  have hrowPrecompiled : row.is_precompiled = zib.i.is_precompiled := by
    simp only [aeneas_extract.ZiskInstExtract.from_inst, lift, Bind.bind, bind_ok] at hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  rcases hfinalFields with ⟨haSrcFinal, haUseSpFinal, haOffsetFinal, hbSrcFinal,
    hbUseSpFinal, hbOffsetFinal⟩
  have hopVal : zib.i.op = 1#u8 := by
    change ok 1#u8 = ok zib.i.op at hop
    exact (Result.ok.inj hop).symm
  have hm32Val : zib.i.m32 = false := by
    change ok false = ok zib.i.m32 at hm32
    exact (Result.ok.inj hm32).symm
  have hotVal : ot = zisk_ops.OpType.Internal := by
    change ok zisk_ops.OpType.Internal = ok ot at hot
    exact (Result.ok.inj hot).symm
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Sd false =
        ok { ctx' with extract_marker := () } := by
    rw [show riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
        defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Sd false =
      (do
        let s ← riscv2zisk_context.Riscv2ZiskContext.store_op_typed
          { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB 8#u64 4#u64
        ok { s with extract_marker := () }) by rfl, hctx]
    rfl
  let ext : aeneas_extract.Rv64imTranspileExtract :=
    { accepted := true, decode := dext, row := row }
  have hextRaw : aeneas_extract.extract_transpile_rv64im_raw raw = ok ext := by
    rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd]
    simp only [defCtx] at hlower
    simp only [aeneas_extract.lowering_opcode, riscv2zisk_single_row.Rv64imLoweringInput.new,
      bind_ok, ← hinput, hlower, hctxExtract, core.option.Option.unwrap, Result.ofOption, hrow, ext]
  rw [romMessageOfRaw]
  change memorySdRow =
    match aeneas_extract.extract_transpile_rv64im_raw raw with
    | ok ext => romRowOf 0 ext.row
    | _ => _
  simp only [hextRaw]
  rw [romRowOf_eq_serializeExtract]
  simp only [memorySdRow, serializeExtract, romOpcode, romFlagBitsOfExtract,
    ZiskFv.AirsClean.Main.packFlags, haSrc, haUseSp, haOffset, hbSrc, hbUseSp, hbOffset,
    hrowWidth, hrowOp, hrowStore, hrowStoreOffset, hrowJmp1, hrowJmp2, hrowSetPc,
    hrowStorePc, hrowExternal, hrowM32, hrowPrecompiled, hiw, hstore, hstoreOffset, hj1,
    hj2, hsetPc,
    hstorePc, hopVal, hm32Val, hotVal, hext, input, ← hdecoded, ext,
    hpre7,
    haSrcFinal, haUseSpFinal, haOffsetFinal, hbSrcFinal, hbUseSpFinal, hbOffsetFinal,
    hz1Saved,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.ind_width,
    zisk_inst_builder.ZiskInstBuilder.store_ind,
    zisk_inst_builder.ZiskInstBuilder.j]
  norm_num [input, ← hdecoded, zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm, zisk_registers.REGS_IN_MAIN_FROM,
    zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at hz1Saved ⊢
  norm_num [signedOffset, sourceImmediate, ZiskFv.AirsClean.boolF,
    zisk_inst.SRC_IMM, zisk_inst.SRC_MEM, zisk_inst.SRC_IND, zisk_inst.SRC_REG,
    zisk_inst.STORE_MEM, zisk_inst.STORE_IND, zisk_inst.STORE_REG,
    ZiskFv.Compliance.Extraction.cast_u32_u64_val] at *
  constructor
  · decide
  constructor <;> decide

#print axioms memorySdRow_eq_romMessageOfRaw

theorem memoryLdZeroRow_eq_romMessageOfRaw :
    memoryLdZeroRow =
      romMessageOfRaw 4 (ZiskFv.Completeness.Rv64imShapes.rawIType 0 1 3 3 0x03) := by
  let raw := ZiskFv.Compliance.Decode.toU32
    (ZiskFv.Completeness.Rv64imShapes.rawIType 0 1 3 3 0x03)
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ :=
    decode_i_bounds raw aeneas_extract.rv64im_decode.RiscvOpcode.Ld false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := by
    rw [show aeneas_extract.rv64im_decode.decode_32_core raw =
        aeneas_extract.rv64im_decode.decode_i raw
          aeneas_extract.rv64im_decode.RiscvOpcode.Ld false by
      simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc,
        Bind.bind, bind_ok, ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.toU32_and7, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode 0 1 3 3 0x03 (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 0 1 3 3 0x03 (by norm_num) (by norm_num)
          (by norm_num)]
      all_goals rfl]
    exact hdecoded
  obtain ⟨hrd, hrs1, himm⟩ :=
    decode_i_rawIType_fields 0 1 3 3 0x03 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) _ decoded hdecoded
  have hrs1ne : decoded.rs1.val ≠ 0 := by
    have hv : decoded.rs1.val = 1 := by
      simpa only [UScalar.val, BitVec.toNat_ofNat] using congrArg BitVec.toNat hrs1
    omega
  have hrs1val : decoded.rs1.val = 1 := by
    simpa only [UScalar.val, BitVec.toNat_ofNat] using congrArg BitVec.toNat hrs1
  have hrdne : decoded.rd.val ≠ 0 := by
    have hv : decoded.rd.val = 3 := by
      simpa only [UScalar.val, BitVec.toNat_ofNat] using congrArg BitVec.toNat hrd
    omega
  have hrdval : decoded.rd.val = 3 := by
    simpa only [UScalar.val, BitVec.toNat_ofNat] using congrArg BitVec.toNat hrd
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm } with hinput
  obtain ⟨ctx, hctx⟩ :=
    load_op_typed_ok { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB
      8#u64 4#u64 (fun _ => ⟨_, rfl⟩) (by rw [hinput]; exact hrs1b)
      (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, haSrc, haOff, haSp, hbSrc, hbOff, hstoreOff, hstore,
      hstoreReg, hiw, hj1, hj2, hpre⟩ :=
    ZiskFv.Compliance.RawProgramBinding.ld_op_typed_nonzero_rs1_full_pins
      { defCtx with extract_marker := () } input
      4#u64 8#u64 ctx (by rw [hinput]; exact hrdb) (by rw [hinput]; exact hrs1b)
      (by rw [hinput]; exact hrs1ne) ind_width_set8 hctx
  obtain ⟨zib', hzib', hop, hext, hm32, hsetPc, hstorePc⟩ :=
    load_static_pins_of { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB
      8#u64 4#u64 ctx 1#u8 false false zisk_ops.OpType.Internal rfl rfl rfl rfl hctx
  have hz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  subst zib'
  have haOffEq : zib.i.a_offset_imm0 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    rw [haOff, hinput, hrs1val]
    rfl
  have hstoreOffEq : zib.i.store_offset = 3#i64 := by
    apply IScalar.eq_of_val_eq
    rw [hstoreOff, hinput, hrdval]
    rfl
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrowASrc, hrowASp, hrowAOff, hrowBSrc, hrowBSp, hrowBOff,
      hrowWidth, hrowOp, hrowStore, hrowStoreOff, hrowJ1, hrowJ2, hrowSetPc,
      hrowStorePc, hrowExt, hrowM32⟩ := from_inst_full_fields zib.i
  have hrowPre : row.is_precompiled = zib.i.is_precompiled := by
    simp only [aeneas_extract.ZiskInstExtract.from_inst, lift, Bind.bind, bind_ok] at hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false =
        ok { ctx with extract_marker := () } := by
    rw [show riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
        defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false =
      (do
        let s ← riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB 8#u64 4#u64
        ok { s with extract_marker := () }) by rfl, hctx]
    rfl
  let ext : aeneas_extract.Rv64imTranspileExtract :=
    { accepted := true, decode := dext, row := row }
  have hextRaw : aeneas_extract.extract_transpile_rv64im_raw raw = ok ext := by
    rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd]
    simp only [defCtx] at hlower
    simp only [aeneas_extract.lowering_opcode,
      riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput, hlower, hzib,
      core.option.Option.unwrap, Result.ofOption, hrow, ext]
  rw [romMessageOfRaw]
  change memoryLdZeroRow =
    match aeneas_extract.extract_transpile_rv64im_raw raw with
    | ok ext => romRowOf 4 ext.row
    | _ => _
  simp only [hextRaw, romRowOf_eq_serializeExtract, memoryLdZeroRow, serializeExtract,
    romOpcode, romFlagBitsOfExtract, ZiskFv.AirsClean.Main.packFlags, hrowASrc, hrowASp,
    hrowAOff, hrowBSrc, hrowBSp, hrowBOff, hrowWidth, hrowOp, hrowStore, hrowStoreOff,
    hrowJ1, hrowJ2, hrowSetPc, hrowStorePc, hrowExt, hrowM32, haSrc, haOffEq, haSp,
    hbSrc, hbOff, hstoreOffEq, hstoreReg hrdne, hiw, hj1, hj2, hpre, hrowPre, hop, hext,
    hm32, hsetPc, hstorePc, input, ext]
  norm_num [signedOffset, sourceImmediate, ZiskFv.AirsClean.boolF, zisk_inst.SRC_IMM,
    zisk_inst.SRC_MEM, zisk_inst.SRC_IND, zisk_inst.SRC_REG, zisk_inst.STORE_MEM,
    zisk_inst.STORE_IND, zisk_inst.STORE_REG, hrd, hrs1, himm]
  constructor
  · decide
  constructor <;> decide

theorem memoryLdNegativeRow_eq_romMessageOfRaw :
    memoryLdNegativeRow =
      romMessageOfRaw 8 (ZiskFv.Completeness.Rv64imShapes.rawIType 4088 1 3 4 0x03) := by
  let raw := ZiskFv.Compliance.Decode.toU32
    (ZiskFv.Completeness.Rv64imShapes.rawIType 4088 1 3 4 0x03)
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ :=
    decode_i_bounds raw aeneas_extract.rv64im_decode.RiscvOpcode.Ld false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := by
    rw [show aeneas_extract.rv64im_decode.decode_32_core raw =
        aeneas_extract.rv64im_decode.decode_i raw
          aeneas_extract.rv64im_decode.RiscvOpcode.Ld false by
      simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc,
        Bind.bind, bind_ok, ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.toU32_and7, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode 4088 1 3 4 0x03 (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 4088 1 3 4 0x03 (by norm_num)
          (by norm_num) (by norm_num)]
      all_goals rfl]
    exact hdecoded
  obtain ⟨hrd, hrs1, himm⟩ :=
    decode_i_rawIType_fields 4088 1 3 4 0x03 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) _ decoded hdecoded
  have hrs1val : decoded.rs1.val = 1 := by
    simpa only [UScalar.val, BitVec.toNat_ofNat] using congrArg BitVec.toNat hrs1
  have hrs1ne : decoded.rs1.val ≠ 0 := by omega
  have hrdval : decoded.rd.val = 4 := by
    simpa only [UScalar.val, BitVec.toNat_ofNat] using congrArg BitVec.toNat hrd
  have hrdne : decoded.rd.val ≠ 0 := by omega
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm } with hinput
  obtain ⟨ctx, hctx⟩ :=
    load_op_typed_ok { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB
      8#u64 4#u64 (fun _ => ⟨_, rfl⟩) (by rw [hinput]; exact hrs1b)
      (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, haSrc, haOff, haSp, hbSrc, hbOff, hstoreOff, hstore,
      hstoreReg, hiw, hj1, hj2, hpre⟩ :=
    ZiskFv.Compliance.RawProgramBinding.ld_op_typed_nonzero_rs1_full_pins
      { defCtx with extract_marker := () } input 4#u64 8#u64 ctx
      (by rw [hinput]; exact hrdb) (by rw [hinput]; exact hrs1b)
      (by rw [hinput]; exact hrs1ne) ind_width_set8 hctx
  obtain ⟨zib', hzib', hop, hext, hm32, hsetPc, hstorePc⟩ :=
    load_static_pins_of { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB
      8#u64 4#u64 ctx 1#u8 false false zisk_ops.OpType.Internal rfl rfl rfl rfl hctx
  have hz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  subst zib'
  have haOffEq : zib.i.a_offset_imm0 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    rw [haOff, hinput, hrs1val]
    rfl
  have hstoreOffEq : zib.i.store_offset = 4#i64 := by
    apply IScalar.eq_of_val_eq
    rw [hstoreOff, hinput, hrdval]
    rfl
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrowASrc, hrowASp, hrowAOff, hrowBSrc, hrowBSp, hrowBOff,
      hrowWidth, hrowOp, hrowStore, hrowStoreOff, hrowJ1, hrowJ2, hrowSetPc,
      hrowStorePc, hrowExt, hrowM32⟩ := from_inst_full_fields zib.i
  have hrowPre : row.is_precompiled = zib.i.is_precompiled := by
    simp only [aeneas_extract.ZiskInstExtract.from_inst, lift, Bind.bind, bind_ok] at hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false =
        ok { ctx with extract_marker := () } := by
    rw [show riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
        defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false =
      (do
        let s ← riscv2zisk_context.Riscv2ZiskContext.load_op_typed
          { defCtx with extract_marker := () } input zisk_ops.ZiskOp.CopyB 8#u64 4#u64
        ok { s with extract_marker := () }) by rfl, hctx]
    rfl
  let ext : aeneas_extract.Rv64imTranspileExtract :=
    { accepted := true, decode := dext, row := row }
  have hextRaw : aeneas_extract.extract_transpile_rv64im_raw raw = ok ext := by
    rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd]
    simp only [defCtx] at hlower
    simp only [aeneas_extract.lowering_opcode,
      riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput, hlower, hzib,
      core.option.Option.unwrap, Result.ofOption, hrow, ext]
  rw [romMessageOfRaw]
  change memoryLdNegativeRow =
    match aeneas_extract.extract_transpile_rv64im_raw raw with
    | ok ext => romRowOf 8 ext.row
    | _ => _
  simp only [hextRaw, romRowOf_eq_serializeExtract, memoryLdNegativeRow, serializeExtract,
    romOpcode, romFlagBitsOfExtract, ZiskFv.AirsClean.Main.packFlags, hrowASrc, hrowASp,
    hrowAOff, hrowBSrc, hrowBSp, hrowBOff, hrowWidth, hrowOp, hrowStore, hrowStoreOff,
    hrowJ1, hrowJ2, hrowSetPc, hrowStorePc, hrowExt, hrowM32, haSrc, haOffEq, haSp,
    hbSrc, hbOff, hstoreOffEq, hstoreReg hrdne, hiw, hj1, hj2, hpre, hrowPre, hop, hext,
    hm32, hsetPc, hstorePc, input, ext]
  norm_num [signedOffset, sourceImmediate, ZiskFv.AirsClean.boolF, zisk_inst.SRC_IMM,
    zisk_inst.SRC_MEM, zisk_inst.SRC_IND, zisk_inst.SRC_REG, zisk_inst.STORE_MEM,
    zisk_inst.STORE_IND, zisk_inst.STORE_REG, hrd, hrs1, himm]
  constructor
  · decide
  constructor <;> decide

theorem memoryProgramBinding :
    ProgramBinding memoryAcceptedTrace memoryAddr memoryRawProgram := by
  constructor
  · decide
  · intro k
    fin_cases k
    · simp only [memoryAcceptedTrace, memoryProgram, memoryAddr, memoryRawProgram]
      exact memorySdRow_eq_romMessageOfRaw
    · simp only [memoryAcceptedTrace, memoryProgram, memoryAddr, memoryRawProgram]
      exact memoryLdZeroRow_eq_romMessageOfRaw
    · simp only [memoryAcceptedTrace, memoryProgram, memoryAddr, memoryRawProgram]
      exact memoryLdNegativeRow_eq_romMessageOfRaw

#print axioms memoryProgramBinding

/-- Identity embedding of architectural raw-word indices into physical ROM
    rows: the 3-row memory witness has exactly one physical row per raw word
    (SD and the two LDs are all non-JALR, so no expansion row is ever
    produced). -/
def memoryStart :
    Fin memoryAcceptedTrace.programLength → Fin memoryAcceptedTrace.programLength :=
  id

/-- A committed ROM row known to differ from the all-zero default (via its
    `flags`) must have come from the successful branch of `romMessageOfRaw`,
    exposing the underlying `extract_transpile_rv64im_raw` witness. Avoids
    re-deriving the full decode/lower/serialize chain a second time. -/
private theorem memoryRomMessage_ext_of_ne_default {line : FGL} {raw : BitVec 32}
    {msg : ZiskRomMessage FGL} (heq : msg = romMessageOfRaw line raw)
    (hflags : msg.flags ≠ 0) :
    ∃ ext : aeneas_extract.Rv64imTranspileExtract,
      aeneas_extract.extract_transpile_rv64im_raw
        (ZiskFv.Compliance.Decode.toU32 raw) = ok ext := by
  unfold romMessageOfRaw at heq
  split at heq
  · rename_i ext hext
    exact ⟨ext, hext⟩
  · exact absurd (congrArg ZiskRomMessage.flags heq) (by simpa using hflags)

theorem memoryProgramRowsBinding :
    ProgramRowsBinding memoryAcceptedTrace memoryStart memoryAddr memoryRawProgram := by
  have hnonSd : (ZiskFv.Compliance.Decode.toU32
      (ZiskFv.Completeness.Rv64imShapes.rawSType 0 2 1 3) &&& 127#u32) ≠ 103#u32 := by decide
  have hnonLdZero : (ZiskFv.Compliance.Decode.toU32
      (ZiskFv.Completeness.Rv64imShapes.rawIType 0 1 3 3 0x03) &&& 127#u32) ≠ 103#u32 := by
    decide
  have hnonLdNeg : (ZiskFv.Compliance.Decode.toU32
      (ZiskFv.Completeness.Rv64imShapes.rawIType 4088 1 3 4 0x03) &&& 127#u32) ≠ 103#u32 := by
    decide
  obtain ⟨extSd, hextSd⟩ := memoryRomMessage_ext_of_ne_default
    memorySdRow_eq_romMessageOfRaw (by decide)
  obtain ⟨extLdZero, hextLdZero⟩ := memoryRomMessage_ext_of_ne_default
    memoryLdZeroRow_eq_romMessageOfRaw (by decide)
  obtain ⟨extLdNeg, hextLdNeg⟩ := memoryRomMessage_ext_of_ne_default
    memoryLdNegativeRow_eq_romMessageOfRaw (by decide)
  have hsndSd : (romMessagesOfRaw (0 : FGL)
      (ZiskFv.Completeness.Rv64imShapes.rawSType 0 2 1 3)).2 = none := by
    unfold romMessagesOfRaw
    rw [aeneas_extract.extract_transpile_rv64im_rows_raw, hextSd]
    simp only [lift, Bind.bind, bind_ok, hnonSd]
    rfl
  have hsndLdZero : (romMessagesOfRaw (4 : FGL)
      (ZiskFv.Completeness.Rv64imShapes.rawIType 0 1 3 3 0x03)).2 = none := by
    unfold romMessagesOfRaw
    rw [aeneas_extract.extract_transpile_rv64im_rows_raw, hextLdZero]
    simp only [lift, Bind.bind, bind_ok, hnonLdZero]
    rfl
  have hsndLdNeg : (romMessagesOfRaw (8 : FGL)
      (ZiskFv.Completeness.Rv64imShapes.rawIType 4088 1 3 4 0x03)).2 = none := by
    unfold romMessagesOfRaw
    rw [aeneas_extract.extract_transpile_rv64im_rows_raw, hextLdNeg]
    simp only [lift, Bind.bind, bind_ok, hnonLdNeg]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' h
    fin_cases k <;> fin_cases k' <;> revert h <;> decide
  · intro k
    fin_cases k <;> decide
  · intro k
    fin_cases k <;> decide
  · intro k k' h
    fin_cases k <;> fin_cases k' <;>
      simp only [memoryAddr, memoryRawProgram, hsndSd, hsndLdZero, hsndLdNeg] <;>
      revert h <;> decide
  · intro k
    fin_cases k
    · simp only [memoryStart, id_eq, memoryAddr, memoryRawProgram]
      refine ⟨?_, ?_⟩
      · rw [romMessagesOfRaw_fst_of_non_jalr _ _ extSd hextSd hnonSd]
        exact memorySdRow_eq_romMessageOfRaw
      · rw [hsndSd]
        trivial
    · simp only [memoryStart, id_eq, memoryAddr, memoryRawProgram]
      refine ⟨?_, ?_⟩
      · rw [romMessagesOfRaw_fst_of_non_jalr _ _ extLdZero hextLdZero hnonLdZero]
        exact memoryLdZeroRow_eq_romMessageOfRaw
      · rw [hsndLdZero]
        trivial
    · simp only [memoryStart, id_eq, memoryAddr, memoryRawProgram]
      refine ⟨?_, ?_⟩
      · rw [romMessagesOfRaw_fst_of_non_jalr _ _ extLdNeg hextLdNeg hnonLdNeg]
        exact memoryLdNegativeRow_eq_romMessageOfRaw
      · rw [hsndLdNeg]
        trivial
  · intro j
    fin_cases j
    · exact ⟨⟨0, by decide⟩, Or.inl rfl⟩
    · exact ⟨⟨1, by decide⟩, Or.inl rfl⟩
    · exact ⟨⟨2, by decide⟩, Or.inl rfl⟩

#print axioms memoryProgramRowsBinding

end ZiskFv.Compliance.RawProgramBinding
