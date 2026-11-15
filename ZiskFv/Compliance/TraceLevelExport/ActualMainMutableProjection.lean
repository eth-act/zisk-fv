import ZiskFv.Compliance.TraceLevelExport.AuxiliaryReplayNeutrality

/-!
# Actual Main mutable-memory projection

The projection below uses all six maintained Main requests. Register-pre
requests are excluded by their actual PIL opcode, not removed from RAW balance.
The weak source classification concerns mutable traffic only: it does not
identify A's register index or operand value, and changes no root interface.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Air.Flat Interaction
open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Channels.MemoryBus
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open RawProgramBinding CanonicalExecutionRows
open ZiskFv.Compliance.Extraction
open Spike

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- The complete maintained roster, before any projection simplification. -/
theorem mainMutableReplayRowsAt_eq_six {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) :
    let v := (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    let env := trace.mainTable.environment (trace.mainTable.table.get row)
    let project := fun mult message => mutableReplayRowsOfTyped
      (((MemBusChannel.emitted mult message).toRaw).eval env).mult (eval env message)
    mainMutableReplayRowsAt trace row =
      project v.rom.a_src_reg (aRegPreMessageExpr v) ++
      project (-(v.rom.a_src_mem + v.rom.a_src_reg)) (aMemMessageExpr v) ++
      project v.rom.b_src_reg (bRegPreMessageExpr v) ++
      project (-(v.rom.b_src_mem + v.rom.b_src_ind + v.rom.b_src_reg)) (bMemMessageExpr v) ++
      project v.rom.store_reg (cRegPreMessageExpr v) ++
      project (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg)) (cMemMessageExpr v) := by
  simp only [mainMutableReplayRowsAt, mainTypedMemRoster, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

private theorem projected_register_pre_nil (mult : FGL) (message : MemBusMessage FGL)
    (register : message.mem_op = 3) : mutableReplayRowsOfTyped mult message = [] := by
  apply mutableReplayRowsOfTyped_eq_nil
  · rw [register]; decide
  · rw [register]; decide

/-- Only after proving the three actual register-pre opcodes are 3 can the
six-request expression be reduced to its three current-access projections. -/
theorem mainMutableReplayRowsAt_eq_current {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) :
    let v := (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    let env := trace.mainTable.environment (trace.mainTable.table.get row)
    let project := fun mult message => mutableReplayRowsOfTyped
      (((MemBusChannel.emitted mult message).toRaw).eval env).mult (eval env message)
    mainMutableReplayRowsAt trace row =
      project (-(v.rom.a_src_mem + v.rom.a_src_reg)) (aMemMessageExpr v) ++
      project (-(v.rom.b_src_mem + v.rom.b_src_ind + v.rom.b_src_reg)) (bMemMessageExpr v) ++
      project (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg)) (cMemMessageExpr v) := by
  rw [mainMutableReplayRowsAt_eq_six]
  dsimp only
  rw [projected_register_pre_nil _ _ (by rw [eval_aRegPreMessageExpr]; rfl),
    projected_register_pre_nil _ _ (by rw [eval_bRegPreMessageExpr]; rfl),
    projected_register_pre_nil _ _ (by rw [eval_cRegPreMessageExpr]; rfl)]
  simp only [List.nil_append, List.append_nil]

/-- Source-only mutable-traffic information. No canonical register index, A
value, lane equality, architectural state, or caller promise occurs here. -/
private structure WeakMutableSourceShape (reads writes : Bool) (row : zisk_inst.ZiskInst) : Prop where
  a_not_mem : row.a_src ≠ zisk_inst.SRC_MEM
  b_not_mem : row.b_src ≠ zisk_inst.SRC_MEM
  b_ind : decide (row.b_src = zisk_inst.SRC_IND) = reads
  store_not_mem : row.store ≠ zisk_inst.STORE_MEM
  store_ind : decide (row.store = zisk_inst.STORE_IND) = writes

private theorem weakShape_congr {reads writes : Bool} {a b : zisk_inst.ZiskInst}
    (ha : b.a_src = a.a_src) (hb : b.b_src = a.b_src) (hc : b.store = a.store)
    (shape : WeakMutableSourceShape reads writes a) : WeakMutableSourceShape reads writes b := by
  rcases shape with ⟨am, bm, bi, cm, ci⟩
  exact ⟨ha.symm ▸ am, hb.symm ▸ bm, hb.symm ▸ bi, hc.symm ▸ cm, hc.symm ▸ ci⟩

private theorem weakShape_new (address : Std.U64) (z : zisk_inst_builder.ZiskInstBuilder)
    (source : zisk_inst_builder.ZiskInstBuilder.new address = .ok z) :
    WeakMutableSourceShape false false z.i := by
  simp only [zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default, Bind.bind, bind_ok] at source
  cases Result.ok.inj source
  constructor <;> decide

private theorem weakShape_new_for (input : riscv2zisk_single_row.Rv64imLoweringInput)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (source : zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering input = .ok z) :
    WeakMutableSourceShape false false z.i := by
  simpa only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering] using
    weakShape_new input.rom_address z source

private theorem weakShape_a_imm {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (value : Std.U64)
    (source : self.src_a_imm value = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_imm, lift, Bind.bind, bind_ok] at source
  repeat' obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
  cases Result.ok.inj source
  exact ⟨by decide, shape.b_not_mem, shape.b_ind, shape.store_not_mem, shape.store_ind⟩

private theorem weakShape_a_reg {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (bound : reg.val < 32) (source : self.src_a_reg reg false = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  have cast1 := cast_one_u64
  have cast31 := cast_31_u64
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    lift, Bind.bind, bind_ok, Bool.false_eq_true, if_false] at source
  split_ifs at source <;>
    first
    | (repeat' obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
       cases Result.ok.inj source
       exact ⟨by decide, shape.b_not_mem, shape.b_ind, shape.store_not_mem, shape.store_ind⟩)
    | (exfalso; scalar_tac)

private theorem weakShape_b_imm {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (value : Std.U64)
    (source : self.src_b_imm value = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape false writes z.i := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm, lift, Bind.bind, bind_ok] at source
  repeat' obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
  cases Result.ok.inj source
  exact ⟨shape.a_not_mem, by decide, by decide, shape.store_not_mem, shape.store_ind⟩

private theorem weakShape_b_reg {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (reg : Std.U64)
    (bound : reg.val < 32) (source : self.src_b_reg reg false = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape false writes z.i := by
  have cast1 := cast_one_u64
  have cast31 := cast_31_u64
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    lift, Bind.bind, bind_ok, Bool.false_eq_true, if_false] at source
  split_ifs at source <;>
    first
    | (repeat' obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
       cases Result.ok.inj source
       exact ⟨shape.a_not_mem, by decide, by decide, shape.store_not_mem, shape.store_ind⟩)
    | (exfalso; scalar_tac)

private theorem weakShape_b_lastc {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder)
    (source : self.src_b_lastc = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape false writes z.i := by
  cases Result.ok.inj source
  exact ⟨shape.a_not_mem, by decide, by decide, shape.store_not_mem, shape.store_ind⟩

private theorem weakShape_b_ind {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (offset : Std.U64)
    (source : self.src_b_ind offset false = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape true writes z.i := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_ind, lift, Bind.bind, bind_ok,
    Bool.false_eq_true, if_false] at source
  split_ifs at source <;>
    (cases Result.ok.inj source
     exact ⟨shape.a_not_mem, by decide, by decide, shape.store_not_mem, shape.store_ind⟩)

private theorem weakShape_ind_width {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (width : Std.U64)
    (source : self.ind_width width = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  unfold zisk_inst_builder.ZiskInstBuilder.ind_width at source
  split at source <;> first
  | (cases Result.ok.inj source; exact shape)
  | simp at source

private theorem weakShape_op {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (op : zisk_ops.ZiskOp)
    (source : self.op_zisk op = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  obtain ⟨a, _, b, _⟩ := op_zisk_src_pres self z op source
  exact weakShape_congr a b (op_zisk_pres_store self z op source).2 shape

private theorem weakShape_store_reg {reads : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (offset : Std.I64) (storePc : Bool)
    (lower : 0 ≤ offset.val) (upper : offset.val < 32)
    (source : self.store_reg offset false storePc = .ok z)
    (shape : WeakMutableSourceShape reads false self.i) :
    WeakMutableSourceShape reads false z.i := by
  have cast1 := cast_one_i64
  have cast31 := cast_31_i64
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    lift, Bind.bind, bind_ok] at source
  split_ifs at source <;>
    first
    | (cases Result.ok.inj source; exact shape)
    | (cases Result.ok.inj source
       exact ⟨shape.a_not_mem, shape.b_not_mem, shape.b_ind, by decide, by decide⟩)
    | (exfalso; scalar_tac)

private theorem weakShape_store_ind {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (offset : Std.I64)
    (source : self.store_ind offset false = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads true z.i := by
  cases Result.ok.inj source
  exact ⟨shape.a_not_mem, shape.b_not_mem, shape.b_ind, by decide, by decide⟩

private theorem weakShape_j {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (j1 j2 : Std.I64)
    (source : self.j j1 j2 = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  obtain ⟨a, _, b, _⟩ := j_src_pres self j1 j2 z source
  exact weakShape_congr a b (j_pres_store self z j1 j2 source).2 shape

private theorem weakShape_build {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (source : self.build = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  rw [build_eq self z source]
  exact shape

private theorem weakShape_set_pc {reads writes : Bool}
    (self z : zisk_inst_builder.ZiskInstBuilder) (source : self.set_pc = .ok z)
    (shape : WeakMutableSourceShape reads writes self.i) :
    WeakMutableSourceShape reads writes z.i := by
  cases Result.ok.inj source
  exact shape

private theorem i64_add_zero_eq (x y : Std.I64) (source : x + 0#i64 = .ok y) : y = x := by
  obtain ⟨z, hz, value⟩ := iscalar_add_zero_ok x
  have same := Result.ok.inj (source.symm.trans hz)
  subst z
  exact IScalar.eq_of_val_eq value

private theorem u64_add_zero_eq (x y : Std.U64) (source : x + 0#u64 = .ok y) : y = x := by
  obtain ⟨z, hz, value⟩ := uscalar_add_zero_ok x
  have same := Result.ok.inj (source.symm.trans hz)
  subst z
  exact UScalar.eq_of_val_eq value

/-- Only the production opcode's mutable traffic class is observed. -/
private def sourceReads : riscv2zisk_single_row.Rv64imSingleRowOpcode → Bool
  | .Lb | .Lbu | .Lh | .Lhu | .Lw | .Lwu | .Ld => true
  | _ => false

private def sourceWrites : riscv2zisk_single_row.Rv64imSingleRowOpcode → Bool
  | .Sb | .Sh | .Sw | .Sd => true
  | _ => false

private theorem weakShape_insert {reads writes : Bool}
    (self result : riscv2zisk_context.Riscv2ZiskContext) (address : Std.U64)
    (z : zisk_inst_builder.ZiskInstBuilder)
    (source : self.insert_inst address z = .ok result)
    (shape : WeakMutableSourceShape reads writes z.i) :
    ∃ actual, result.extract_inst = some actual ∧
      WeakMutableSourceShape reads writes actual.i :=
  ⟨z, insert_inst_extract self address z result source, shape⟩

-- Backward rules follow successful primitive calls. Scalar discharge uses
-- only the actual source decoder's register bounds and zero-offset results.
local macro "prove_source_shape" : tactic => `(tactic|
  aesop (config := { terminal := true, maxRuleApplications := 10000 })
    (add safe forward [i64_add_zero_eq, u64_add_zero_eq])
    (add unsafe 90% apply [weakShape_insert, weakShape_new_for, weakShape_new,
      weakShape_a_imm, weakShape_a_reg, weakShape_b_imm, weakShape_b_reg,
      weakShape_b_lastc, weakShape_b_ind, weakShape_ind_width, weakShape_op,
      weakShape_store_reg, weakShape_store_ind, weakShape_j, weakShape_build,
      weakShape_set_pc])
    (add safe (by
      solve | (simp only [cast_u32_u64_val, hcast_u32_i64_val] at *; scalar_tac))))

private def sourceRegisterBounds (opcode : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (input : riscv2zisk_single_row.Rv64imLoweringInput) : Prop :=
  match opcode with
  | .Fence => True
  | .Lui | .Auipc | .Jal => input.rd.val < 32
  | .Jalr | .Addi | .Slli | .Slti | .Sltiu | .Xori | .Srli | .Srai | .Ori | .Andi
  | .Addiw | .Slliw | .Srliw | .Sraiw
  | .Lb | .Lbu | .Lh | .Lhu | .Lw | .Lwu | .Ld =>
      input.rd.val < 32 ∧ input.rs1.val < 32
  | .Beq | .Bne | .Blt | .Bge | .Bltu | .Bgeu | .Sb | .Sh | .Sw | .Sd =>
      input.rs1.val < 32 ∧ input.rs2.val < 32
  | _ => input.rd.val < 32 ∧ input.rs1.val < 32 ∧ input.rs2.val < 32

/-- All 63 source opcodes, including Add/Or/ADDI pseudo-op paths and both JALR
arms. The source context is exactly the existing extractor's defCtx, so its ADD
precompile path is not silently assumed absent in an arbitrary context. -/
private theorem lower_source_weak_mutable_shape
    (input : riscv2zisk_single_row.Rv64imLoweringInput)
    (opcode : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (bounds : sourceRegisterBounds opcode input)
    (source : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
      defCtx input opcode false = .ok ctx) :
    ∃ z, ctx.extract_inst = some z ∧
      WeakMutableSourceShape (sourceReads opcode) (sourceWrites opcode) z.i := by
  cases opcode <;> simp only [sourceRegisterBounds] at bounds
  all_goals first
  | obtain ⟨rd, rs1, rs2⟩ := bounds
  | obtain ⟨firstBound, secondBound⟩ := bounds
  | skip
  all_goals
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      sourceReads, sourceWrites, defCtx,
      riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
      riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed,
      riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed,
      riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
      riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
      riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
      riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
      riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
      riscv2zisk_context.Riscv2ZiskContext.lui,
      riscv2zisk_context.Riscv2ZiskContext.auipc,
      riscv2zisk_context.Riscv2ZiskContext.jal,
      riscv2zisk_context.Riscv2ZiskContext.jalr,
      riscv2zisk_context.Riscv2ZiskContext.copyb,
      riscv2zisk_context.Riscv2ZiskContext.nop,
      riscv2zisk_context.Riscv2ZiskContext.hint,
      zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
      lift, Bind.bind, bind_ok, bind_assoc, Bool.false_eq_true, if_false,
      riscv2zisk_single_row.CSR_DMA_MEMCPY_ADDR,
      riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR] at source
  all_goals
    repeat' first
    | (obtain ⟨_, _, source⟩ := bind_eq_ok_imp source)
    | (progress split_ifs at source)
    cases Result.ok.inj source
    prove_source_shape

end ZiskFv.Compliance.SerializedExecutionRows

namespace ZiskFv.Compliance.SerializedExecutionRows

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction
open RawProgramBinding CanonicalExecutionRows
open Air.Flat Interaction
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.Channels.MemoryBus
open Spike

private theorem fence_lowering_opcode
    (raw : Std.U32) (decoded : aeneas_extract.rv64im_decode.DecodedRv64im)
    (opcode : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (core : aeneas_extract.rv64im_decode.decode_fence raw = .ok decoded)
    (lower : aeneas_extract.lowering_opcode decoded.opcode = .ok (some opcode)) :
    opcode = .Fence := by
  unfold aeneas_extract.rv64im_decode.decode_fence at core
  simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new,
    lift, Bind.bind, bind_ok] at core
  repeat' first
  | (obtain ⟨_, _, core⟩ := bind_eq_ok_imp core)
  | (split at core)
  all_goals
    cases Result.ok.inj core
    simpa [aeneas_extract.lowering_opcode,
      aeneas_extract.rv64im_decode.DecodedRv64im.reserved,
      aeneas_extract.rv64im_decode.DecodedRv64im.unsupported,
      aeneas_extract.rv64im_decode.DecodedRv64im.new] using lower.symm

private theorem core_r_facts
    {raw : Std.U32} {op : aeneas_extract.rv64im_decode.RiscvOpcode}
    {decoded : aeneas_extract.rv64im_decode.DecodedRv64im}
    (source : aeneas_extract.rv64im_decode.decode_r raw op = .ok decoded) :
    decoded.opcode = op ∧ decoded.rd.val < 32 ∧ decoded.rs1.val < 32 ∧ decoded.rs2.val < 32 := by
  obtain ⟨actual, success, opcode, rd, rs1, rs2⟩ := decode_r_bounds raw op
  have same := Result.ok.inj (success.symm.trans source)
  subst decoded
  exact ⟨opcode, rd, rs1, rs2⟩

private theorem core_i_facts
    {raw : Std.U32} {op : aeneas_extract.rv64im_decode.RiscvOpcode} {shift : Bool}
    {decoded : aeneas_extract.rv64im_decode.DecodedRv64im}
    (source : aeneas_extract.rv64im_decode.decode_i raw op shift = .ok decoded) :
    decoded.opcode = op ∧ decoded.rd.val < 32 ∧ decoded.rs1.val < 32 := by
  obtain ⟨actual, success, opcode, rd, rs1, _⟩ := decode_i_bounds raw op shift
  have same := Result.ok.inj (success.symm.trans source)
  subst decoded
  exact ⟨opcode, rd, rs1⟩

private theorem core_s_facts
    {raw : Std.U32} {op : aeneas_extract.rv64im_decode.RiscvOpcode}
    {decoded : aeneas_extract.rv64im_decode.DecodedRv64im}
    (source : aeneas_extract.rv64im_decode.decode_s raw op = .ok decoded) :
    decoded.opcode = op ∧ decoded.rs1.val < 32 ∧ decoded.rs2.val < 32 := by
  obtain ⟨actual, success, opcode, rs1, rs2⟩ := decode_s_bounds raw op
  have same := Result.ok.inj (success.symm.trans source)
  subst decoded
  exact ⟨opcode, rs1, rs2⟩

private theorem core_b_facts
    {raw : Std.U32} {op : aeneas_extract.rv64im_decode.RiscvOpcode}
    {decoded : aeneas_extract.rv64im_decode.DecodedRv64im}
    (source : aeneas_extract.rv64im_decode.decode_b raw op = .ok decoded) :
    decoded.opcode = op ∧ decoded.rs1.val < 32 ∧ decoded.rs2.val < 32 := by
  obtain ⟨actual, success, opcode, rs1, rs2⟩ := decode_b_bounds raw op
  have same := Result.ok.inj (success.symm.trans source)
  subst decoded
  exact ⟨opcode, rs1, rs2⟩

private theorem core_u_facts
    {raw : Std.U32} {op : aeneas_extract.rv64im_decode.RiscvOpcode}
    {decoded : aeneas_extract.rv64im_decode.DecodedRv64im}
    (source : aeneas_extract.rv64im_decode.decode_u raw op = .ok decoded) :
    decoded.opcode = op ∧ decoded.rd.val < 32 := by
  obtain ⟨actual, success, opcode, rd, _⟩ := decode_u_bounds raw op
  have same := Result.ok.inj (success.symm.trans source)
  subst decoded
  exact ⟨opcode, rd⟩

private theorem core_j_facts
    {raw : Std.U32} {op : aeneas_extract.rv64im_decode.RiscvOpcode}
    {decoded : aeneas_extract.rv64im_decode.DecodedRv64im}
    (source : aeneas_extract.rv64im_decode.decode_j raw op = .ok decoded) :
    decoded.opcode = op ∧ decoded.rd.val < 32 := by
  obtain ⟨actual, success, opcode, rd, _⟩ := decode_j_bounds raw op
  have same := Result.ok.inj (success.symm.trans source)
  subst decoded
  exact ⟨opcode, rd⟩

-- Each terminal decoder arm uses its existing successful format decoder.
local macro "finish_source_core" : tactic => `(tactic|
  aesop (config := { terminal := true })
    (add safe forward [core_r_facts, core_i_facts, core_s_facts, core_b_facts,
      core_u_facts, core_j_facts, fence_lowering_opcode])
    (add norm simp [sourceRegisterBounds, sourceReads, sourceWrites,
      aeneas_extract.lowering_opcode,
      aeneas_extract.rv64im_decode.DecodedRv64im.reserved,
      aeneas_extract.rv64im_decode.DecodedRv64im.unsupported,
      aeneas_extract.rv64im_decode.DecodedRv64im.new]))

private theorem source_core_controls
    (raw : Std.U32) (decoded : aeneas_extract.rv64im_decode.DecodedRv64im)
    (opcode : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (core : aeneas_extract.rv64im_decode.decode_32_core raw = .ok decoded)
    (lower : aeneas_extract.lowering_opcode decoded.opcode = .ok (some opcode)) :
    sourceRegisterBounds opcode
        { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
          rs2 := decoded.rs2, imm := decoded.imm } ∧
      sourceReads opcode = decide ((raw &&& 127#u32) = 3#u32) ∧
      sourceWrites opcode = decide ((raw &&& 127#u32) = 35#u32) := by
  unfold aeneas_extract.rv64im_decode.decode_32_core at core
  simp only [lift, Bind.bind, bind_ok] at core
  repeat' first
  | (solve | finish_source_core)
  | (obtain ⟨_, _, core⟩ := bind_eq_ok_imp core)
  | (split at core)

/-- Weak all63 classification of the actual successful terminal production
row. In particular, every load (including rs1=x0) has no A mutable request.
Only mutable selector absence is exported; no A/r1 canonical bridge is added. -/
theorem successful_terminal_mutable_source_selectors {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) :
    lowering.rows.last_row.a_src ≠ zisk_inst.SRC_MEM ∧
      lowering.rows.last_row.b_src ≠ zisk_inst.SRC_MEM ∧
      decide (lowering.rows.last_row.b_src = zisk_inst.SRC_IND) =
        decide ((Decode.toU32 raw &&& 127#u32) = 3#u32) ∧
      lowering.rows.last_row.store ≠ zisk_inst.STORE_MEM ∧
      decide (lowering.rows.last_row.store = zisk_inst.STORE_IND) =
        decide ((Decode.toU32 raw &&& 127#u32) = 35#u32) := by
  obtain ⟨terminal, source, accepted, _, last, _⟩ := lowering.source_cases
  unfold aeneas_extract.extract_transpile_rv64im_raw at source
  obtain ⟨decoded, core, source⟩ := bind_eq_ok_imp source
  obtain ⟨extracted, _, source⟩ := bind_eq_ok_imp source
  obtain ⟨opcode, lower, source⟩ := bind_eq_ok_imp source
  cases opcode with
  | none =>
      obtain ⟨zero, _, source⟩ := bind_eq_ok_imp source
      cases Result.ok.inj source
      contradiction
  | some opcode =>
      obtain ⟨bounds, reads, writes⟩ := source_core_controls
        (Decode.toU32 raw) decoded opcode core lower
      obtain ⟨input, inputSource, source⟩ := bind_eq_ok_imp source
      have inputEq : input =
          ({ rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
             rs2 := decoded.rs2, imm := decoded.imm } :
            riscv2zisk_single_row.Rv64imLoweringInput) :=
        (Result.ok.inj inputSource).symm
      subst input
      obtain ⟨ctx, contextSource, source⟩ := bind_eq_ok_imp source
      obtain ⟨actual, actualSource, shape⟩ :=
        lower_source_weak_mutable_shape _ opcode ctx bounds contextSource
      obtain ⟨z, zSource, source⟩ := bind_eq_ok_imp source
      rw [actualSource] at zSource
      have same : actual = z := Result.ok.inj zSource
      subst z
      obtain ⟨row, rowSource, source⟩ := bind_eq_ok_imp source
      obtain ⟨copied, copySource, a, _, _, b, _, _, _, _, store, _⟩ :=
        from_inst_full_fields actual.i
      have copiedEq : copied = row := Result.ok.inj (copySource.symm.trans rowSource)
      subst copied
      have terminalEq := Result.ok.inj source
      have terminalRow := congrArg aeneas_extract.Rv64imTranspileExtract.row terminalEq
      rw [last, ← terminalRow]
      exact ⟨a.symm ▸ shape.a_not_mem, b.symm ▸ shape.b_not_mem,
        by rw [b, shape.b_ind, reads], store.symm ▸ shape.store_not_mem,
        by rw [store, shape.store_ind, writes]⟩

end ZiskFv.Compliance.SerializedExecutionRows

namespace ZiskFv.Compliance.SerializedExecutionRows

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction
open RawProgramBinding CanonicalExecutionRows
open Air.Flat Interaction
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.Channels.MemoryBus
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open Spike

private theorem boolean_column (x : FGL) (boolean : x * (1 - x) = 0) :
    ∃ b : Bool, x = ZiskFv.AirsClean.boolF b := by
  rcases mul_eq_zero.mp boolean with zero | one
  · exact ⟨false, by simpa [ZiskFv.AirsClean.boolF] using zero⟩
  · exact ⟨true, by
      simp only [ZiskFv.AirsClean.boolF_true]
      exact (sub_eq_zero.mp one).symm⟩

private theorem main_a_mem_source_column {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) (bits : RomFlagBits)
    (flags : romFlags (mainRowWithRomAt trace row) = packFlags bits) :
    (mainRowWithRomAt trace row).rom.a_src_mem =
      ZiskFv.AirsClean.boolF bits.a_src_mem := by
  let r := mainRowWithRomAt trace row
  obtain ⟨_, _, _, _, _, amBoolean, preBoolean, _⟩ :=
    RomDecodeBinding.mainRow_flags_boolean trace row
  obtain ⟨am, amEq⟩ := boolean_column _ amBoolean
  obtain ⟨pre, preEq⟩ := boolean_column _ preBoolean
  obtain ⟨ieo, m32, setpc, storepc⟩ :=
    RomDecodeBinding.romFlagColumns_of_romFlags_eq_packFlags r bits
      (RomDecodeBinding.mainRow_flags_boolean trace row) flags
  obtain ⟨ar, ai, br, bi⟩ :=
    RomDecodeBinding.romAllSourceSelectorColumns_of_romFlags_eq_packFlags r bits
      (RomDecodeBinding.mainRow_flags_boolean trace row) flags
  obtain ⟨bm, sm, si, bind, _, sr⟩ :=
    RomDecodeBinding.romMemorySelectorColumns_of_romFlags_eq_packFlags r bits
      (RomDecodeBinding.mainRow_flags_boolean trace row) flags
  have packed : romFlags r =
      packFlags { bits with a_src_mem := am, is_precompiled := pre } := by
    simp only [romFlags, packFlags, ieo, m32, setpc, storepc,
      ar, ai, br, bi, bm, sm, si, bind, sr, amEq, preEq]
  have same := RomDecodeBinding.packFlags_inj (packed.symm.trans flags)
  exact amEq.trans (congrArg ZiskFv.AirsClean.boolF
    (congrArg RomFlagBits.a_src_mem same))

private theorem current_mult_a (env : Environment FGL) (v : Var MainRowWithRom FGL) :
    (((MemBusChannel.emitted (-(v.rom.a_src_mem + v.rom.a_src_reg))
      (aMemMessageExpr v)).toRaw).eval env).mult =
      -((eval env v).rom.a_src_mem + (eval env v).rom.a_src_reg) := by
  change Expression.eval env (-(v.rom.a_src_mem + v.rom.a_src_reg)) = _
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  ring

private theorem current_mult_b (env : Environment FGL) (v : Var MainRowWithRom FGL) :
    (((MemBusChannel.emitted (-(v.rom.b_src_mem + v.rom.b_src_ind + v.rom.b_src_reg))
      (bMemMessageExpr v)).toRaw).eval env).mult =
      -((eval env v).rom.b_src_mem + (eval env v).rom.b_src_ind +
        (eval env v).rom.b_src_reg) := by
  change Expression.eval env (-(v.rom.b_src_mem + v.rom.b_src_ind + v.rom.b_src_reg)) = _
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  ring

private theorem current_mult_c (env : Environment FGL) (v : Var MainRowWithRom FGL) :
    (((MemBusChannel.emitted (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg))
      (cMemMessageExpr v)).toRaw).eval env).mult =
      -((eval env v).rom.store_mem + (eval env v).rom.store_ind +
        (eval env v).rom.store_reg) := by
  change Expression.eval env (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg)) = _
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  ring

/-- Evaluation of the six actual requests. The positive legacy write tag
comes from mem_op=2 below; all three actual current-request signs stay negative. -/
theorem mainMutableReplayRowsAt_eq_current_values {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) :
    let r := mainRowWithRomAt trace row
    mainMutableReplayRowsAt trace row =
      mutableReplayRowsOfTyped (-(r.rom.a_src_mem + r.rom.a_src_reg)) (aMemMessage r) ++
      mutableReplayRowsOfTyped (-(r.rom.b_src_mem + r.rom.b_src_ind + r.rom.b_src_reg))
        (bMemMessage r) ++
      mutableReplayRowsOfTyped (-(r.rom.store_mem + r.rom.store_ind + r.rom.store_reg))
        (cMemMessage r) := by
  rw [mainMutableReplayRowsAt_eq_current]
  dsimp only
  rw [current_mult_a, current_mult_b, current_mult_c,
    eval_aMemMessageExpr, eval_bMemMessageExpr, eval_cMemMessageExpr,
    ← ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
      trace.program trace.mainTable row]
  rfl

/-- Exact mutable replay at an actual source terminal, before associating its
raw word with an architectural constructor. This includes EVERY source opcode,
not just loads/stores, and requires no new selector or compatibility promise. -/
theorem main_mutable_projection_of_successful_terminal {n : Nat}
    (trace : AcceptedZiskTrace n) (row : Fin trace.mainTable.table.length)
    {raw : BitVec 32} (lowering : SuccessfulRowLowering raw) (line : FGL)
    (agreement : romMessage (mainRowWithRomAt trace row) =
      romRowOf line lowering.rows.last_row) :
    mainMutableReplayRowsAt trace row =
      (if (Decode.toU32 raw &&& 127#u32) = 3#u32 then
        [(bMemMessage (mainRowWithRomAt trace row)).toEntry (-1) 2] else []) ++
      (if (Decode.toU32 raw &&& 127#u32) = 35#u32 then
        [(cMemMessage (mainRowWithRomAt trace row)).toEntry 1 2] else []) := by
  obtain ⟨sourceA, sourceB, sourceRead, sourceC, sourceWrite⟩ :=
    successful_terminal_mutable_source_selectors lowering
  have flags : romFlags (mainRowWithRomAt trace row) =
      packFlags (romFlagBitsOfExtract lowering.rows.last_row) :=
    congrArg ZiskRomMessage.flags agreement
  have aMem := main_a_mem_source_column trace row _ flags
  obtain ⟨aReg, _, bReg, _⟩ :=
    RomDecodeBinding.romAllSourceSelectorColumns_of_romFlags_eq_packFlags
      (mainRowWithRomAt trace row) _ (RomDecodeBinding.mainRow_flags_boolean trace row) flags
  obtain ⟨bMem, cMem, cInd, bInd, _, cReg⟩ :=
    RomDecodeBinding.romMemorySelectorColumns_of_romFlags_eq_packFlags
      (mainRowWithRomAt trace row) _ (RomDecodeBinding.mainRow_flags_boolean trace row) flags
  have aZero : (mainRowWithRomAt trace row).rom.a_src_mem = 0 := by
    simpa [romFlagBitsOfExtract, sourceA] using aMem
  have bZero : (mainRowWithRomAt trace row).rom.b_src_mem = 0 := by
    simpa [romFlagBitsOfExtract, sourceB] using bMem
  have cZero : (mainRowWithRomAt trace row).rom.store_mem = 0 := by
    simpa [romFlagBitsOfExtract, sourceC] using cMem
  change (mainRowWithRomAt trace row).rom.b_src_ind =
    ZiskFv.AirsClean.boolF (decide (lowering.rows.last_row.b_src = zisk_inst.SRC_IND)) at bInd
  change (mainRowWithRomAt trace row).rom.store_ind =
    ZiskFv.AirsClean.boolF (decide (lowering.rows.last_row.store = zisk_inst.STORE_IND)) at cInd
  rw [sourceRead] at bInd
  rw [sourceWrite] at cInd
  rw [mainMutableReplayRowsAt_eq_current_values]
  dsimp only
  by_cases read : (Decode.toU32 raw &&& 127#u32) = 3#u32 <;>
    by_cases write : (Decode.toU32 raw &&& 127#u32) = 35#u32
  · have impossible : (3#u32 : Std.U32) = 35#u32 := read.symm.trans write
    exact False.elim ((by decide : (3#u32 : Std.U32) ≠ 35#u32) impossible)
  · have sourceInd : lowering.rows.last_row.b_src = zisk_inst.SRC_IND := by
      simpa only [read, decide_true, decide_eq_true_eq] using sourceRead
    have bRegZero : (mainRowWithRomAt trace row).rom.b_src_reg = 0 := by
      simpa [romFlagBitsOfExtract, sourceInd, zisk_inst.SRC_IND, zisk_inst.SRC_REG] using bReg
    by_cases ar : lowering.rows.last_row.a_src = zisk_inst.SRC_REG <;>
      by_cases cr : lowering.rows.last_row.store = zisk_inst.STORE_REG <;>
      simp [romFlagBitsOfExtract, ar, cr] at aReg cReg <;>
      simp [mutableReplayRowsOfTyped, aMemMessage, bMemMessage, cMemMessage,
        aZero, bZero, cZero, aReg, bRegZero, cReg, bInd, cInd, read, write]
  · have sourceInd : lowering.rows.last_row.store = zisk_inst.STORE_IND := by
      simpa only [write, decide_true, decide_eq_true_eq] using sourceWrite
    have cRegZero : (mainRowWithRomAt trace row).rom.store_reg = 0 := by
      simpa [romFlagBitsOfExtract, sourceInd, zisk_inst.STORE_IND, zisk_inst.STORE_REG] using cReg
    by_cases ar : lowering.rows.last_row.a_src = zisk_inst.SRC_REG <;>
      by_cases br : lowering.rows.last_row.b_src = zisk_inst.SRC_REG <;>
      simp [romFlagBitsOfExtract, ar, br] at aReg bReg <;>
      simp [mutableReplayRowsOfTyped, aMemMessage, bMemMessage, cMemMessage,
        aZero, bZero, cZero, aReg, bReg, cRegZero, bInd, cInd, read, write]
  · by_cases ar : lowering.rows.last_row.a_src = zisk_inst.SRC_REG <;>
      by_cases br : lowering.rows.last_row.b_src = zisk_inst.SRC_REG <;>
      by_cases cr : lowering.rows.last_row.store = zisk_inst.STORE_REG <;>
      simp [romFlagBitsOfExtract, ar, br, cr] at aReg bReg cReg <;>
      simp [mutableReplayRowsOfTyped, aMemMessage, bMemMessage, cMemMessage,
        aZero, bZero, cZero, aReg, bReg, cReg, bInd, cInd, read, write]

private def stepReads {n : Nat} {trace : AcceptedZiskTrace n} {i : Fin trace.numInstructions} :
    ZiskStep trace i → Bool
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ => true
  | _ => false

private def stepWrites {n : Nat} {trace : AcceptedZiskTrace n} {i : Fin trace.numInstructions} :
    ZiskStep trace i → Bool
  | .sb _ | .sh _ | .sw _ | .sd _ => true
  | _ => false

private theorem raw_decode_mutable_tags {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i step start addr rawProgram)
    (k : Fin rawLength)
    (atPc : (mainOfTable trace.program trace.mainTable).pc i.val = addr k) :
    decide ((Decode.toU32 (rawProgram k) &&& 127#u32) = 3#u32) = stepReads step ∧
      decide ((Decode.toU32 (rawProgram k) &&& 127#u32) = 35#u32) = stepWrites step := by
  obtain ⟨j, atLine, _⟩ := RomDecodeBinding.mainDecodeColumns_at_eq_program trace
    ⟨i.val, trace.mainTable_index i⟩
  have selected (other : Fin rawLength) (address : addr other = (trace.program j).line) :
      other = k :=
    source_address_injective trace start addr rawProgram binding
      (address.trans (atLine.trans atPc))
  cases step
  case jalr c =>
      cases rawDecode.down.down with
      | aligned evidence =>
          obtain ⟨other, _, address, word⟩ := evidence.hLine j atLine
          have same := selected other address
          subst other
          rw [word, evidence.h_raw]
          simp [stepReads, stepWrites, Decode.toU32_and127, Decode.rawIType_opcode]
      | unaligned evidence =>
          obtain ⟨other, _, address, word⟩ := evidence.hLineAdd j atLine
          have same := selected other address
          subst other
          rw [word, evidence.h_raw]
          simp [stepReads, stepWrites, Decode.toU32_and127, Decode.rawIType_opcode]
  all_goals
    first
    | (obtain ⟨other, address, word⟩ := rawDecode.down.down.hLine j atLine
       have addressTyped : addr other = (trace.program j).line := address)
    | obtain ⟨other, _, address, word⟩ := rawDecode.down.down.hLine j atLine
    have same := selected other address
    subst other
    rw [word]
    simp [stepReads, stepWrites, Decode.toU32_and127,
      Decode.rawRType_opcode, Decode.rawIType_opcode, Decode.rawSType_opcode,
      Decode.rawBType_opcode, Decode.rawUType_opcode, Decode.rawJType_opcode,
      Decode.rawSupportedFence_opcode]

/-- A real source terminal is a finite physical row, computed from the same
width prefix as physicalStart. No old starts=i convention is used. -/
def physicalTerminal {m : Nat} {words : Fin m → BitVec 32}
    (L : ∀ i, SuccessfulRowLowering (words i)) (i : Fin m) : Fin (sourceEnd L) :=
  ⟨sourceStart L i + (L i).width - 1, by
    have room := prefix_mono (sourceWidth L) (Nat.succ_le_of_lt i.isLt)
    have positive := (L i).width_pos
    rw [prefix_succ] at room
    change sourceStart L i + (L i).width ≤ sourceEnd L at room
    omega⟩

@[simp] theorem physicalTerminal_val {m : Nat} {words : Fin m → BitVec 32}
    (L : ∀ i, SuccessfulRowLowering (words i)) (i : Fin m) :
    (physicalTerminal L i).val = sourceStart L i + (L i).width - 1 := rfl

/-- The source-selected producer is DERIVED from existing raw decode for ALL63
constructors, rather than supplied as a terminal selector oracle. -/
theorem physicalTerminal_eq_actual_producer
    {m rawLength : Nat} (rawProgram : Fin rawLength → BitVec 32)
    (selected : Fin m → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (steps : ∀ i, ZiskStep trace (physicalStart L i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
      start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i)) (i : Fin m) :
    (physicalTerminal L i).val = stepProducerRow (physicalStart L i) (steps i)
      (rowDecode_of_programDecode trace (physicalStart L i)
        (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
          start addr rawProgram binding (rawDecodes i))) := by
  have producer := mapped_producer_successor_eq_source_stop rawProgram selected L trace
    start addr binding steps rawDecodes atPc i
  change sourceStart L i + (L i).width - 1 = _
  simp only [physicalStart_val] at producer
  omega

private theorem terminal_rom
    {m rawLength : Nat} (rawProgram : Fin rawLength → BitVec 32)
    (selected : Fin m → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i)) (i : Fin m) :
    romMessage (mainRowWithRomAt trace
      ⟨(physicalTerminal L i).val, trace.mainTable_index (physicalTerminal L i)⟩) =
      romRowOf (addr (selected i) + (((L i).width - 1 : Nat) : FGL))
        (L i).rows.last_row := by
  let lastOffset : Fin (L i).width := ⟨(L i).width - 1, by
    have positive := (L i).width_pos
    omega⟩
  have span := main_full_serialized_span trace start addr rawProgram binding
    (selected i) (L i)
    ⟨(physicalStart L i).val, trace.mainTable_index (physicalStart L i)⟩
    (canonical_span_room rawProgram selected L trace i) (atPc i) lastOffset
  have indexEq : sourceStart L i + ((L i).width - 1) =
      (physicalTerminal L i).val := by
    have positive := (L i).width_pos
    simp only [physicalTerminal_val]
    omega
  change ZiskFv.AirsClean.Main.romMessage
    (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      trace.program trace.mainTable (physicalTerminal L i).val) = _
  rw [← indexEq]
  by_cases widthOne : (L i).width = 1
  · simpa only [lastOffset, widthOne, Nat.sub_self, Nat.add_zero,
      if_pos rfl, (L i).first_eq_last_of_width_one widthOne, physicalStart_val] using span
  · have positive := (L i).width_pos
    have nonzero : (L i).width - 1 ≠ 0 := by omega
    simpa only [lastOffset, physicalStart_val, if_neg nonzero] using span

/-- Actual terminal Main projection equals the real architectural step's
structural memory rows. The source A/B/C classification and all three
register-pre exclusions are proved above, not added as premises here. -/
theorem actual_main_terminal_mutable_projection
    {m rawLength : Nat} (rawProgram : Fin rawLength → BitVec 32)
    (selected : Fin m → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (steps : ∀ i, ZiskStep trace (physicalStart L i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
      start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i)) (i : Fin m) :
    mainMutableReplayRowsAt trace
        ⟨(physicalTerminal L i).val, trace.mainTable_index (physicalTerminal L i)⟩ =
      memoryRowsOfStep trace (physicalStart L i) (steps i) := by
  have projection := main_mutable_projection_of_successful_terminal trace
    ⟨(physicalTerminal L i).val, trace.mainTable_index (physicalTerminal L i)⟩
    (L i) _ (terminal_rom rawProgram selected L trace start addr binding atPc i)
  obtain ⟨reads, writes⟩ := raw_decode_mutable_tags trace (physicalStart L i) (steps i)
    start addr rawProgram binding (rawDecodes i) (selected i) (atPc i)
  have producer := physicalTerminal_eq_actual_producer rawProgram selected L trace
    start addr binding steps rawDecodes atPc i
  cases stepEq : steps i <;> simp only [stepEq, stepReads, stepWrites] at reads writes
  all_goals
    first
    | (have read : (Decode.toU32 (rawProgram (selected i)) &&& 127#u32) = 3#u32 := by
        simpa only [decide_eq_true_eq] using reads
       have notWrite : (Decode.toU32 (rawProgram (selected i)) &&& 127#u32) ≠ 35#u32 := by
        simpa only [decide_eq_false_iff_not] using writes
       have terminalStart : (physicalTerminal L i).val = (physicalStart L i).val := by
        simpa [stepEq, stepProducerRow] using producer
       simpa [stepEq, read, notWrite, memoryRowsOfStep, busLd,
        mainRowWithRomLd, mainRowWithRomAt, terminalStart,
        ← ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
          trace.program trace.mainTable] using projection)
    | (have notRead : (Decode.toU32 (rawProgram (selected i)) &&& 127#u32) ≠ 3#u32 := by
        simpa only [decide_eq_false_iff_not] using reads
       have write : (Decode.toU32 (rawProgram (selected i)) &&& 127#u32) = 35#u32 := by
        simpa only [decide_eq_true_eq] using writes
       have terminalStart : (physicalTerminal L i).val = (physicalStart L i).val := by
        simpa [stepEq, stepProducerRow] using producer
       simpa [stepEq, notRead, write, memoryRowsOfStep, busSt, eRdSt,
        mainRowWithRomSt, mainRowWithRomAt, terminalStart,
        ← ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
          trace.program trace.mainTable] using projection)
    | (have notRead : (Decode.toU32 (rawProgram (selected i)) &&& 127#u32) ≠ 3#u32 := by
        simpa only [decide_eq_false_iff_not] using reads
       have notWrite : (Decode.toU32 (rawProgram (selected i)) &&& 127#u32) ≠ 35#u32 := by
        simpa only [decide_eq_false_iff_not] using writes
       simpa [stepEq, notRead, notWrite, memoryRowsOfStep] using projection)

end ZiskFv.Compliance.SerializedExecutionRows

namespace ZiskFv.Compliance.SerializedExecutionRows

open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding CanonicalExecutionRows
open Air.Flat Interaction
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open Spike

/-- Inclusion of a finite execution-prefix row into the actual Main table.
There is no out-of-range default and no RAW interaction is erased. -/
noncomputable def physicalMainMutableReplayRowsAt {n : Nat}
    (trace : AcceptedZiskTrace n) (row : Fin n) : List (MemoryBusEntry FGL) :=
  mainMutableReplayRowsAt trace ⟨row.val, trace.mainTable_index row⟩

/-- One actual Main mutable-projection slot for every finite physical row. -/
noncomputable def actualMainMutablePhysicalSlots {n : Nat}
    (trace : AcceptedZiskTrace n) : List (List (MemoryBusEntry FGL)) :=
  (List.finRange n).map (physicalMainMutableReplayRowsAt trace)

section PhysicalProjection

variable {m rawLength : Nat}
variable (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
variable (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
variable (trace : AcceptedZiskTrace (sourceEnd L))
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (steps : ∀ i, ZiskStep trace (physicalStart L i))
variable (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
  start addr rawProgram)
variable (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
  (physicalStart L i).val = addr (selected i))

include binding atPc

/-- Every interior physical source slot is a genuine auxiliary with empty
mutable projection, by exclusion of all SIX actual source messages. -/
theorem actual_main_interior_mutable_projection
    (i : Fin m) (row : Fin (sourceEnd L))
    (inside : sourceStart L i ≤ row.val ∧
      row.val + 1 < sourceStart L i + (L i).width) :
    physicalMainMutableReplayRowsAt trace row = [] := by
  have count := (L i).count
  have widthTwo : (L i).width = 2 := by
    change (L i).width = 1 ∨ (L i).width = 2 at count
    omega
  have rowEq : row = physicalStart L i := by
    apply Fin.ext
    change row.val = sourceStart L i
    omega
  subst row
  exact expanded_main_first_mutable_replay_rows_nil trace start addr rawProgram binding
    (selected i) (L i) widthTwo
    ⟨(physicalStart L i).val, trace.mainTable_index (physicalStart L i)⟩ (atPc i)

include rawDecodes

private theorem actual_main_span_slots (i : Fin m) :
    ((List.finRange (sourceEnd L)).take (sourceStart L i + (L i).width)).map
        (physicalMainMutableReplayRowsAt trace) =
      ((List.finRange (sourceEnd L)).take (sourceStart L i)).map
          (physicalMainMutableReplayRowsAt trace) ++
        sourceSpanSlots L
          (fun k => memoryRowsOfStep trace (physicalStart L k) (steps k)) i := by
  have terminal := actual_main_terminal_mutable_projection rawProgram selected L trace
    start addr binding steps rawDecodes atPc i
  change physicalMainMutableReplayRowsAt trace (physicalTerminal L i) = _ at terminal
  have firstNext := finitePrefix_succ (physicalStart L i)
  have lastNext := finitePrefix_succ (physicalTerminal L i)
  rcases (L i).count with widthOne | widthTwo
  · change (L i).width = 1 at widthOne
    have same : physicalTerminal L i = physicalStart L i := by
      apply Fin.ext
      simp only [physicalTerminal_val, physicalStart_val, widthOne]
      omega
    rw [same] at terminal
    simpa only [physicalStart_val, List.map_append, List.map_singleton,
      widthOne, sourceSpanSlots, Nat.sub_self, List.replicate_zero,
      List.nil_append, terminal] using
      congrArg (List.map (physicalMainMutableReplayRowsAt trace)) firstNext
  · change (L i).width = 2 at widthTwo
    have lastVal : (physicalTerminal L i).val = sourceStart L i + 1 := by
      simp only [physicalTerminal_val, widthTwo]
      omega
    have firstEmpty : physicalMainMutableReplayRowsAt trace (physicalStart L i) = [] := by
      apply actual_main_interior_mutable_projection rawProgram selected L trace
        start addr binding atPc i (physicalStart L i)
      simp only [physicalStart_val, widthTwo]
      omega
    rw [lastVal] at lastNext
    rw [show sourceStart L i + 1 + 1 = sourceStart L i + (L i).width by omega] at lastNext
    rw [lastNext, firstNext]
    simp only [List.map_append, List.map_singleton, terminal, firstEmpty,
      sourceSpanSlots, widthTwo, List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append, List.append_assoc]

/-- Exact ORDERED physical Main prefix at each architectural source cut.
Duplicates and empty auxiliary slots are retained, including count zero. -/
theorem actual_main_mutable_prefix_eq_sourcePhysicalPrefix
    (j : Nat) (bound : j ≤ m) :
    ((List.finRange (sourceEnd L)).take (rowPrefix (sourceWidth L) j)).map
        (physicalMainMutableReplayRowsAt trace) =
      sourcePhysicalPrefix L
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) j bound := by
  induction j with
  | zero => simp
  | succ j previous =>
      have before : j < m := by omega
      let i : Fin m := ⟨j, before⟩
      have next := sourcePhysicalPrefix_succ L
        (fun k => memoryRowsOfStep trace (physicalStart L k) (steps k)) i
      have span := actual_main_span_slots rawProgram selected L trace start addr binding
        steps rawDecodes atPc i
      have cut := prefix_succ (sourceWidth L) i
      change rowPrefix (sourceWidth L) (j + 1) =
        sourceStart L i + (L i).width at cut
      rw [cut, span, previous (by omega)]
      exact next.symm

/-- The WHOLE actual physical slot list is the source spine of the real
architectural memoryRowsOfStep lists. No supplied projection equality is used. -/
theorem actual_main_mutable_slots_eq_sourcePhysicalSlots :
    actualMainMutablePhysicalSlots trace =
      sourcePhysicalSlots L
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
  have wholePrefix := actual_main_mutable_prefix_eq_sourcePhysicalPrefix rawProgram selected L trace
    start addr binding steps rawDecodes atPc m (Nat.le_refl m)
  change ((List.finRange (sourceEnd L)).take (sourceEnd L)).map
    (physicalMainMutableReplayRowsAt trace) = _ at wholePrefix
  simpa only [List.length_finRange, List.take_length, sourcePhysicalPrefix_end,
    actualMainMutablePhysicalSlots] using wholePrefix

/-- Exact ordered physical prefix equality in the full-slot vocabulary. -/
theorem actual_main_mutable_slots_take_cut
    (j : Nat) (bound : j ≤ m) :
    (actualMainMutablePhysicalSlots trace).take (rowPrefix (sourceWidth L) j) =
      sourcePhysicalPrefix L
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) j bound := by
  rw [actual_main_mutable_slots_eq_sourcePhysicalSlots rawProgram selected L trace
    start addr binding steps rawDecodes atPc, sourcePhysicalSlots_take_cut]

/-- Flattening every actual physical Main slot gives exactly the architectural
memory rows, in execution order rather than merely up to permutation. -/
theorem actual_main_mutable_flatten :
    (actualMainMutablePhysicalSlots trace).flatten =
      (List.finRange m).flatMap
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
  rw [actual_main_mutable_slots_eq_sourcePhysicalSlots rawProgram selected L trace
    start addr binding steps rawDecodes atPc, sourcePhysicalSlots_flatten]

/-- The same exact ordered flattening at EVERY bounded source cut. -/
theorem actual_main_mutable_prefix_flatten
    (j : Nat) (bound : j ≤ m) :
    ((actualMainMutablePhysicalSlots trace).take (rowPrefix (sourceWidth L) j)).flatten =
      ((List.finRange m).take j).flatMap
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
  rw [actual_main_mutable_slots_take_cut rawProgram selected L trace start addr binding
    steps rawDecodes atPc j bound, sourcePhysicalPrefix_flatten]

end PhysicalProjection

/-- Genuine source regression: the existing successful two-row JALR is NONFINAL
and its existing successful ADDI successor owns row2. This is source production,
not the unrelated accepted-root JALR fixture. -/
theorem nonfinal_jalr_source_mutable_slots {α : Type}
    (rows : Fin 2 → List α) :
    sourcePhysicalSlots nonfinalJalrLowering rows = [[], rows 0, rows 1] := by
  have width0 : (nonfinalJalrLowering (0 : Fin 2)).width = 2 := sourceJalrTwo_width
  have width1 : (nonfinalJalrLowering (1 : Fin 2)).width = 1 := sourceAddiOne_width
  change
    (List.replicate ((nonfinalJalrLowering (0 : Fin 2)).width - 1) [] ++ [rows 0]) ++
      (List.replicate ((nonfinalJalrLowering (1 : Fin 2)).width - 1) [] ++ [rows 1]) = _
  rw [width0, width1]
  rfl

/-- The genuine source2/1 example also composes with ACTUAL Main rows and actual
existing raw-decode-selected steps. No accepted trace or root witness is
fabricated: the statement is the projection theorem specialized to those
ordinary existing source/binding/raw-decode facts. -/
theorem actual_nonfinal_jalr_successor_mutable_projection
    (trace : AcceptedZiskTrace (sourceEnd nonfinalJalrLowering))
    (start : Fin 2 → Fin trace.programLength) (addr : Fin 2 → FGL)
    (binding : ProgramRowsBinding trace start addr nonfinalJalrWords)
    (steps : ∀ i, ZiskStep trace (physicalStart nonfinalJalrLowering i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart nonfinalJalrLowering i)
      (steps i) start addr nonfinalJalrWords)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart nonfinalJalrLowering i).val = addr i) :
    actualMainMutablePhysicalSlots trace =
      [[], memoryRowsOfStep trace (physicalStart nonfinalJalrLowering 0) (steps 0),
        memoryRowsOfStep trace (physicalStart nonfinalJalrLowering 1) (steps 1)] ∧
      sourceStart nonfinalJalrLowering (0 : Fin 2) = 0 ∧
      sourceStart nonfinalJalrLowering (1 : Fin 2) = 2 ∧
      sourceEnd nonfinalJalrLowering = 3 := by
  obtain ⟨first, second, endpoint, _⟩ := nonfinal_jalr_source_layout
  refine ⟨?_, first, second, endpoint⟩
  rw [actual_main_mutable_slots_eq_sourcePhysicalSlots nonfinalJalrWords id
    nonfinalJalrLowering trace start addr binding steps rawDecodes atPc,
    nonfinal_jalr_source_mutable_slots]

end ZiskFv.Compliance.SerializedExecutionRows
