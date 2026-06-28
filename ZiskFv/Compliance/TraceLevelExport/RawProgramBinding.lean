import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Dispatch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.DynamicFields
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves

/-!
# Raw-program binding for the ADD pilot (issue #159, BLOCK 3)

This module makes the committed ROM message's ADD decode fields **derived** from
the raw RISC-V instruction word, via the REAL Aeneas transpile pipeline
(`extract_transpile_rv64im_raw`, `trust/aeneas/ProductionM2.lean`).

Block 1 (`RomDecodeBinding.Decode_add_of_program`) tied the witness row's decode
columns to the committed program `trace.program`.  This block ties the committed
program entry to its raw instruction word: the op-agnostic `ProgramBinding`
certificate states the committed ROM holds exactly the serialized lowering of the
raw program.  For the ADD case the chain closes — `Decode_add_from_rawProgram`
rebuilds `Decode_add` from `rawProgram` + `ProgramBinding` + the ADD-branch of the
(eventual exhaustive) per-entry raw-word split.

Op-AGNOSTIC: `serializeExtract` / `romMessageOfRaw` / `ProgramBinding` run ONE
pipeline for every word; ADD-ness enters only via the `rawRType … 0x33` raw-word
hypothesis (the ADD case of an exhaustive split), never as a trust premise.

Sound: NO native_decide / bv_decide / new axiom / sorry; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).  The lowering totality is proven
with the kernel-sound `System.Platform.numBits` casing (the same register-bound
lemmas as `…/Extraction/Helpers.lean`), NOT `native_decide` (the production
RV-completeness harness uses `native_decide`; this in-build pilot does not).
-/

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)

set_option maxHeartbeats 8000000

/-! ## Op-agnostic serialization of the lowered row into the committed ROM message. -/

/-- Op-agnostic flag-bit extraction from a lowered ZiskInstExtract: the five
    decode-relevant flags are faithful direct copies of the lowered booleans; the
    operand-source / store selector bits are the op-agnostic selector decode
    (operand-side, out of decode scope — not consumed by per-op decode). -/
def romFlagBitsOfExtract (e : zisk_core.aeneas_extract.ZiskInstExtract) : RomFlagBits where
  a_src_imm := decide (e.a_src = zisk_core.zisk_inst.SRC_IMM)
  a_src_mem := decide (e.a_src = zisk_core.zisk_inst.SRC_MEM)
  is_precompiled := e.is_precompiled
  b_src_imm := decide (e.b_src = zisk_core.zisk_inst.SRC_IMM)
  b_src_mem := decide (e.b_src = zisk_core.zisk_inst.SRC_MEM)
  is_external_op := e.is_external_op
  store_pc := e.store_pc
  store_mem := decide (e.store = zisk_core.zisk_inst.STORE_MEM)
  store_ind := decide (e.store = zisk_core.zisk_inst.STORE_IND)
  set_pc := e.set_pc
  m32 := e.m32
  b_src_ind := decide (e.b_src = (3#u64 : Std.U64))
  a_src_reg := decide (e.a_src = zisk_core.zisk_inst.SRC_REG)
  b_src_reg := decide (e.b_src = zisk_core.zisk_inst.SRC_REG)
  store_reg := decide (e.store = zisk_core.zisk_inst.STORE_REG)

/-- Op-agnostic serialization of a lowered row into the committed FGL ROM message.
    The `line` (pc) is threaded separately (it is the program-counter, supplied by
    the caller). Every other field is the uniform `.val`→FGL coercion of the
    extracted ZiskInst field; `flags` is the standard 15-bit packing. -/
def serializeExtract (line : FGL) (e : zisk_core.aeneas_extract.ZiskInstExtract) :
    ZiskRomMessage FGL where
  line := line
  a_offset_imm0 := (e.a_offset_imm0.val : FGL)
  a_imm1 := (e.a_use_sp_imm1.val : FGL)
  b_offset_imm0 := (e.b_offset_imm0.val : FGL)
  b_imm1 := (e.b_use_sp_imm1.val : FGL)
  ind_width := (e.ind_width.val : FGL)
  op := (e.op.val : FGL)
  store_offset := (e.store_offset.val : FGL)
  jmp_offset1 := (e.jmp_offset1.val : FGL)
  jmp_offset2 := (e.jmp_offset2.val : FGL)
  flags := packFlags (romFlagBitsOfExtract e)

/-- The committed ROM message a raw RISC-V word must serialize to: run the REAL
    Aeneas transpile pipeline on the word and FGL-serialize its lowered row. A
    raw word the pipeline rejects maps to the all-zero message (never matched by a
    supported decode). Op-AGNOSTIC: one pipeline for every word. -/
noncomputable def romMessageOfRaw (line : FGL) (raw : BitVec 32) : ZiskRomMessage FGL :=
  match zisk_core.aeneas_extract.extract_transpile_rv64im_raw (ZiskFv.Compliance.Decode.toU32 raw) with
  | .ok ext => serializeExtract line ext.row
  | _ => { line := line, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0,
           b_imm1 := 0, ind_width := 0, op := 0, store_offset := 0,
           jmp_offset1 := 0, jmp_offset2 := 0, flags := 0 }

/-- Op-agnostic ROM-image binding (a verifier-attached certificate, NOT an axiom):
    the committed ROM holds exactly the serialized lowering of the raw program. -/
def ProgramBinding {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (rawProgram : Fin n → BitVec 32) : Prop :=
  ∀ k : Fin n, trace.program k = romMessageOfRaw (trace.program k).line (rawProgram k)

/-! ## Kernel-sound lowering-totality scalar lemmas.

The register-source / store builders branch on `Std.Usize`-valued register
bounds (`REGS_IN_MAIN_FROM = 1`, `REGS_IN_MAIN_TO = 31`), whose width is the
opaque `System.Platform.numBits`.  These pin the relevant `.val`s under the
two-case `numBits` split (the kernel-sound technique of `Extraction/Helpers.lean`,
NOT `native_decide`).  The two `toU32_and*` lemmas reduce the two R-type field
masks (`rs2`, `funct7`) the `decode_32_core` masks in `Decode/Leaves.lean` don't
already carry. -/

private theorem regs_from_u64_val_eq :
    ((BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64).val) = 1 := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
private theorem regs_to_u64_val_eq :
    ((BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64).val) = 31 := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
private theorem regs_from_i64_val_eq :
    ((BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64).val) = 1 := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
private theorem regs_to_i64_val_eq :
    ((BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64).val) = 31 := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

private theorem toU32_and32505856 (X : BitVec 32) :
    toU32 X &&& 32505856#u32 = toU32 (X &&& 32505856#32) := rfl
private theorem toU32_and4261412864 (X : BitVec 32) :
    toU32 X &&& 4261412864#u32 = toU32 (X &&& 4261412864#32) := rfl

/-! ## ADD pilot raw word `add x1, x2, x3` (funct7=0, rs2=3, rs1=2, funct3=0, rd=1, 0x33). -/

/-- The full Aeneas transpile pipeline on the concrete ADD raw word `add x1, x2, x3`
    succeeds and lowers to a row whose ADD decode fields are pinned.  All eight
    facts come from REDUCING the real `extract_transpile_rv64im_raw` (decode →
    lower → `from_inst`); the lowering register-bound branches are discharged by
    the kernel-sound `numBits` casing.  Concrete registers keep the decode masks
    `decide`-able; generalizing rd/rs1/rs2 is mechanical sweep work. -/
theorem transpile_add :
    ∃ ext, zisk_core.aeneas_extract.extract_transpile_rv64im_raw
        (ZiskFv.Compliance.Decode.toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33))
          = .ok ext
      ∧ ext.row.op = 10#u8
      ∧ ext.row.is_external_op = true
      ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false
      ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  -- `decode_32_core` on the ADD word routes to `decode_r … .Add` (the masks of
  -- `Decode/Leaves.lean`); the final `rfl` reduces the (now-classified) match.
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33))
      = aeneas_extract.rv64im_decode.decode_r
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33))
        aeneas_extract.rv64im_decode.RiscvOpcode.Add := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr25,
      ZiskFv.Compliance.Decode.rawRType_opcode 0 3 2 0 1 0x33 (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct3 0 3 2 0 1 0x33 (by norm_num) (by norm_num) (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct7 0 3 2 0 1 0x33 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    rfl
  -- Reduce the whole pipeline once, packaging the seven row pins into a closed
  -- boolean so `bind_eq_ok_imp` can recover the materialized `ext` plus the pins.
  have hcheck : (do
      let ext ← aeneas_extract.extract_transpile_rv64im_raw
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33))
      (ok (decide (ext.row.op = 10#u8) && decide (ext.row.is_external_op = true)
        && decide (ext.row.m32 = false) && decide (ext.row.set_pc = false)
        && decide (ext.row.store_pc = false)
        && decide (ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
        && decide (ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)) : Result Bool)) = ok true := by
    simp (config := { decide := true }) [aeneas_extract.extract_transpile_rv64im_raw, hdec,
      aeneas_extract.rv64im_decode.decode_r, aeneas_extract.rv64im_decode.DecodedRv64im.new,
      aeneas_extract.decode_extract_from_decoded,
      aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im,
      aeneas_extract.opcode_id, aeneas_extract.format_id, aeneas_extract.lowering_opcode,
      riscv2zisk_single_row.Rv64imLoweringInput.new,
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR, riscv2zisk_single_row.CSR_DMA_MEMCPY_ADDR,
      riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
      zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering, zisk_inst_builder.ZiskInstBuilder.new,
      zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
      zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
      zisk_inst_builder.ZiskInstBuilder.src_a_reg, zisk_inst_builder.ZiskInstBuilder.src_b_reg,
      zisk_inst_builder.ZiskInstBuilder.op_zisk,
      zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
      zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
      zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
      zisk_inst_builder.ZiskInstBuilder.store_reg, zisk_inst_builder.ZiskInstBuilder.j,
      zisk_inst_builder.ZiskInstBuilder.build, riscv2zisk_context.Riscv2ZiskContext.insert_inst,
      zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO, zisk_registers.REG_FIRST,
      mem.SYS_ADDR, mem.RAM_ADDR, UScalar.cast, UScalar.hcast, IScalar.hcast, lift,
      core.option.Option.unwrap, Result.ofOption, aeneas_extract.ZiskInstExtract.from_inst,
      toU32_and32505856, toU32_and4261412864,
      regs_from_u64_val_eq, regs_to_u64_val_eq, regs_from_i64_val_eq, regs_to_i64_val_eq]
  obtain ⟨ext, hext, hb⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hcheck
  rw [Result.ok.injEq] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hb
  exact ⟨ext, hext, h1, h2, h3, h4, h5, h6, h7⟩

/-- The materialized lowered ADD row, named for reuse in the field bridge and the
    block-1 integration.  Choice-backed (kernel-sound: `Classical.choice` is in
    the allowed closure). -/
noncomputable def addExt : zisk_core.aeneas_extract.Rv64imTranspileExtract := transpile_add.choose

/-- `transpile_add`'s payload about the named `addExt`. -/
theorem addExt_spec :
    zisk_core.aeneas_extract.extract_transpile_rv64im_raw
        (ZiskFv.Compliance.Decode.toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33))
          = .ok addExt
      ∧ addExt.row.op = 10#u8
      ∧ addExt.row.is_external_op = true
      ∧ addExt.row.m32 = false
      ∧ addExt.row.set_pc = false
      ∧ addExt.row.store_pc = false
      ∧ addExt.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ addExt.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 :=
  transpile_add.choose_spec

/-- **The op-agnostic field bridge (crux deliverable).**  The committed message's
    ADD decode fields, derived from its raw word plus the binding equation for that
    entry.  No per-op decode premise: the only hypothesis is `hbind`, the
    op-agnostic `romMessageOfRaw` equation specialized to the ADD raw word.  The
    flag conjuncts expose exactly the `RomFlagBits` that `Decode_add_of_program`
    consumes, so they line up with the integration below. -/
theorem add_decode_fields_of_binding (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33)) :
    msg.op = ZiskFv.Trusted.OP_ADD
  ∧ msg.jmp_offset1 = 4
  ∧ msg.jmp_offset2 = 4
  ∧ msg.flags = packFlags (romFlagBitsOfExtract addExt.row)
  ∧ (romFlagBitsOfExtract addExt.row).is_external_op = true
  ∧ (romFlagBitsOfExtract addExt.row).m32 = false
  ∧ (romFlagBitsOfExtract addExt.row).set_pc = false
  ∧ (romFlagBitsOfExtract addExt.row).store_pc = false := by
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := addExt_spec
  have hmsg : msg = serializeExtract line addExt.row := by
    rw [hbind, romMessageOfRaw, hok]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- op = OP_ADD
    rw [hmsg]; show (addExt.row.op.val : FGL) = ZiskFv.Trusted.OP_ADD
    rw [hop]; simp [ZiskFv.Trusted.OP_ADD]
  · -- jmp_offset1 = 4
    rw [hmsg]; show (addExt.row.jmp_offset1.val : FGL) = 4
    rw [hj1]; norm_num [show (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) from by decide]
  · -- jmp_offset2 = 4
    rw [hmsg]; show (addExt.row.jmp_offset2.val : FGL) = 4
    rw [hj2]; norm_num [show (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) from by decide]
  · -- flags = packFlags …  (definitional: serializeExtract.flags)
    rw [hmsg]; rfl
  · exact hieo
  · exact hm32
  · exact hsetpc
  · exact hstorepc

/-- **Block-1 integration.**  Produce `Decode_add` with NO per-op decode premise:
    only `rawProgram`, the op-agnostic `ProgramBinding`, the ADD-branch of the
    (eventual exhaustive) per-entry raw-word split, and the structural next-row
    bound.  The ADD decode columns are derived through `Decode_add_of_program`
    (the in-circuit ROM lookup) fed by `add_decode_fields_of_binding` (the raw-word
    serialization). -/
def Decode_add_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_add trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hAddLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33) :
    ZiskFv.Compliance.Decode_add trace i c := by
  obtain ⟨_, _, hieo, hm32, hsetpc, hstorepc, _, _⟩ := addExt_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_add_of_program trace i c h_idx
    (romFlagBitsOfExtract addExt.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (ZiskFv.Completeness.Rv64imShapes.rawRType 0 3 2 0 1 0x33) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hAddLine j hline))
  obtain ⟨ho, hjo1, hjo2, hf, _, _, _, _⟩ :=
    add_decode_fields_of_binding (trace.program j).line (trace.program j) hbk
  exact ⟨ho, hjo1, hjo2, hf⟩

section AxiomAudit
-- Kernel-only closure audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms transpile_add
#print axioms add_decode_fields_of_binding
#print axioms Decode_add_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
