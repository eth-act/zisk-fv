import ZiskFv.Compliance.TraceLevelExport.CanonicalJalrExecution
import ZiskFv.Compliance.JalrSpinWitness

/-!
# Actual physical provider world for two source JALRs

The source word is JALR x1,x2,1. The literal ROM below is tied to the actual
9ca88b5 production extractor, not the older ADDI/JALR witness's placeholder
ROM. In particular the source ADD has jmp1=jmp2=1 and both rows retain the
source default ind_width=0 (ProductionM2.lean:2134-2161,2362-2453).

The Main table has FIVE actual rows: ADD/AND/ADD/AND/ADD. The accepted
consumed prefix is four rows; the final real ADD successor still contributes
its x2 read to the full provider/register/end-boundary balances. This is not
physical completion, a final-I/O witness, or a total family of auxiliary RV
instructions. Every register predecessor and all31 end/reload rows come
from the actual constructed access history.
-/

open Goldilocks Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.SingleAddWitness

namespace ZiskFv.Compliance.CanonicalJalrWorld

open RawProgramBinding CanonicalSourceParser

/-- Reuse only the generic selector pattern, never the old program or world. -/
def worldAddBits : RomFlagBits := JalrSpinWitness.jalrAddBits

def worldAndBits : RomFlagBits := JalrSpinWitness.jalrAndBits

def worldAddProgramRow : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 2, b_imm1 := 0,
    ind_width := 0, op := ZiskFv.Trusted.OP_ADD, store_offset := 0,
    jmp_offset1 := 1, jmp_offset2 := 1, flags := packFlags worldAddBits }

def worldAndProgramRow : ZiskRomMessage FGL :=
  { line := 1, a_offset_imm0 := 4294967294, a_imm1 := 4294967295,
    b_offset_imm0 := 0, b_imm1 := 0, ind_width := 0, op := ZiskFv.Trusted.OP_AND,
    store_offset := 1, jmp_offset1 := 0, jmp_offset2 := 3,
    flags := packFlags worldAndBits }

def worldProgram : Program 2
  | ⟨0, _⟩ => worldAddProgramRow
  | ⟨1, _⟩ => worldAndProgramRow

section SourceSerialization

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction

private theorem sourceExtract_precompiled
    (zi : zisk_inst.ZiskInst) (row : aeneas_extract.ZiskInstExtract)
    (extracted : aeneas_extract.ZiskInstExtract.from_inst zi = ok row) :
    row.is_precompiled = zi.is_precompiled := by
  unfold aeneas_extract.ZiskInstExtract.from_inst at extracted
  obtain ⟨_, _, extracted⟩ := bind_eq_ok_imp extracted
  rw [Result.ok.injEq] at extracted
  subst row
  rfl

/-- Defaults and mask lanes omitted by the generic decode-facing JALR pins.
Only actual successful source execution and its two recorded rows are used. -/
private theorem sourceJalr_remaining_fields
    (input : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (first : aeneas_extract.ZiskInstExtract) (last : zisk_inst_builder.ZiskInstBuilder)
    (rd : input.rd = 1#u32) (rs1 : input.rs1 = 2#u32) (imm : input.imm = 1#i32)
    (rom : input.rom_address = 0#u64)
    (source : riscv2zisk_context.Riscv2ZiskContext.jalr
      { defCtx with extract_marker := () } input 4#u64 = ok ctx)
    (firstRecorded : ctx.extract_first_inst = some first)
    (lastRecorded : ctx.extract_inst = some last) :
    first.ind_width = 0#u64 ∧ first.store_offset = 0#i64 ∧ first.is_precompiled = false ∧
      last.i.a_src = zisk_inst.SRC_IMM ∧
      last.i.a_use_sp_imm1 = 4294967295#u64 ∧
      last.i.a_offset_imm0 = 4294967294#u64 ∧
      last.i.ind_width = 0#u64 ∧ last.i.is_precompiled = false := by
  have fromU : UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_FROM = 1#u64 := by
    apply UScalar.eq_of_val_eq
    simp [zisk_registers.REGS_IN_MAIN_FROM, UScalar.cast, UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have toU : UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_TO = 31#u64 := by
    apply UScalar.eq_of_val_eq
    simp [zisk_registers.REGS_IN_MAIN_TO, UScalar.cast, UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have fromI : UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_FROM = 1#i64 := by
    apply IScalar.eq_of_val_eq
    simp [zisk_registers.REGS_IN_MAIN_FROM, UScalar.hcast, UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have toI : UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_TO = 31#i64 := by
    apply IScalar.eq_of_val_eq
    simp [zisk_registers.REGS_IN_MAIN_TO, UScalar.hcast, UScalarTy.USize.numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all <;> decide
  have rs1Cast : UScalar.cast UScalarTy.U64 input.rs1 = 2#u64 := by rw [rs1]; decide
  have rdCast : UScalar.hcast IScalarTy.I64 input.rd = 1#i64 := by rw [rd]; decide
  have immCast : IScalar.hcast UScalarTy.U64 input.imm = 1#u64 := by rw [imm]; decide
  have immRem : input.imm % 4#i32 = ok 1#i32 := by rw [imm]; rfl
  have belowU : ¬ (2#u64 : Std.U64) < 1#u64 := by decide
  have aboveU : ¬ (2#u64 : Std.U64) > 31#u64 := by decide
  have belowI : ¬ (1#i64 : Std.I64) < 1#i64 := by decide
  have aboveI : ¬ (1#i64 : Std.I64) > 31#i64 := by decide
  have immNonzero : (1#i32 : Std.I32) ≠ 0#i32 := by decide
  have rs1Nonzero : (2#u64 : Std.U64) ≠ 0#u64 := by decide
  have rdNonzero : (1#i64 : Std.I64) ≠ 0#i64 := by decide
  have fourCast : UScalar.hcast IScalarTy.I64 (4#u64 : Std.U64) = 4#i64 := by decide
  have three : (4#i64 : Std.I64) - 1#i64 = ok 3#i64 := rfl
  have successor : (0#u64 : Std.U64) + 1#u64 = ok 1#u64 := rfl
  simp only [riscv2zisk_context.Riscv2ZiskContext.jalr, immRem, immCast, rs1Cast, rdCast,
    riscv2zisk_context.Riscv2ZiskContext.jalr.JALR_MASK,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_lastc,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.set_pc,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    fromU, toU, fromI, toI, belowU, aboveU, belowI, aboveI,
    immNonzero, rs1Nonzero, rdNonzero, fourCast, three, successor, rom,
    Bool.false_eq_true, if_false, if_true, reduceIte, bind_ok, Result.ok.injEq,
    lift, Bind.bind, defCtx] at source
  subst ctx
  simp only [Option.some.injEq] at firstRecorded lastRecorded
  subst first
  subst last
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

/-- Exact source serialization, not only a decoder shape or an opcode claim. -/
theorem worldProgram_actual_source :
    romMessagesOfRaw 0 jalrExpansionRaw = (worldAddProgramRow, some worldAndProgramRow) := by
  let raw := ZiskFv.Completeness.Rv64imShapes.rawIType 1 2 0 1 0x67
  have decodedAsI : aeneas_extract.rv64im_decode.decode_32_core (Decode.toU32 raw) =
      aeneas_extract.rv64im_decode.decode_i (Decode.toU32 raw)
        aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false := by
    simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift, Bind.bind,
      bind_ok, Decode.toU32_and127, Decode.toU32_ofNat,
      Decode.rawIType_opcode 1 2 0 1 0x67 (by norm_num)]
  obtain ⟨decoded, decodedI, opcode, rdBound, rs1Bound, _⟩ :=
    decode_i_bounds (Decode.toU32 raw) aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false
  have decodedCore := decodedAsI.trans decodedI
  let input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm }
  obtain ⟨rdBits, rs1Bits, _⟩ := decode_i_rawIType_fields 1 2 0 1 0x67
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    aeneas_extract.rv64im_decode.RiscvOpcode.Jalr decoded (by simpa only [raw] using decodedI)
  have rd : input.rd = 1#u32 := by
    apply UScalar.eq_of_val_eq
    change decoded.rd.bv.toNat = 1
    rw [rdBits]
    decide
  have rs1 : input.rs1 = 2#u32 := by
    apply UScalar.eq_of_val_eq
    change decoded.rs1.bv.toNat = 2
    rw [rs1Bits]
    decide
  have immBits : input.imm.bv = BitVec.signExtend 32 (BitVec.ofNat 12 1) :=
    decode_i_rawIType_imm 1 2 0 1 0x67 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) aeneas_extract.rv64im_decode.RiscvOpcode.Jalr decoded
      (by simpa only [raw] using decodedI)
  have imm : input.imm = 1#i32 := by
    apply IScalar.eq_of_val_eq
    change input.imm.bv.toInt = 1
    rw [immBits]
    decide
  obtain ⟨ctx, source⟩ := jalr_ok { defCtx with extract_marker := () } input
    (by simpa only [input] using rs1Bound) (by simpa only [input] using rdBound) rfl
  have pins := jalr_production_expanded_row_pins input ctx
    (by simpa only [input] using rdBound) (by simpa only [input] using rs1Bound) source
  obtain ⟨dext, decodeExtract⟩ := decode_extract_ok decoded
  have dextFields := decodeExtract
  unfold aeneas_extract.decode_extract_from_decoded at dextFields
  obtain ⟨_, _, dextFields⟩ := bind_eq_ok_imp dextFields
  obtain ⟨_, _, dextFields⟩ := bind_eq_ok_imp dextFields
  obtain ⟨_, _, dextFields⟩ := bind_eq_ok_imp dextFields
  rw [Result.ok.injEq] at dextFields
  have dextImm : dext.imm = decoded.imm := by rw [← dextFields]
  have dextRd : dext.rd = decoded.rd := by rw [← dextFields]
  have dextRs1 : dext.rs1 = decoded.rs1 := by rw [← dextFields]
  have dextRs2 : dext.rs2 = decoded.rs2 := by rw [← dextFields]
  have lower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
      defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false =
        ok { ctx with extract_marker := () } := by
    change (do
      let next ← riscv2zisk_context.Riscv2ZiskContext.jalr
        { defCtx with extract_marker := () } input 4#u64
      ok { next with extract_marker := () }) = _
    rw [source]
    rfl
  rcases pins with aligned | unaligned
  · obtain ⟨remainder, _, _⟩ := aligned
    rw [imm] at remainder
    have oneRem : (1#i32 : Std.I32) % 4#i32 = ok 1#i32 := rfl
    rw [oneRem] at remainder
    cases remainder
  · obtain ⟨rem, remainder, nonzero, first, last, firstRecorded, lastRecorded,
      firstPins, lastPins⟩ := unaligned
    obtain ⟨firstWidth, firstStoreOffset, firstPrecompiled, lastASrc, lastAHi, lastALo,
      lastWidth, lastPrecompiled⟩ := sourceJalr_remaining_fields
      input ctx first last rd rs1 imm rfl source firstRecorded lastRecorded
    obtain ⟨lastRow, extracted, aSrc, aHi, aLo, bSrc, bHi, bLo, indWidth,
      op, store, storeOffset, jmp1, jmp2, setPc, storePc, external, m32⟩ :=
      from_inst_full_fields last.i
    have extractedPrecompiled := sourceExtract_precompiled last.i lastRow extracted
    let terminal : aeneas_extract.Rv64imTranspileExtract :=
      { accepted := true, decode := dext, row := lastRow }
    have terminalExtract : aeneas_extract.extract_transpile_rv64im_raw (Decode.toU32 raw) =
        ok terminal := by
      rw [aeneas_extract.extract_transpile_rv64im_raw, decodedCore]
      simp only [bind_ok, Bind.bind, decodeExtract, opcode]
      change (do
        let input' ← riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
          decoded.rd decoded.rs1 decoded.rs2 decoded.imm
        let next ← riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input' riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let last' ← core.option.Option.unwrap next.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst last'.i
        ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      simp only [riscv2zisk_single_row.Rv64imLoweringInput.new]
      change (do
        let next ← riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let last' ← core.option.Option.unwrap next.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst last'.i
        ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      rw [lower]
      simp only [Bind.bind, lastRecorded, core.option.Option.unwrap, Result.ofOption, bind_ok]
      rw [extracted]
      rfl
    let rows : aeneas_extract.Rv64imTranspileRowsExtract :=
      { accepted := true, decode := dext, row_count := 2#u32, first_row := first, last_row := lastRow }
    have actualRows : aeneas_extract.extract_transpile_rv64im_rows_raw (Decode.toU32 raw) =
        ok rows := by
      unfold aeneas_extract.extract_transpile_rv64im_rows_raw
      rw [terminalExtract]
      simp only [Decode.toU32_and127]
      have remVal : rem.val ≠ 0 := by
        intro zero
        apply nonzero
        apply IScalar.eq_of_val_eq
        simpa using zero
      have inputNew : riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
          decoded.rd decoded.rs1 decoded.rs2 decoded.imm = ok input := rfl
      have decodedRem : decoded.imm % 4#i32 = ok rem := remainder
      norm_num [terminal, raw, dextRd, dextRs1, dextRs2, dextImm, remainder,
        decodedRem, remVal, lift, Bind.bind, inputNew, rows, core.option.Option.unwrap, Result.ofOption]
      rw [if_pos (by decide)]
      simp only [defCtx] at lower
      rw [lower]
      simp [firstRecorded]
    rcases firstPins with ⟨firstOp, firstJ1, firstJ2, firstASrc, firstAHiVal,
      firstALoVal, firstB, firstExternal, firstM32, firstSetPc, firstStorePc, firstStore⟩
    have firstAHi : first.a_use_sp_imm1 = 0#u64 := by
      apply UScalar.eq_of_val_eq
      rw [firstAHiVal, imm]
      decide
    have firstALo : first.a_offset_imm0 = 1#u64 := by
      apply UScalar.eq_of_val_eq
      rw [firstALoVal, imm]
      decide
    rcases firstB with ⟨zero, _⟩ | ⟨_, firstBSrc, firstBHi, firstBLo⟩
    · rw [rs1] at zero
      cases zero
    · change first.b_src = zisk_inst.SRC_REG at firstBSrc
      change first.b_use_sp_imm1 = 0#u64 at firstBHi
      change first.b_offset_imm0 = UScalar.cast UScalarTy.U64 input.rs1 at firstBLo
      have firstBLo' : first.b_offset_imm0 = 2#u64 := by
        rw [firstBLo, rs1]
        decide
      rcases lastPins with ⟨lastOp, lastJ1, lastJ2, destination, lastBSrc,
        lastBHi, lastBLo, lastExternal, lastM32, lastSetPc⟩
      rcases destination with ⟨zero, _⟩ |
        ⟨_, lastStore, lastStoreOffset, _, lastStorePc⟩
      · rw [rd] at zero
        cases zero
      · have lastStoreOffset' : last.i.store_offset = 1#i64 := by
          rw [lastStoreOffset, rd]
          decide
        have offsetZero : signedOffset (0#u64 : Std.U64) = 0 := by decide +kernel
        have offsetOne : signedOffset (1#u64 : Std.U64) = 1 := by decide +kernel
        have offsetTwo : signedOffset (2#u64 : Std.U64) = 2 := by decide +kernel
        have offsetMask : signedOffset (4294967294#u64 : Std.U64) = 4294967294 := by decide +kernel
        change romMessagesOfRaw 0 raw = _
        simp only [romMessagesOfRaw, actualRows]
        norm_num [rows, worldAddProgramRow, worldAndProgramRow, romRowOf,
          offsetZero, offsetOne, offsetTwo, offsetMask,
          romFlagBitsOfExtract, packFlags, worldAddBits, worldAndBits,
          JalrSpinWitness.jalrAddBits, JalrSpinWitness.jalrAndBits,
          firstOp, firstJ1, firstJ2, firstASrc, firstAHi, firstALo,
          firstBSrc, firstBHi, firstBLo', firstExternal, firstM32,
          firstSetPc, firstStorePc, firstStore, firstWidth, firstStoreOffset, firstPrecompiled,
          aSrc, aHi, aLo, bSrc, bHi, bLo, indWidth, op, store, storeOffset,
          jmp1, jmp2, setPc, storePc, external, m32, extractedPrecompiled,
          lastASrc, lastAHi, lastALo, lastWidth, lastPrecompiled, lastOp, lastJ1, lastJ2,
          lastStore, lastStoreOffset', lastStorePc, lastBSrc, lastBHi, lastBLo,
          lastExternal, lastM32, lastSetPc, ZiskFv.Trusted.OP_ADD, ZiskFv.Trusted.OP_AND,
          zisk_inst.SRC_IMM, zisk_inst.SRC_MEM, zisk_inst.SRC_REG, zisk_inst.SRC_IND,
          zisk_inst.SRC_C, zisk_inst.STORE_REG, zisk_inst.STORE_MEM, zisk_inst.STORE_IND,
          ZiskRomMessage.mk.injEq]

end SourceSerialization

@[reducible] def worldInitial (reg : FGL) : MemBusMessage FGL :=
  ZiskFv.AirsClean.RegisterBoundary.bootMessage (boundaryRowIdle reg)

@[reducible] def worldFreeCols (step a0 a1 b0 b1 : FGL)
    (previous : MemBusMessage FGL) : MainRomFreeCols :=
  mainRomFreeColsWithRegisterPrevious
    { addX1MainFreeCols with
      a_0 := a0
      a_1 := a1
      b_0 := b0
      b_1 := b1
      im_high_degree_2 := 0
      segment_l1 := 0
      main_step := step }
    previous

attribute [local simp] worldFreeCols worldInitial mainRomFreeColsWithRegisterPrevious

@[reducible] def worldRow0Template : MainRowWithRom FGL :=
  mainRomRowOf worldAddProgramRow worldAddBits (MainRomExecKind.external false 1 0)
    { worldFreeCols 0 1 0 0 0 (worldInitial 2) with segment_l1 := 1 }
@[reducible] def worldRow0WithLast :=
  materializeMainRegisterRow (worldInitial 2) worldRow0Template [.b]
def worldRow0 : MainRowWithRom FGL := worldRow0WithLast.2

@[reducible] def worldRow1Template : MainRowWithRom FGL :=
  mainRomRowOf worldAndProgramRow worldAndBits (MainRomExecKind.external false 0 0)
    (worldFreeCols 1 4294967294 4294967295 1 0 (worldInitial 1))
@[reducible] def worldRow1WithLast :=
  materializeMainRegisterRow (worldInitial 1) worldRow1Template [.store]
def worldRow1 : MainRowWithRom FGL := worldRow1WithLast.2

@[reducible] def worldRow2Template : MainRowWithRom FGL :=
  mainRomRowOf worldAddProgramRow worldAddBits (MainRomExecKind.external false 1 0)
    (worldFreeCols 2 1 0 0 0 worldRow0WithLast.1)
@[reducible] def worldRow2WithLast :=
  materializeMainRegisterRow worldRow0WithLast.1 worldRow2Template [.b]
def worldRow2 : MainRowWithRom FGL := worldRow2WithLast.2

@[reducible] def worldRow3Template : MainRowWithRom FGL :=
  mainRomRowOf worldAndProgramRow worldAndBits (MainRomExecKind.external false 0 0)
    (worldFreeCols 3 4294967294 4294967295 1 0 worldRow1WithLast.1)
@[reducible] def worldRow3WithLast :=
  materializeMainRegisterRow worldRow1WithLast.1 worldRow3Template [.store]
def worldRow3 : MainRowWithRom FGL := worldRow3WithLast.2

@[reducible] def worldRow4Template : MainRowWithRom FGL :=
  mainRomRowOf worldAddProgramRow worldAddBits (MainRomExecKind.external false 1 0)
    (worldFreeCols 4 1 0 0 0 worldRow2WithLast.1)
@[reducible] def worldRow4WithLast :=
  materializeMainRegisterRow worldRow2WithLast.1 worldRow4Template [.b]
def worldRow4 : MainRowWithRom FGL := worldRow4WithLast.2

def worldMainRows : List (MainRowWithRom FGL) :=
  [worldRow0, worldRow1, worldRow2, worldRow3, worldRow4]

theorem worldMainRows_fixed_domain : worldMainRows.length ≤ mainFixedCapacity := by
  norm_num [worldMainRows, mainFixedCapacity]

def worldMainTable : Table FGL :=
  mainRowsTable 2 worldProgram worldMainRows worldMainRows_fixed_domain

/-- The two read/write histories are actual materialized Main messages. -/
theorem worldRegisterHistories :
    (bMemMessage worldRow0).timestamp = 2 ∧
    (cMemMessage worldRow1).timestamp = 7 ∧
    (bMemMessage worldRow2).timestamp = 10 ∧
    (cMemMessage worldRow3).timestamp = 15 ∧
    (bMemMessage worldRow4).timestamp = 18 ∧
    bRegPreMessage worldRow0 = worldInitial 2 ∧
    cRegPreMessage worldRow1 = worldInitial 1 ∧
    bRegPreMessage worldRow2 = bMemMessage worldRow0 ∧
    cRegPreMessage worldRow3 = cMemMessage worldRow1 ∧
    bRegPreMessage worldRow4 = bMemMessage worldRow2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def worldBoundaryRows : List (ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :=
  [ registerBoundaryRowFromLast 1 worldRow3WithLast.1,
    registerBoundaryRowFromLast 2 worldRow4WithLast.1 ] ++
    (List.range 29).map (fun i => boundaryRowIdle ((i + 3 : Nat) : FGL))

theorem worldBoundaryRows_length : worldBoundaryRows.length ≤
    ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity := by
  simp [worldBoundaryRows, ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity]

theorem worldBoundaryRows_enumerated : RegisterBoundaryRowsEnumerated worldBoundaryRows := by
  intro i hi
  have limit : i < 31 := by simpa [worldBoundaryRows] using hi
  interval_cases i <;> rfl

def worldBoundaryTable : Table FGL :=
  registerBoundaryRowsTableOf worldBoundaryRows worldBoundaryRows_length

/-- Evaluate the ACTUAL Main range expression on actual materialized rows.
The provider payloads are not caller-supplied predicted gap numbers. -/
def worldMainRangeValues : List FGL :=
  [ Expression.eval (Environment.fromInput worldRow0 emptyData)
      (bRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow1 emptyData)
      (cRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow2 emptyData)
      (bRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow3 emptyData)
      (cRegStepDistanceExpr (varFromOffset MainRowWithRom 0)),
    Expression.eval (Environment.fromInput worldRow4 emptyData)
      (bRegStepDistanceExpr (varFromOffset MainRowWithRom 0)) ]

private theorem eval_world_b_distance (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    Expression.eval env (bRegStepDistanceExpr row) =
      (2 + (eval env row).rom.main_step * 4) - (eval env row).rom.b_reg_prev_mem_step - 1 := by
  rcases row with ⟨core, rom⟩
  cases rom
  simp [bRegStepDistanceExpr, Expression.eval, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, CircuitType.eval_expr, sub_eq_add_neg]

private theorem eval_world_c_distance (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    Expression.eval env (cRegStepDistanceExpr row) =
      (3 + (eval env row).rom.main_step * 4) - (eval env row).rom.store_reg_prev_mem_step - 1 := by
  rcases row with ⟨core, rom⟩
  cases rom
  simp [cRegStepDistanceExpr, Expression.eval, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, CircuitType.eval_expr, sub_eq_add_neg]

theorem worldMainRangeValues_actual : worldMainRangeValues = [1, 6, 7, 7, 7] := by
  simp only [worldMainRangeValues, eval_world_b_distance, eval_world_c_distance,
    ProvableType.eval_fromInput_varFromOffset_zero]
  rfl

theorem worldAllRangeValues_spec :
    ∀ v ∈ worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows,
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec v := by
  rw [worldMainRangeValues_actual]
  change ∀ v ∈ ([1, 6, 7, 7, 7] : List FGL) ++ registerBoundaryRangeValues worldBoundaryRows,
    v.val < 2 ^ 24
  letI := List.decidableBAll (fun v : FGL => v.val < 2 ^ 24)
    (([1, 6, 7, 7, 7] : List FGL) ++ registerBoundaryRangeValues worldBoundaryRows)
  decide

def worldBinaryAddRow := ZiskFv.AirsClean.BinaryAdd.binaryAddRowOf 1 0

def worldBinaryAddTable : Table FGL :=
  binaryAddRowsTable [worldBinaryAddRow, worldBinaryAddRow, worldBinaryAddRow]

private def andByte0Index : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 510, by decide⟩
private def andMiddleIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 255, by decide⟩
private def andLastIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + 65791, by decide⟩

def worldBinaryAndRow : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  ZiskFv.AirsClean.Binary.binaryStaticRowOf false false false false false
    andByte0Index andMiddleIndex andMiddleIndex andMiddleIndex
    andMiddleIndex andMiddleIndex andMiddleIndex andLastIndex

/-- The actual eight AND requests, repeated for the two terminal consumers. -/
def worldBinarySourceRequests : Fin 8 → ZiskFv.AirsClean.Binary.BinaryTableIndex
  | ⟨0, _⟩ => andByte0Index
  | ⟨7, _⟩ => andLastIndex
  | _ => andMiddleIndex

theorem worldBinarySourceRequests_weld (index : Fin 8) :
    ZiskFv.AirsClean.BinaryTable.rowOfIndex (worldBinarySourceRequests index).val =
      ZiskFv.AirsClean.BinaryTableBalance.binaryMessageRow worldBinaryAndRow index := by
  have elements :
      toElements (ZiskFv.AirsClean.BinaryTable.rowOfIndex
        (worldBinarySourceRequests index).val) =
      toElements (ZiskFv.AirsClean.BinaryTableBalance.binaryMessageRow
        worldBinaryAndRow index) := by
    fin_cases index <;> decide
  simpa only [ProvableType.fromElements_toElements] using
    congrArg (fun values =>
      (fromElements values : ZiskFv.Channels.BinaryTable.BinaryTableMessage FGL)) elements

def worldBinaryRequests : List ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  List.ofFn worldBinarySourceRequests ++ List.ofFn worldBinarySourceRequests

/-- Both full-domain providers project the same actual physical witness.
Repeated requests contribute their actual counts, not invented unit weights. -/
def worldPackedSources : ZiskFv.AirsClean.PackedVirtualTableSources.Witness FGL :=
  ZiskFv.AirsClean.PackedVirtualTableSources.physicalOfRequests (fun _ => 0)
    worldBinaryRequests []

def worldBinarySourceTable : Table FGL :=
  ZiskFv.AirsClean.PackedVirtualTableSources.binaryProviderTable worldPackedSources emptyData

def worldExtensionSourceTable : Table FGL :=
  ZiskFv.AirsClean.PackedVirtualTableSources.extensionProviderTable worldPackedSources emptyData

@[simp] theorem worldBinarySourceTable_component :
    worldBinarySourceTable.component = ZiskFv.AirsClean.BinaryTableSlice.sourceComponent := rfl

@[simp] theorem worldExtensionSourceTable_component :
    worldExtensionSourceTable.component =
      ZiskFv.AirsClean.BinaryExtensionTableSlice.sourceComponent := rfl

@[simp] theorem worldBinarySourceTable_other_channel (channel : RawChannel FGL)
    (different : channel ≠ ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw) :
    worldBinarySourceTable.interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change channel ∉ [ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw]
  simpa only [List.mem_singleton] using different

@[simp] theorem worldExtensionSourceTable_other_channel (channel : RawChannel FGL)
    (different : channel ≠
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw) :
    worldExtensionSourceTable.interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change channel ∉ [ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw]
  simpa only [List.mem_singleton] using different

/-- Two real AND provider rows, one for each consumed terminal row. -/
def worldBinaryAndTable : Table FGL :=
  { binaryConsumerSingleRowTable worldBinaryAndRow with
    rawRows := [binaryRowArray worldBinaryAndRow, binaryRowArray worldBinaryAndRow]
    raw_uniform_width := by
      intro arr harr
      have member : arr ∈ (binaryConsumerSingleRowTable worldBinaryAndRow).rawRows := by
        simpa [binaryConsumerSingleRowTable,
          ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable] using harr
      exact (binaryConsumerSingleRowTable worldBinaryAndRow).raw_uniform_width arr member
    fixed_domain := by
      intro columns hcolumns
      simp [binaryConsumerSingleRowTable,
        ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable,
        ZiskFv.AirsClean.Binary.tableConsumerComponent] at hcolumns }

private theorem worldRow_proverAssumptions (i : Fin 5) :
    (componentWithRomMemAndOpBus 2 worldProgram).circuit.ProverAssumptions
      (worldMainRows[i.val]'i.isLt) emptyData (ProverHint.empty FGL) := by
  fin_cases i
  · refine ⟨⟨0, by decide⟩, worldAddBits, MainRomExecKind.external false 1 0,
      { worldFreeCols 0 1 0 0 0 (worldInitial 2) with segment_l1 := 1 },
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [MainRomSourceGuard, worldProgram, worldAddProgramRow, worldAddBits,
        JalrSpinWitness.jalrAddBits]
    · simp [MainRomAddressGuard, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [worldMainRows, worldRow0, worldRow0Template, worldProgram, worldAddProgramRow,
        worldAddBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨1, by decide⟩, worldAndBits, MainRomExecKind.external false 0 0,
      worldFreeCols 1 4294967294 4294967295 1 0 (worldInitial 1),
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [MainRomSourceGuard, worldProgram, worldAndProgramRow, worldAndBits,
        JalrSpinWitness.jalrAndBits]
    · simp [MainRomAddressGuard, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [worldMainRows, worldRow1, worldRow1Template, worldProgram, worldAndProgramRow,
        worldAndBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨0, by decide⟩, worldAddBits, MainRomExecKind.external false 1 0,
      worldFreeCols 2 1 0 0 0 worldRow0WithLast.1,
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [MainRomSourceGuard, worldProgram, worldAddProgramRow, worldAddBits,
        JalrSpinWitness.jalrAddBits]
    · simp [MainRomAddressGuard, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [worldMainRows, worldRow2, worldRow2Template, worldProgram, worldAddProgramRow,
        worldAddBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨1, by decide⟩, worldAndBits, MainRomExecKind.external false 0 0,
      worldFreeCols 3 4294967294 4294967295 1 0 worldRow1WithLast.1,
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [MainRomSourceGuard, worldProgram, worldAndProgramRow, worldAndBits,
        JalrSpinWitness.jalrAndBits]
    · simp [MainRomAddressGuard, worldAndBits, JalrSpinWitness.jalrAndBits]
    · simp [worldMainRows, worldRow3, worldRow3Template, worldProgram, worldAndProgramRow,
        worldAndBits, mainRomRowOf, withMainRegisterPrevious]
  · refine ⟨⟨0, by decide⟩, worldAddBits, MainRomExecKind.external false 1 0,
      worldFreeCols 4 1 0 0 0 worldRow2WithLast.1,
      by decide, ?_, ?_, ?_, ?_⟩
    · simp [MainRomExecKind.Coherent, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [MainRomSourceGuard, worldProgram, worldAddProgramRow, worldAddBits,
        JalrSpinWitness.jalrAddBits]
    · simp [MainRomAddressGuard, worldAddBits, JalrSpinWitness.jalrAddBits]
    · simp [worldMainRows, worldRow4, worldRow4Template, worldProgram, worldAddProgramRow,
        worldAddBits, mainRomRowOf, withMainRegisterPrevious]

private theorem worldMain_constraintsHold_materialize (index : Nat) (row : MainRowWithRom FGL)
    (segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
    (step : row.rom.main_step = mainFixedColumns.fixedAt 1 index)
    (assumptions : (componentWithRomMemAndOpBus 2 worldProgram).circuit.ProverAssumptions
      row emptyData (ProverHint.empty FGL)) :
    (componentWithRomMemAndOpBus 2 worldProgram).operations.ConstraintsHold
      (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
  apply component_constraintsHold_of_proverAssumptions_at_data
    (componentWithRomMemAndOpBus 2 worldProgram)
    (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
    row emptyData
  · change (mainWithRomMemAndOpBusElaborated 2 worldProgram).localLength
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar = 0
    rfl
  · exact eval_mainRawRow_materialize index emptyData row segment step
  · rfl
  · exact assumptions

theorem worldMainTable_constraints : worldMainTable.Constraints := by
  change ∀ arr ∈
    [ mainFixedColumns.materialize 0 (mainRawRow worldRow0),
      mainFixedColumns.materialize 1 (mainRawRow worldRow1),
      mainFixedColumns.materialize 2 (mainRawRow worldRow2),
      mainFixedColumns.materialize 3 (mainRawRow worldRow3),
      mainFixedColumns.materialize 4 (mainRawRow worldRow4) ],
    (componentWithRomMemAndOpBus 2 worldProgram).operations.ConstraintsHold
      (Environment.fromArray arr emptyData)
  intro arr harr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at harr
  rcases harr with rfl | rfl | rfl | rfl | rfl
  · exact worldMain_constraintsHold_materialize 0 worldRow0 (by rfl) (by rfl)
      (worldRow_proverAssumptions 0)
  · exact worldMain_constraintsHold_materialize 1 worldRow1 (by rfl) (by rfl)
      (worldRow_proverAssumptions 1)
  · exact worldMain_constraintsHold_materialize 2 worldRow2 (by rfl) (by rfl)
      (worldRow_proverAssumptions 2)
  · exact worldMain_constraintsHold_materialize 3 worldRow3 (by rfl) (by rfl)
      (worldRow_proverAssumptions 3)
  · exact worldMain_constraintsHold_materialize 4 worldRow4 (by rfl) (by rfl)
      (worldRow_proverAssumptions 4)

theorem worldBinaryAddTable_constraints : worldBinaryAddTable.Constraints := by
  apply binaryAddRowsTable_constraints_of_proverAssumptions
  intro row hrow
  simp [worldBinaryAddTable] at hrow
  subst row
  exact ⟨1, 0, by decide, by decide, rfl⟩

private theorem worldBinaryAndSingle_constraints :
    (binaryConsumerSingleRowTable worldBinaryAndRow).Constraints := by
  apply binaryConsumerSingleRowTable_constraints_of_proverAssumptions
  apply ZiskFv.AirsClean.FullEnsemble.binary_consumer_prover_of_static
  refine ⟨false, false, false, false, false, andByte0Index,
    andMiddleIndex, andMiddleIndex, andMiddleIndex, andMiddleIndex,
    andMiddleIndex, andMiddleIndex, andLastIndex, ?_⟩
  norm_num [worldBinaryAndRow, andByte0Index, andMiddleIndex, andLastIndex,
    ZiskFv.AirsClean.Binary.binaryTableRow, ZiskFv.AirsClean.BinaryTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryTable.blockOfIndex, ZiskFv.AirsClean.BinaryTable.relativeIndex,
    ZiskFv.AirsClean.BinaryTable.coutOfIndex, ZiskFv.AirsClean.BinaryTable.resultIsAOfIndex,
    ZiskFv.AirsClean.BinaryTable.cIsSignedOfIndex, ZiskFv.AirsClean.BinaryTable.opOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfBlock,
    ZiskFv.AirsClean.Binary.binaryMode32AndCIsSignedOf,
    ZiskFv.AirsClean.Binary.binaryBOpOrSextOf,
    ZiskFv.AirsClean.BinaryTable.block14, ZiskFv.AirsClean.BinaryTable.block13,
    ZiskFv.AirsClean.BinaryTable.block12, ZiskFv.AirsClean.BinaryTable.block11,
    ZiskFv.AirsClean.BinaryTable.block10, ZiskFv.AirsClean.BinaryTable.block9,
    ZiskFv.AirsClean.BinaryTable.block8, ZiskFv.AirsClean.BinaryTable.block7,
    ZiskFv.AirsClean.BinaryTable.block6, ZiskFv.AirsClean.BinaryTable.block5,
    ZiskFv.AirsClean.BinaryTable.block4, ZiskFv.AirsClean.BinaryTable.block3,
    ZiskFv.AirsClean.BinaryTable.block2, ZiskFv.AirsClean.BinaryTable.block1,
    ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
    ZiskFv.AirsClean.BinaryTable.absBlockSize, ZiskFv.AirsClean.BinaryTable.fullBlockSize]

theorem worldBinaryAndTable_constraints : worldBinaryAndTable.Constraints := by
  intro arr harr
  have member : arr ∈ (binaryConsumerSingleRowTable worldBinaryAndRow).table := by
    simpa [worldBinaryAndTable, binaryConsumerSingleRowTable,
      ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable, Table.table,
      ZiskFv.AirsClean.Binary.tableConsumerComponent] using harr
  exact worldBinaryAndSingle_constraints arr member

theorem worldBoundaryTable_constraints : worldBoundaryTable.Constraints :=
  registerBoundaryRowsTableOf_constraints worldBoundaryRows worldBoundaryRows_length
    worldBoundaryRows_enumerated

@[simp] theorem worldMainTable_length : worldMainTable.length = 5 := rfl

@[simp] theorem worldMainTable_evalAt (i : Fin worldMainTable.length) :
    Eval.eval (worldMainTable.environmentAt i)
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar =
        worldMainRows[i.val]'i.isLt := by
  fin_cases i <;>
    change Eval.eval
      (Environment.fromArray (mainFixedColumns.materialize _ (mainRawRow _)) emptyData)
      (varFromOffset MainRowWithRom 0) = _ <;>
    apply eval_mainRawRow_materialize <;> rfl

theorem worldMainTable_transitions : worldMainTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  change transitionBetween
    (Eval.eval (worldMainTable.previousEnvironment index)
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar)
    (Eval.eval (worldMainTable.environmentAt index)
      (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar)
  fin_cases index <;>
    simp [Table.previousEnvironment, worldMainRows, transitionBetween,
      pcHandshakeBetween, sourceCCopyBetween, worldRow0, worldRow0Template,
      worldRow1, worldRow1Template, worldRow2, worldRow2Template,
      worldRow3, worldRow3Template, worldRow4, worldRow4Template,
      worldAddProgramRow, worldAndProgramRow, worldAddBits, worldAndBits,
      JalrSpinWitness.jalrAddBits, JalrSpinWitness.jalrAndBits,
      mainRomRowOf, withMainRegisterPrevious]

theorem worldMainTable_cyclicSuccessorTransitions :
    worldMainTable.CyclicSuccessorTransitionConstraints := by
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  simp [worldMainTable, mainRowsTable, componentWithRomMemAndOpBus]

def worldTables : List (Table FGL) :=
  [ worldBoundaryTable,
    emptyComponentTable ZiskFv.AirsClean.MemAlignReadByte.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignByte.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlign.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignRangeSlice.component,
    emptyComponentTable ZiskFv.AirsClean.MemAlignRomSlice.component,
    emptyComponentTable ZiskFv.AirsClean.Mem.componentWithDualMemBus,
    registerStepRangeRowsTable
      (worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows),
    emptyComponentTable ZiskFv.AirsClean.SpecifiedRangesSlice.component,
    emptyComponentTable ZiskFv.AirsClean.ArithDiv.component,
    emptyComponentTable ZiskFv.AirsClean.ArithMul.componentComplete,
    emptyComponentTable ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent,
    worldBinaryAndTable, worldBinaryAddTable,
    worldExtensionSourceTable, worldBinarySourceTable, worldMainTable ]

def worldEnsemble : Ensemble FGL unit := (fullRv64imEnsemble 2 worldProgram).ensemble

theorem worldEnsemble_verifier : worldEnsemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 2 worldProgram).verifier_empty

def worldWitness : EnsembleWitness worldEnsemble where
  tables := worldTables
  data := emptyData
  publicInput := ()
  same_length := by
    simp [worldEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
      worldTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
      SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable]
  same_circuits := by
    intro i hi
    have limit : i < 17 := by simpa [worldTables] using hi
    interval_cases i <;>
      simp [worldEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
        worldTables, SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_tables,
        SoundEnsemble.addTable, SoundEnsemble.empty_tables, Ensemble.addTable,
        worldBoundaryTable, registerBoundaryRowsTableOf, emptyComponentTable,
        registerStepRangeRowsTable, worldBinaryAndTable, binaryConsumerSingleRowTable,
        ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable,
        worldBinaryAddTable, binaryAddRowsTable, worldMainTable, mainRowsTable]
  same_data := by
    intro table htable
    simp only [worldTables, List.mem_cons, List.not_mem_nil, or_false] at htable
    rcases htable with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem worldWitness_table_constraints : ∀ table ∈ worldWitness.tables, table.Constraints := by
  intro table htable
  simp only [worldWitness, worldTables, List.mem_cons, List.not_mem_nil, or_false] at htable
  rcases htable with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact worldBoundaryTable_constraints
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignReadByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignByte.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlign.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRangeSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.MemAlignRomSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.Mem.componentWithDualMemBus
  · exact registerStepRangeRowsTable_constraints _ worldAllRangeValues_spec
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.SpecifiedRangesSlice.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithDiv.component
  · exact emptyComponentTable_constraints ZiskFv.AirsClean.ArithMul.componentComplete
  · exact emptyComponentTable_constraints
      ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
  · exact worldBinaryAndTable_constraints
  · exact worldBinaryAddTable_constraints
  · exact ZiskFv.AirsClean.PackedVirtualTableSources.extensionProviderTable_constraints
      worldPackedSources emptyData
  · exact ZiskFv.AirsClean.PackedVirtualTableSources.binaryProviderTable_constraints
      worldPackedSources emptyData
  · exact worldMainTable_constraints

theorem worldWitness_constraints : worldWitness.Constraints :=
  worldWitness.constraints_of_tables worldEnsemble_verifier worldWitness_table_constraints

private theorem balanced_of_all_actual_payloads (emitted : List (Interaction FGL))
    (bound : emitted.length < ringChar FGL ∨ ringChar FGL = 0)
    (checks : emitted.all (fun interaction => decide (balanceOf emitted interaction.msg = 0)) = true) :
    BalancedInteractions emitted := by
  refine balancedInteractions_of_present bound (emitted.map (·.msg)) ?_ ?_
  · intro interaction member
    exact List.mem_map.mpr ⟨interaction, member, rfl⟩
  · intro msg member
    obtain ⟨interaction, present, rfl⟩ := List.mem_map.mp member
    exact of_decide_eq_true ((List.all_eq_true.mp checks) interaction present)

private theorem worldMain_effectiveRows :
    worldMainTable.table =
      [ mainFixedColumns.materialize 0 (mainRawRow worldRow0),
        mainFixedColumns.materialize 1 (mainRawRow worldRow1),
        mainFixedColumns.materialize 2 (mainRawRow worldRow2),
        mainFixedColumns.materialize 3 (mainRawRow worldRow3),
        mainFixedColumns.materialize 4 (mainRawRow worldRow4) ] := by
  simp [worldMainTable, mainRowsTable, Table.table, componentWithRomMemAndOpBus, worldMainRows]

private theorem worldMainOp_eval (env : Environment FGL) (row : MainRowWithRom FGL)
    (input : eval env (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar = row) :
    (((OpBusChannel.emitted
      (-(componentWithRomMemAndOpBus 2 worldProgram).rowInputVar.core.is_external_op)
      (opBusMessageExpr (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar.core)).toRaw).eval env) =
        mainOpBusInteraction row := by
  let rowVar := (componentWithRomMemAndOpBus 2 worldProgram).rowInputVar
  have core : eval env rowVar.core = row.core := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
    exact congrArg MainRowWithRom.core input
  have field := ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op env rowVar.core
  simp [mainOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env (-rowVar.core.is_external_op) = -row.core.is_external_op
    simp [Expression.eval, field, core]
  constructor
  · have message : eval env (opBusMessageExpr rowVar.core) = opBusMessage row.core := by
      rw [eval_opBusMessageExpr, core]
    rw [toElements_eval_toArray]
    change (toElements (eval env (opBusMessageExpr rowVar.core))).toArray =
      (toElements (opBusMessage row.core)).toArray
    rw [message]
  · rfl

private theorem worldMain_ops :
    worldMainTable.interactionsWith OpBusChannel.toRaw =
      [mainOpBusInteraction worldRow0, mainOpBusInteraction worldRow1,
       mainOpBusInteraction worldRow2, mainOpBusInteraction worldRow3,
       mainOpBusInteraction worldRow4] := by
  rw [Table.interactionsWith, worldMain_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have atRow (index : Nat) (row : MainRowWithRom FGL)
      (segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
      (step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
      worldMainTable.component.operations.interactionValuesWith OpBusChannel.toRaw
        (worldMainTable.environment (mainFixedColumns.materialize index (mainRawRow row))) =
          [mainOpBusInteraction row] := by
    simp only [worldMainTable, mainRowsTable, Table.environment]
    simp [Operations.interactionValuesWith_eq_map,
      componentWithRomMemAndOpBus_interactionsWith_opBus]
    exact worldMainOp_eval _ row (eval_mainRawRow_materialize index emptyData row segment step)
  rw [atRow 0 worldRow0 (by rfl) (by rfl), atRow 1 worldRow1 (by rfl) (by rfl),
    atRow 2 worldRow2 (by rfl) (by rfl), atRow 3 worldRow3 (by rfl) (by rfl),
    atRow 4 worldRow4 (by rfl) (by rfl)]
  rfl

private theorem worldMain_mem :
    worldMainTable.interactionsWith MemBusChannel.toRaw =
      worldMainRows.flatMap mainValueMemBusInteractions := by
  rw [Table.interactionsWith, worldMain_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have atRow (index : Nat) (row : MainRowWithRom FGL)
      (segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
      (step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
      worldMainTable.component.operations.interactionValuesWith MemBusChannel.toRaw
        (worldMainTable.environment (mainFixedColumns.materialize index (mainRawRow row))) =
          mainValueMemBusInteractions row := by
    calc
      _ = mainMemBusInteractionsAt 2 worldProgram
          (Environment.fromArray (mainFixedColumns.materialize index (mainRawRow row)) emptyData) := by
        simpa [worldMainTable, mainRowsTable] using mainMemBusInteractionsAt_eq_component
          2 worldProgram (Environment.fromArray
            (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
      _ = mainValueMemBusInteractions row := mainMemBusInteractionsAt_eq_valueLevel
        2 worldProgram _ row (eval_mainRawRow_materialize index emptyData row segment step)
  rw [atRow 0 worldRow0 (by rfl) (by rfl), atRow 1 worldRow1 (by rfl) (by rfl),
    atRow 2 worldRow2 (by rfl) (by rfl), atRow 3 worldRow3 (by rfl) (by rfl),
    atRow 4 worldRow4 (by rfl) (by rfl)]
  rfl

private theorem worldMain_ranges :
    worldMainTable.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
      worldMainRows.flatMap (fun row =>
        [mainARegStepInteraction row, mainBRegStepInteraction row, mainCRegStepInteraction row]) := by
  rw [Table.interactionsWith, worldMain_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have atRow (index : Nat) (row : MainRowWithRom FGL)
      (segment : row.core.segment_l1 = mainFixedColumns.fixedAt 0 index)
      (step : row.rom.main_step = mainFixedColumns.fixedAt 1 index) :
      worldMainTable.component.operations.interactionValuesWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
        (worldMainTable.environment (mainFixedColumns.materialize index (mainRawRow row))) =
          [mainARegStepInteraction row, mainBRegStepInteraction row, mainCRegStepInteraction row] := by
    simpa [worldMainTable, mainRowsTable] using mainRegisterStepInteractionsAt
      2 worldProgram (Environment.fromArray
        (mainFixedColumns.materialize index (mainRawRow row)) emptyData)
      row (eval_mainRawRow_materialize index emptyData row segment step)
  rw [atRow 0 worldRow0 (by rfl) (by rfl), atRow 1 worldRow1 (by rfl) (by rfl),
    atRow 2 worldRow2 (by rfl) (by rfl), atRow 3 worldRow3 (by rfl) (by rfl),
    atRow 4 worldRow4 (by rfl) (by rfl)]
  rfl

private theorem worldAnd_emissions (channel : RawChannel FGL) :
    worldBinaryAndTable.interactionsWith channel =
      (binaryConsumerSingleRowTable worldBinaryAndRow).interactionsWith channel ++
        (binaryConsumerSingleRowTable worldBinaryAndRow).interactionsWith channel := by
  simp [worldBinaryAndTable, binaryConsumerSingleRowTable, binaryRowArray,
    ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable,
    Table.interactionsWith, Table.table,
    Table.environment, ZiskFv.AirsClean.Binary.tableConsumerComponent]

private def worldMemEmissions : List (Interaction FGL) :=
  worldBoundaryRows.flatMap registerBoundaryMemBusInteractions ++
    worldMainRows.flatMap mainValueMemBusInteractions

private theorem worldMem_emissions :
    worldWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw) = worldMemEmissions := by
  have boundary : worldBoundaryTable.interactionsWith MemBusChannel.toRaw =
      worldBoundaryRows.flatMap registerBoundaryMemBusInteractions := by
    simpa [worldBoundaryTable] using registerBoundaryRowsTableOf_interactionsWith_memBus
      worldBoundaryRows worldBoundaryRows_length worldBoundaryRows_enumerated
  have binary := ZiskFv.AirsClean.FullEnsemble.staticBinary_table_interactionsWith_memBus_nil
    (table := worldBinaryAndTable) rfl
  have add := ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_memBus_nil
    (table := worldBinaryAddTable) rfl
  simp only [worldWitness, worldTables, List.flatMap_cons, List.flatMap_nil,
    worldMemEmissions, boundary, binary, add,
    worldBinarySourceTable_other_channel MemBusChannel.toRaw
      (mt (congrArg RawChannel.name) (by decide)),
    worldExtensionSourceTable_other_channel MemBusChannel.toRaw
      (mt (congrArg RawChannel.name) (by decide)),
    emptyComponentTable_interactionsWith, worldMain_mem,
    registerStepRangeRowsTable_interactionsWith_memBus_nil,
    List.nil_append, List.append_nil, List.append_assoc]

private def worldOpEmissions : List (Interaction FGL) :=
  [binaryOpBusInteraction worldBinaryAndRow, binaryOpBusInteraction worldBinaryAndRow,
    binaryAddOpBusInteraction worldBinaryAddRow, binaryAddOpBusInteraction worldBinaryAddRow,
    binaryAddOpBusInteraction worldBinaryAddRow,
    mainOpBusInteraction worldRow0, mainOpBusInteraction worldRow1,
    mainOpBusInteraction worldRow2, mainOpBusInteraction worldRow3, mainOpBusInteraction worldRow4]

private theorem worldOp_emissions :
    worldWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) = worldOpEmissions := by
  have boundary := ZiskFv.AirsClean.FullEnsemble.registerBoundary_table_interactionsWith_opBus_nil
    (table := worldBoundaryTable) rfl
  simp only [worldWitness, worldTables, List.flatMap_cons, List.flatMap_nil,
    worldOpEmissions, boundary, emptyComponentTable_interactionsWith,
    worldBinarySourceTable_other_channel OpBusChannel.toRaw
      (mt (congrArg RawChannel.name) (by decide)),
    worldExtensionSourceTable_other_channel OpBusChannel.toRaw
      (mt (congrArg RawChannel.name) (by decide)),
    worldAnd_emissions, binaryConsumerSingleRowTable_interactionsWith_opBus,
    worldBinaryAddTable, binaryAddRowsTable_interactionsWith_opBus, worldMain_ops,
    registerStepRangeRowsTable_interactionsWith_opBus_nil,
    List.map_cons, List.map_nil, List.nil_append, List.append_nil, List.append_assoc]

private def worldRangeEmissions : List (Interaction FGL) :=
  worldBoundaryRows.map registerBoundaryRangeInteraction ++
    (worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows).map
      registerStepRangeInteraction ++
    worldMainRows.flatMap (fun row =>
      [mainARegStepInteraction row, mainBRegStepInteraction row, mainCRegStepInteraction row])

private theorem worldRange_emissions :
    worldWitness.tables.flatMap
      (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) =
        worldRangeEmissions := by
  have boundary : worldBoundaryTable.interactionsWith
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
        worldBoundaryRows.map registerBoundaryRangeInteraction := by
    simpa [worldBoundaryTable] using registerBoundaryRowsTableOf_interactionsWith_registerStepRange
      worldBoundaryRows worldBoundaryRows_length worldBoundaryRows_enumerated emptyData
  have add := ZiskFv.AirsClean.FullEnsemble.binaryAdd_table_interactionsWith_registerStepRange_nil
    (table := worldBinaryAddTable) rfl
  have binary := ZiskFv.AirsClean.FullEnsemble.staticBinary_table_interactionsWith_registerStepRange_nil
    (table := worldBinaryAndTable) rfl
  simp only [worldWitness, worldTables, List.flatMap_cons, List.flatMap_nil,
    worldRangeEmissions, emptyComponentTable_interactionsWith,
    worldBinarySourceTable_other_channel
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
      (mt (congrArg RawChannel.name) (by decide)),
    worldExtensionSourceTable_other_channel
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
      (mt (congrArg RawChannel.name) (by decide)),
    boundary, add, binary, registerStepRangeRowsTable_interactionsWith,
    worldMain_ranges, List.map_append, List.nil_append, List.append_nil, List.append_assoc]

private theorem worldOther_emissions (channel : RawChannel FGL)
    (mem : channel ≠ MemBusChannel.toRaw) (op : channel ≠ OpBusChannel.toRaw)
    (range : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)
    (binaryTable : channel ≠ ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)
    (extensionTable : channel ≠
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw) :
    worldWitness.tables.flatMap (·.interactionsWith channel) = [] := by
  have boundary : worldBoundaryTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw, ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro mem range
  have binary : worldBinaryAndTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw, ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using
      And.intro op binaryTable
  have add : worldBinaryAddTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa only [List.mem_singleton] using op
  have main : worldMainTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro mem (And.intro op range)
  have provider := registerStepRangeRowsTable_interactionsWith_of_ne
    (worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows) channel range
  simp [worldWitness, worldTables, boundary, binary, add, main, provider,
    worldBinarySourceTable_other_channel channel binaryTable,
    worldExtensionSourceTable_other_channel channel extensionTable,
    emptyComponentTable_interactionsWith]

private theorem worldChannel_ne
    (channel : RawChannel FGL) (expectedName : String) (named : channel.name = expectedName)
    (other : RawChannel FGL) (otherName : String) (otherNamed : other.name = otherName)
    (different : expectedName ≠ otherName) : channel ≠ other := by
  intro equal
  apply different
  exact named.symm.trans ((congrArg (fun raw : RawChannel FGL => raw.name) equal).trans otherNamed)

private theorem worldOther_balanced (channel : RawChannel FGL)
    (mem : channel ≠ MemBusChannel.toRaw) (op : channel ≠ OpBusChannel.toRaw)
    (range : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)
    (binaryTable : channel ≠ ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)
    (extensionTable : channel ≠
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw) :
    BalancedInteractions (worldWitness.tables.flatMap (·.interactionsWith channel)) := by
  rw [worldOther_emissions channel mem op range binaryTable extensionTable]
  apply balanced_of_all_actual_payloads
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide +kernel
  · decide +kernel

private theorem worldRanges_balanced :
    BalancedInteractions (worldWitness.tables.flatMap
      (·.interactionsWith ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw)) := by
  rw [worldRange_emissions]
  unfold worldRangeEmissions
  rw [worldMainRangeValues_actual]
  apply balanced_of_all_actual_payloads
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide +kernel
  · decide +kernel

private theorem worldMem_balanced :
    BalancedInteractions (worldWitness.tables.flatMap (·.interactionsWith MemBusChannel.toRaw)) := by
  rw [worldMem_emissions]
  apply balanced_of_all_actual_payloads
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide +kernel
  · decide +kernel

private theorem worldOps_balanced :
    BalancedInteractions (worldWitness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw)) := by
  rw [worldOp_emissions]
  apply balanced_of_all_actual_payloads
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide +kernel
  · decide +kernel

/-- Reduce only proved-silent tables; retain the actual consumer and both
full-domain source streams, including zero multiplicities. -/
private theorem worldSource_emissions (channel : RawChannel FGL)
    (mem : channel ≠ MemBusChannel.toRaw) (op : channel ≠ OpBusChannel.toRaw)
    (range : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) :
    worldWitness.tables.flatMap (·.interactionsWith channel) =
      worldBinaryAndTable.interactionsWith channel ++
        worldExtensionSourceTable.interactionsWith channel ++
          worldBinarySourceTable.interactionsWith channel := by
  have boundary : worldBoundaryTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro mem range
  have add : worldBinaryAddTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [OpBusChannel.toRaw]
    simpa only [List.mem_singleton] using op
  have main : worldMainTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw,
      ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using
      And.intro mem (And.intro op range)
  have provider := registerStepRangeRowsTable_interactionsWith_of_ne
    (worldMainRangeValues ++ registerBoundaryRangeValues worldBoundaryRows) channel range
  simp only [worldWitness, worldTables, List.flatMap_cons, List.flatMap_nil,
    boundary, add, main, provider, emptyComponentTable_interactionsWith,
    List.nil_append, List.append_nil, List.append_assoc]

private theorem worldBinary_consumer_requests :
    worldBinaryAndTable.interactionsWith
        ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw =
      ZiskFv.AirsClean.PackedVirtualTableSources.consumedSourceRequests
        ZiskFv.Channels.BinaryTable.BinaryTableChannel
        (fun index : Fin ZiskFv.AirsClean.BinaryTable.tableSize =>
          ZiskFv.AirsClean.BinaryTable.rowOfIndex index.val) worldBinaryRequests := by
  have single :
      (binaryConsumerSingleRowTable worldBinaryAndRow).interactionsWith
          ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw =
        ZiskFv.AirsClean.Binary.tableConsumerComponent.operations.interactionValuesWith
          ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
          (Environment.fromInput worldBinaryAndRow emptyData) := by
    change (ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable
      emptyData [worldBinaryAndRow]).interactionsWith _ = _
    rw [ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable_interactionsWith]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have one :
      ZiskFv.AirsClean.PackedVirtualTableSources.consumedSourceRequests
        ZiskFv.Channels.BinaryTable.BinaryTableChannel
        (fun index : Fin ZiskFv.AirsClean.BinaryTable.tableSize =>
          ZiskFv.AirsClean.BinaryTable.rowOfIndex index.val)
        (List.ofFn worldBinarySourceRequests) =
      ZiskFv.AirsClean.Binary.tableConsumerComponent.operations.interactionValuesWith
        ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw
        (Environment.fromInput worldBinaryAndRow emptyData) := by
    rw [ZiskFv.AirsClean.FullEnsemble.binary_consumer_interactions_fromInput]
    simp only [ZiskFv.AirsClean.PackedVirtualTableSources.consumedSourceRequests,
      List.map_ofFn]
    apply congrArg List.ofFn
    funext index
    simp only [Function.comp_apply, worldBinarySourceRequests_weld]
  simpa only [worldAnd_emissions, worldBinaryRequests,
    ZiskFv.AirsClean.PackedVirtualTableSources.consumedSourceRequests,
    List.map_append] using
    congrArg₂ (fun left right : List (Interaction FGL) => left ++ right)
      (single.trans one.symm) (single.trans one.symm)

/-- Both AND rows emit their real eight queries; repeated source indices are
counted across both rows in the one physical provider witness. -/
theorem worldWitness_binaryTableChannel_balanced :
    BalancedInteractions (worldWitness.tables.flatMap
      (·.interactionsWith ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)) := by
  rw [worldSource_emissions _
      (mt (congrArg RawChannel.name) (by decide))
      (mt (congrArg RawChannel.name) (by decide))
      (mt (congrArg RawChannel.name) (by decide)),
    worldExtensionSourceTable_other_channel _
      (mt (congrArg RawChannel.name) (by decide)),
    List.append_nil, worldBinary_consumer_requests]
  change BalancedInteractions
    (ZiskFv.AirsClean.PackedVirtualTableSources.consumedSourceRequests
      ZiskFv.Channels.BinaryTable.BinaryTableChannel
      (fun index : Fin ZiskFv.AirsClean.BinaryTable.tableSize =>
        ZiskFv.AirsClean.BinaryTable.rowOfIndex index.val) worldBinaryRequests ++
      (ZiskFv.AirsClean.PackedVirtualTableSources.binaryProviderTable
        worldPackedSources emptyData).interactionsWith
          ZiskFv.Channels.BinaryTable.BinaryTableChannel.toRaw)
  rw [ZiskFv.AirsClean.PackedVirtualTableSources.binaryProviderTable_interactionsWith]
  unfold worldPackedSources
  rw [ZiskFv.AirsClean.PackedVirtualTableSources.binaryInteractions_physicalOfRequests]
  apply balancedInteractions_of_perm _ List.perm_append_comm
  apply ZiskFv.AirsClean.PackedVirtualTableSources.countedSourceRequests_balanced
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  norm_num [worldBinaryRequests, ZiskFv.AirsClean.BinaryTable.tableSize]

theorem worldWitness_extensionTableChannel_balanced :
    BalancedInteractions (worldWitness.tables.flatMap
      (·.interactionsWith
        ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)) := by
  have binary : worldBinaryAndTable.interactionsWith
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw = [] := by
    apply ZiskFv.AirsClean.BinaryTableBalance.interactionsWith_nil_of_channel_names
      (table := worldBinaryAndTable)
    decide
  rw [worldSource_emissions _
      (mt (congrArg RawChannel.name) (by decide))
      (mt (congrArg RawChannel.name) (by decide))
      (mt (congrArg RawChannel.name) (by decide)),
    binary, worldBinarySourceTable_other_channel _
      (mt (congrArg RawChannel.name) (by decide)),
    List.nil_append, List.append_nil]
  change BalancedInteractions
    ((ZiskFv.AirsClean.PackedVirtualTableSources.extensionProviderTable
      worldPackedSources emptyData).interactionsWith
        ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableChannel.toRaw)
  rw [ZiskFv.AirsClean.PackedVirtualTableSources.extensionProviderTable_interactionsWith]
  exact ZiskFv.AirsClean.FullEnsemble.extension_no_requests_balanced
    (fun _ => 0) worldBinaryRequests

/-- Full actual emissions, INCLUDING the real fifth row and all31 reload rows.
The finite certificate checks every present payload, not a handpicked partition. -/
theorem worldWitness_balancedChannels : worldWitness.BalancedChannels := by
  refine worldWitness.balancedChannels_of_tables worldEnsemble_verifier ?_
  intro channel hchannel
  simp [worldEnsemble, fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact worldWitness_extensionTableChannel_balanced
  · exact worldWitness_binaryTableChannel_balanced
  · exact worldRanges_balanced
  · exact worldOther_balanced _
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
  · exact worldMem_balanced
  · exact worldOps_balanced
  · exact worldOther_balanced _
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
  · exact worldOther_balanced _
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))
      (worldChannel_ne _ _ rfl _ _ rfl (by decide))

theorem worldWitness_transitions : worldWitness.TransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.TransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp only [worldWitness, worldTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.TransitionConstraints]
      intro index
      simp [worldBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · rw [Table.TransitionConstraints]
      intro index
      simp [registerStepRangeRowsTable, ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_transitions ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_transitions
        ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
    · rw [Table.TransitionConstraints]
      intro index
      simp [worldBinaryAndTable, binaryConsumerSingleRowTable,
        ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable,
        ZiskFv.AirsClean.Binary.tableConsumerComponent]
    · rw [Table.TransitionConstraints]
      intro index
      simp [worldBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact ZiskFv.AirsClean.FullEnsemble.extension_source_transitions
        (table := worldExtensionSourceTable) rfl
    · exact ZiskFv.AirsClean.FullEnsemble.binary_source_transitions
        (table := worldBinarySourceTable) rfl
    · exact worldMainTable_transitions

theorem worldWitness_cyclicSuccessorTransitions :
    worldWitness.CyclicSuccessorTransitionConstraints := by
  intro table h_table
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    rw [Table.CyclicSuccessorTransitionConstraints]
    intro index
    simp [EnsembleWitness.verifierTable]
  · simp only [worldWitness, worldTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [worldBoundaryTable, registerBoundaryRowsTableOf,
        ZiskFv.AirsClean.RegisterBoundary.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [registerStepRangeRowsTable, ZiskFv.AirsClean.RegisterStepRangeSlice.component]
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_cyclicSuccessorTransitions ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_cyclicSuccessorTransitions
        ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [worldBinaryAndTable, binaryConsumerSingleRowTable,
        ZiskFv.AirsClean.FullEnsemble.binaryConsumerRowsTable,
        ZiskFv.AirsClean.Binary.tableConsumerComponent]
    · rw [Table.CyclicSuccessorTransitionConstraints]
      intro index
      simp [worldBinaryAddTable, binaryAddRowsTable,
        ZiskFv.AirsClean.BinaryAdd.component]
    · exact ZiskFv.AirsClean.FullEnsemble.extension_source_cyclicSuccessorTransitions
        (table := worldExtensionSourceTable) rfl
    · exact ZiskFv.AirsClean.FullEnsemble.binary_source_cyclicSuccessorTransitions
        (table := worldBinarySourceTable) rfl
    · exact worldMainTable_cyclicSuccessorTransitions

private theorem not_world_main_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠
        (componentWithRomMemAndOpBus 2 worldProgram).circuit.name)
    (h_component : component = componentWithRomMemAndOpBus 2 worldProgram) :
    False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem not_world_main_component_of_width_ne
    {component : Component FGL}
    (h_width :
      component.width ≠ (componentWithRomMemAndOpBus 2 worldProgram).width)
    (h_component : component = componentWithRomMemAndOpBus 2 worldProgram) :
    False :=
  h_width (congrArg Component.width h_component)

private theorem not_world_mutable_mem_component_of_name_ne
    {component : Component FGL}
    (h_name :
      component.circuit.name ≠
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.name)
    (h_component :
      component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    False :=
  h_name (congrArg (fun c : Component FGL => c.circuit.name) h_component)

private theorem worldWitness_main_component_cases
    {table : Table FGL}
    (h_table : table ∈ worldWitness.allTables)
    (h_component :
      table.component = componentWithRomMemAndOpBus 2 worldProgram) :
    table = worldMainTable := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · subst table
    exfalso
    exact not_world_main_component_of_width_ne (by decide) h_component
  · simp only [worldWitness, worldTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_main_component_of_name_ne (by decide) h_component
    · rfl

private theorem worldWitness_mutable_mem_component_tables_empty
    (table : Table FGL) (h_table : table ∈ worldWitness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at h_table
  rcases h_table with h_verifier | h_table
  · exfalso
    rw [h_verifier, EnsembleWitness.verifierTable_component] at h_component
    have h_verifier_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil
        2 worldProgram
    change Operations.interactionsWith MemBusChannel.toRaw
      worldEnsemble.verifierTable.operations = [] at h_verifier_nil
    rw [h_component,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at h_verifier_nil
    exact absurd h_verifier_nil (by simp)
  · simp only [worldWitness, worldTables, List.mem_cons, List.not_mem_nil, or_false] at h_table
    rcases h_table with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignReadByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignByte.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlign.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRangeSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.MemAlignRomSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.Mem.componentWithDualMemBus
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exact emptyComponentTable_table ZiskFv.AirsClean.SpecifiedRangesSlice.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithDiv.component
    · exact emptyComponentTable_table ZiskFv.AirsClean.ArithMul.componentComplete
    · exact emptyComponentTable_table
        ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component
    · exfalso
      exact not_world_mutable_mem_component_of_name_ne (by decide) h_component

theorem worldWitness_not_mutableMemPresent :
    ¬ MutableMemPresent worldWitness := by
  intro h_present
  obtain ⟨table, h_table, h_component, h_length⟩ := h_present
  have h_empty :=
    worldWitness_mutable_mem_component_tables_empty table h_table h_component
  exact absurd h_length (by simp [h_empty])

theorem worldWitness_main_height :
    ∀ table ∈ worldWitness.allTables,
      table.component = componentWithRomMemAndOpBus 2 worldProgram →
        ∀ i : Fin 4, i.val < table.table.length := by
  intro table h_table h_component i
  have h_main := worldWitness_main_component_cases h_table h_component
  subst table
  fin_cases i <;>
    norm_num [worldMainTable, ZiskFv.Compliance.AddSpinWitness.mainRowsTable,
      worldMainRows]

def worldTrace : AcceptedZiskTrace 4 where
  programLength := 2
  program := worldProgram
  witness := worldWitness
  constraints_hold := worldWitness_constraints
  channels_balanced := worldWitness_balancedChannels
  mem_replay_table := fun h => absurd h worldWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h worldWitness_not_mutableMemPresent
  transitions_hold := worldWitness_transitions
  cyclic_successor_transitions_hold := worldWitness_cyclicSuccessorTransitions
  main_height := worldWitness_main_height

theorem worldTrace_mainTable_eq :
    worldTrace.mainTable = worldMainTable := by
  exact worldWitness_main_component_cases
    (by simpa [worldTrace] using worldTrace.mainTable_mem)
    (by simpa [worldTrace] using worldTrace.mainTable_component)

end ZiskFv.Compliance.CanonicalJalrWorld
