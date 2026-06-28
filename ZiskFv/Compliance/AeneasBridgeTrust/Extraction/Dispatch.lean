/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Dispatch.lean  (eth-act/zisk-fv#111)

DISPATCHER-LEVEL static decode / row-mode pins for all 63 RV64IM opcodes, taken
through the REAL top-level lowerer
`riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input`
(`trust/aeneas/ProductionM2.lean:2918`), NOT merely the builder entry points.

This addresses the external-review finding on PR #160: the per-opcode pins in
`Extraction/{ControlUType,Branch,RegisterOp,Immediate,LoadStore}.lean` are stated
about the BUILDER entry points (`create_register_op_typed`, `immediate_op_typed`,
`load_op_typed`, `lui`, …).  Each theorem here goes through the DISPATCHER, states
the EXACT side condition(s) under which `lower_rv64im_single_row_input` routes the
opcode to its entry point, discharges every other branch via `if_neg` / the side
conditions, and then REDUCES to the corresponding entry-point lemma.  The
entry-point lemmas are kept as the reusable core.

Side-condition summary (matching the dispatcher's branch guards verbatim):
  * Register ALU/M ops (SUB/AND/XOR/SLT/SLTU/SLL/SRL/SRA, the W-ops, MUL…REMUW),
    branches, the plain immediates (SLLI/SRLI/SRAI/SLTI/SLTIU/ANDI, SLLIW/SRLIW/
    SRAIW), all loads (LB…LD) and stores (SB…SD), LUI/JAL/JALR/FENCE static, and
    JAL/JALR/AUIPC unconditional static pins: NO side condition (the dispatcher
    routes them unconditionally).
  * ADD : `self.input_precompile = none` (rules out the DMA precompile branch),
    `rd ≠ 0`, `rs1 ≠ 0`, `rs2 ≠ 0` (rule out the copyb degeneracies).
  * OR  : `rs1 ≠ 0`, `rs2 ≠ 0` (copyb degeneracies).
  * ADDI: `rd ≠ 0`, `imm ≠ 0`, `rs1 ≠ 0` (the first two route to
    `immediate_op_or_x0_copyb_typed`, the last selects its op arm over copyb).
  * XORI / ORI: `rs1 ≠ 0` (the `immediate_op_or_x0_copyb_typed` op arm).
  * ADDIW: `rd ≠ 0` (routes to `immediate_op_typed`).
  * AUIPC / JAL row-mode (`store_pc = true`): a nonzero rd cast
    (`UScalar.hcast .I64 rd ≠ 0#i64`); JALR row-mode: `rd ≠ 0#u32`.
    These mirror `store_reg`'s `offset = 0 ⇒ ok self` early return.

Sound: NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`.
The only `decide` use is the closed `(0#u32 : Std.U32) ≠ 2068#u32` literal fact in
the ADD proof (CSR_DMA_MEMCMP_ADDR ≠ 0); kernel-checked, not native.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.ControlUType
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Branch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.RegisterOp
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Immediate
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.LoadStore

open Aeneas Aeneas.Std Result zisk_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

namespace ZiskFv.Compliance.Extraction

/-! ## Unconditional register / branch / plain-immediate arms (entry arity 4, ext = true).

The dispatcher routes each of these opcodes to its builder entry point with NO
guard; the proof peels the `{self1 with extract_marker := ()}` wrapper and applies
the entry lemma. -/

local macro "regd_s" nm:ident "," opc:term "," opcx:term "," m32x:term : command => do
  let dS := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dispatch_static_pins")
  let eS := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $dS:ident (self ri hni ctx)
      (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            self ri $opc hni = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = true ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false := by
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      Bind.bind, bind_ok] at h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact $eS _ _ _ _ hself1)

local macro "regd_r" nm:ident "," opc:term "," opNx:term "," m32x:term : command => do
  let dR := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dispatch_extracted_rowMode_pins")
  let eR := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $dR:ident (self ri hni ctx)
      (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            self ri $opc hni = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = $m32x ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false := by
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      Bind.bind, bind_ok] at h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact $eR _ _ _ _ hself1)

-- Register ALU / M ops (all unconditional; ADD / OR are conditional, see below).
regd_s sub, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sub, 11#u8, false
regd_r sub, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sub, ExtractedConst.opSub, false
regd_s and, riscv2zisk_single_row.Rv64imSingleRowOpcode.And, 14#u8, false
regd_r and, riscv2zisk_single_row.Rv64imSingleRowOpcode.And, ExtractedConst.opAnd, false
regd_s xor, riscv2zisk_single_row.Rv64imSingleRowOpcode.Xor, 16#u8, false
regd_r xor, riscv2zisk_single_row.Rv64imSingleRowOpcode.Xor, ExtractedConst.opXor, false
regd_s slt, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slt, 7#u8, false
regd_r slt, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slt, ExtractedConst.opLt, false
regd_s sltu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltu, 6#u8, false
regd_r sltu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltu, ExtractedConst.opLtu, false
regd_s sll, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sll, 33#u8, false
regd_r sll, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sll, ExtractedConst.opSll, false
regd_s srl, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srl, 34#u8, false
regd_r srl, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srl, ExtractedConst.opSrl, false
regd_s sra, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sra, 35#u8, false
regd_r sra, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sra, ExtractedConst.opSra, false
regd_s addw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Addw, 26#u8, true
regd_r addw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Addw, ExtractedConst.opAddW, true
regd_s subw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Subw, 27#u8, true
regd_r subw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Subw, ExtractedConst.opSubW, true
regd_s sllw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sllw, 36#u8, true
regd_r sllw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sllw, ExtractedConst.opSllW, true
regd_s srlw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srlw, 37#u8, true
regd_r srlw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srlw, ExtractedConst.opSrlW, true
regd_s sraw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraw, 38#u8, true
regd_r sraw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraw, ExtractedConst.opSraW, true
regd_s mul, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mul, 180#u8, false
regd_r mul, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mul, ExtractedConst.opMul, false
regd_s mulh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulh, 181#u8, false
regd_r mulh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulh, ExtractedConst.opMulH, false
regd_s mulhsu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhsu, 179#u8, false
regd_r mulhsu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhsu, ExtractedConst.opMulSUH, false
regd_s mulhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhu, 177#u8, false
regd_r mulhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhu, ExtractedConst.opMulUH, false
regd_s mulw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulw, 182#u8, true
regd_r mulw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulw, ExtractedConst.opMulW, true
regd_s div, riscv2zisk_single_row.Rv64imSingleRowOpcode.Div, 186#u8, false
regd_r div, riscv2zisk_single_row.Rv64imSingleRowOpcode.Div, ExtractedConst.opDiv, false
regd_s divu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divu, 184#u8, false
regd_r divu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divu, ExtractedConst.opDivU, false
regd_s divw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divw, 190#u8, true
regd_r divw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divw, ExtractedConst.opDivW, true
regd_s divuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divuw, 188#u8, true
regd_r divuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divuw, ExtractedConst.opDivUW, true
regd_s rem, riscv2zisk_single_row.Rv64imSingleRowOpcode.Rem, 187#u8, false
regd_r rem, riscv2zisk_single_row.Rv64imSingleRowOpcode.Rem, ExtractedConst.opRem, false
regd_s remu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remu, 185#u8, false
regd_r remu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remu, ExtractedConst.opRemU, false
regd_s remw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remw, 191#u8, true
regd_r remw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remw, ExtractedConst.opRemW, true
regd_s remuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remuw, 189#u8, true
regd_r remuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remuw, ExtractedConst.opRemUW, true

-- Branches.
regd_s beq, riscv2zisk_single_row.Rv64imSingleRowOpcode.Beq, 9#u8, false
regd_r beq, riscv2zisk_single_row.Rv64imSingleRowOpcode.Beq, ExtractedConst.opEq, false
regd_s bne, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bne, 9#u8, false
regd_r bne, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bne, ExtractedConst.opEq, false
regd_s blt, riscv2zisk_single_row.Rv64imSingleRowOpcode.Blt, 7#u8, false
regd_r blt, riscv2zisk_single_row.Rv64imSingleRowOpcode.Blt, ExtractedConst.opLt, false
regd_s bge, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bge, 7#u8, false
regd_r bge, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bge, ExtractedConst.opLt, false
regd_s bltu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bltu, 6#u8, false
regd_r bltu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bltu, ExtractedConst.opLtu, false
regd_s bgeu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bgeu, 6#u8, false
regd_r bgeu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bgeu, ExtractedConst.opLtu, false

-- Plain immediates (SLLI/SRLI/SRAI, SLTI/SLTIU, ANDI, SLLIW/SRLIW/SRAIW).
regd_s slli, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slli, 33#u8, false
regd_r slli, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slli, ExtractedConst.opSll, false
regd_s srli, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srli, 34#u8, false
regd_r srli, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srli, ExtractedConst.opSrl, false
regd_s srai, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srai, 35#u8, false
regd_r srai, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srai, ExtractedConst.opSra, false
regd_s slti, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slti, 7#u8, false
regd_r slti, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slti, ExtractedConst.opLt, false
regd_s sltiu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltiu, 6#u8, false
regd_r sltiu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltiu, ExtractedConst.opLtu, false
regd_s andi, riscv2zisk_single_row.Rv64imSingleRowOpcode.Andi, 14#u8, false
regd_r andi, riscv2zisk_single_row.Rv64imSingleRowOpcode.Andi, ExtractedConst.opAnd, false
regd_s slliw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slliw, 36#u8, true
regd_r slliw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slliw, ExtractedConst.opSllW, true
regd_s srliw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srliw, 37#u8, true
regd_r srliw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srliw, ExtractedConst.opSrlW, true
regd_s sraiw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraiw, 38#u8, true
regd_r sraiw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraiw, ExtractedConst.opSraW, true

/-! ## Loads / stores (entry arity 5; is_external_op carried as a parameter). -/

local macro "memd_s" nm:ident "," opc:term "," opcx:term "," m32x:term "," extx:term : command => do
  let dS := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dispatch_static_pins")
  let eS := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $dS:ident (self ri hni ctx)
      (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            self ri $opc hni = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = $extx ∧ zib.i.m32 = $m32x ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false := by
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      Bind.bind, bind_ok] at h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact $eS _ _ _ _ _ hself1)

local macro "memd_r" nm:ident "," opc:term "," opNx:term "," m32x:term "," extx:term : command => do
  let dR := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dispatch_extracted_rowMode_pins")
  let eR := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $dR:ident (self ri hni ctx)
      (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            self ri $opc hni = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = $extx ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = $m32x ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false := by
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      Bind.bind, bind_ok] at h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact $eR _ _ _ _ _ hself1)

memd_s lb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lb, 39#u8, false, true
memd_r lb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lb, ExtractedConst.opSignextendB, false, true
memd_s lh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lh, 40#u8, false, true
memd_r lh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lh, ExtractedConst.opSignextendH, false, true
memd_s lw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lw, 41#u8, true, true
memd_r lw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lw, ExtractedConst.opSignextendW, true, true
memd_s lbu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lbu, 1#u8, false, false
memd_r lbu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lbu, ExtractedConst.opCopyB, false, false
memd_s lhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lhu, 1#u8, false, false
memd_r lhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lhu, ExtractedConst.opCopyB, false, false
memd_s lwu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lwu, 1#u8, false, false
memd_r lwu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lwu, ExtractedConst.opCopyB, false, false
memd_s ld, riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld, 1#u8, false, false
memd_r ld, riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld, ExtractedConst.opCopyB, false, false
memd_s sb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sb, 1#u8, false, false
memd_r sb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sb, ExtractedConst.opCopyB, false, false
memd_s sh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sh, 1#u8, false, false
memd_r sh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sh, ExtractedConst.opCopyB, false, false
memd_s sw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sw, 1#u8, false, false
memd_r sw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sw, ExtractedConst.opCopyB, false, false
memd_s sd, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sd, 1#u8, false, false
memd_r sd, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sd, ExtractedConst.opCopyB, false, false

/-! ## XORI / ORI : route to `immediate_op_or_x0_copyb_typed`; entry needs rs1 ≠ 0. -/

local macro "x0d_s" nm:ident "," opc:term "," opcx:term : command => do
  let dS := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dispatch_static_pins")
  let eS := Lean.mkIdentFrom nm (nm.getId.appendAfter "_static_pins")
  `(theorem $dS:ident (self ri hni ctx) (hrs1 : ri.rs1 ≠ 0#u32)
      (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            self ri $opc hni = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        zib.i.op = $opcx ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
        zib.i.set_pc = false ∧ zib.i.store_pc = false := by
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      Bind.bind, bind_ok] at h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact $eS _ _ _ _ hrs1 hself1)

local macro "x0d_r" nm:ident "," opc:term "," opNx:term : command => do
  let dR := Lean.mkIdentFrom nm (nm.getId.appendAfter "_dispatch_extracted_rowMode_pins")
  let eR := Lean.mkIdentFrom nm (nm.getId.appendAfter "_extracted_rowMode_pins")
  `(theorem $dR:ident (self ri hni ctx) (hrs1 : ri.rs1 ≠ 0#u32)
      (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            self ri $opc hni = ok ctx) :
      ∃ zib, ctx.extract_inst = some zib ∧
        (mainExtractedRowOfZiskInst zib.i).op = $opNx ∧
        (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
        (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
        (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
        (mainExtractedRowOfZiskInst zib.i).storePc = false := by
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      Bind.bind, bind_ok] at h
    obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
    rw [Result.ok.injEq] at h; subst h
    exact $eR _ _ _ _ hrs1 hself1)

x0d_s xori, riscv2zisk_single_row.Rv64imSingleRowOpcode.Xori, 16#u8
x0d_r xori, riscv2zisk_single_row.Rv64imSingleRowOpcode.Xori, ExtractedConst.opXor
x0d_s ori, riscv2zisk_single_row.Rv64imSingleRowOpcode.Ori, 15#u8
x0d_r ori, riscv2zisk_single_row.Rv64imSingleRowOpcode.Ori, ExtractedConst.opOr

/-! ## LUI : unconditional → `lui` (op = CopyB, is_external_op = false). -/

theorem lui_dispatch_static_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Lui hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 1#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact lui_static_pins _ _ _ _ hself1

theorem lui_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Lui hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opCopyB ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact lui_extracted_rowMode_pins _ _ _ _ hself1

/-! ## AUIPC : unconditional → `auipc`; row-mode `store_pc = true` needs nonzero rd. -/

theorem auipc_dispatch_static_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Auipc hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact auipc_static_pins _ _ _ hself1

theorem auipc_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hrd : (UScalar.hcast IScalarTy.I64 ri.rd : Std.I64) ≠ 0#i64)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Auipc hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opFlag ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = true := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact auipc_extracted_rowMode_pins _ _ _ hrd hself1

/-! ## JAL : unconditional → `jal`; row-mode `store_pc = true` needs nonzero rd. -/

theorem jal_dispatch_static_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Jal hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧
      ((UScalar.hcast IScalarTy.I64 ri.rd : Std.I64) ≠ 0#i64 → zib.i.store_pc = true) := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact jal_static_pins _ _ _ _ hself1

theorem jal_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hrd : (UScalar.hcast IScalarTy.I64 ri.rd : Std.I64) ≠ 0#i64)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Jal hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opFlag ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = true := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact jal_extracted_rowMode_pins _ _ _ _ hrd hself1

/-! ## JALR : unconditional → `jalr` (op = And, set_pc = true); row-mode needs rd ≠ 0. -/

theorem jalr_dispatch_static_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 14#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = true := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact jalr_static_pins _ _ _ _ hself1

theorem jalr_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hrd : ri.rd ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opAnd ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = true ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = true := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact jalr_extracted_rowMode_pins _ _ _ _ hrd hself1

/-! ## FENCE : unconditional → `nop` (op = Flag). -/

theorem fence_dispatch_static_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Fence hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 0#u8 ∧ zib.i.is_external_op = false ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact nop_static_pins _ _ _ _ hself1

theorem fence_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Fence hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opFlag ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = false ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact fence_extracted_rowMode_pins _ _ _ _ hself1

/-! ## ADD : degenerate-input branches.  Routes to `create_register_op_typed Add`
under `input_precompile = none`, `rd ≠ 0`, `rs1 ≠ 0`, `rs2 ≠ 0`. -/

set_option maxHeartbeats 2000000 in
theorem add_dispatch_static_pins (self ri hni ctx)
    (hprec : self.input_precompile = none)
    (hrd : ri.rd ≠ 0#u32) (hrs1 : ri.rs1 ≠ 0#u32) (hrs2 : ri.rs2 ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Add hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 10#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    hprec, riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR, Bind.bind, bind_ok] at h
  -- `rd ≠ 0`, `rs1 ≠ 0`, `rs2 ≠ 0` kill the copyb ifs; the CSR-MEMCMP literal `0 ≠ 2068`
  -- kills the precompile if; full simp also zeta-reduces the resulting `(o, ip)` tuple let.
  simp [ne_eq, hrd, hrs1, hrs2, reduceIte,
    show ((0#u32 : Std.U32) = 2068#u32) = False from by decide] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact add_static_pins _ _ _ _ hself1

set_option maxHeartbeats 2000000 in
theorem add_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hprec : self.input_precompile = none)
    (hrd : ri.rd ≠ 0#u32) (hrs1 : ri.rs1 ≠ 0#u32) (hrs2 : ri.rs2 ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Add hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opAdd ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    hprec, riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR, Bind.bind, bind_ok] at h
  simp [ne_eq, hrd, hrs1, hrs2, reduceIte,
    show ((0#u32 : Std.U32) = 2068#u32) = False from by decide] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact add_extracted_rowMode_pins _ _ _ _ hself1

/-! ## OR : copyb degeneracies.  Routes to `create_register_op_typed Or` under
`rs1 ≠ 0`, `rs2 ≠ 0`. -/

set_option maxHeartbeats 2000000 in
theorem or_dispatch_static_pins (self ri hni ctx)
    (hrs1 : ri.rs1 ≠ 0#u32) (hrs2 : ri.rs2 ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Or hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 15#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  rw [if_neg hrs1, if_neg hrs2] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact or_static_pins _ _ _ _ hself1

set_option maxHeartbeats 2000000 in
theorem or_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hrs1 : ri.rs1 ≠ 0#u32) (hrs2 : ri.rs2 ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Or hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opOr ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  rw [if_neg hrs1, if_neg hrs2] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact or_extracted_rowMode_pins _ _ _ _ hself1

/-! ## ADDI : routes to `immediate_op_or_x0_copyb_typed Add` under `rd ≠ 0`,
`imm ≠ 0`; the op arm (over copyb) additionally needs `rs1 ≠ 0`. -/

set_option maxHeartbeats 2000000 in
theorem addi_dispatch_static_pins (self ri hni ctx)
    (hrd : ri.rd ≠ 0#u32) (himm : ri.imm ≠ 0#i32) (hrs1 : ri.rs1 ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Addi hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 10#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = false ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  rw [if_neg hrd, if_neg himm] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact addi_static_pins _ _ _ _ hrs1 hself1

set_option maxHeartbeats 2000000 in
theorem addi_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hrd : ri.rd ≠ 0#u32) (himm : ri.imm ≠ 0#i32) (hrs1 : ri.rs1 ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Addi hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opAdd ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = false ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  rw [if_neg hrd, if_neg himm] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact addi_extracted_rowMode_pins _ _ _ _ hrs1 hself1

/-! ## ADDIW : routes to `immediate_op_typed AddW` under `rd ≠ 0`. -/

set_option maxHeartbeats 2000000 in
theorem addiw_dispatch_static_pins (self ri hni ctx)
    (hrd : ri.rd ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Addiw hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.op = 26#u8 ∧ zib.i.is_external_op = true ∧ zib.i.m32 = true ∧
      zib.i.set_pc = false ∧ zib.i.store_pc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  rw [if_neg hrd] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact addiw_static_pins _ _ _ _ hself1

set_option maxHeartbeats 2000000 in
theorem addiw_dispatch_extracted_rowMode_pins (self ri hni ctx)
    (hrd : ri.rd ≠ 0#u32)
    (h : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          self ri riscv2zisk_single_row.Rv64imSingleRowOpcode.Addiw hni = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (mainExtractedRowOfZiskInst zib.i).op = ExtractedConst.opAddW ∧
      (mainExtractedRowOfZiskInst zib.i).isExternalOp = true ∧
      (mainExtractedRowOfZiskInst zib.i).m32 = true ∧
      (mainExtractedRowOfZiskInst zib.i).setPc = false ∧
      (mainExtractedRowOfZiskInst zib.i).storePc = false := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    Bind.bind, bind_ok] at h
  rw [if_neg hrd] at h
  obtain ⟨self1, hself1, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h; subst h
  exact addiw_extracted_rowMode_pins _ _ _ _ hself1

end ZiskFv.Compliance.Extraction
