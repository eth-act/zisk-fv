import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.ConstructionLogic
import ZiskFv.Compliance.ConstructionCompare
import ZiskFv.Compliance.ConstructionIType
import ZiskFv.Compliance.ConstructionShift
import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.Compliance.ConstructionWAlu
import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.ConstructionAuipc
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.TraceLevelExport.Base

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open Interaction

-- The M-extension row-computing defs are reducible/semireducible; structure-field
-- elaboration would otherwise whnf-reduce the full per-row ArithMul/ArithDiv
-- computation (a runaway). `seal` blocks that locally without touching the
-- committed construction proofs (which keep the defs as-is in their oleans).
seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

/-- Irreducible per-row residuals for the `beq` archetype — the binders of
    `construction_beq_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_beq
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  beq_input : PureSpec.BeqInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BEQ `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_EQ
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_input_imm : beq_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
    = EStateM.Result.ok beq_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
    = EStateM.Result.ok beq_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some beq_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BEQ_pure beq_input).nextPC
  h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false
  h_success : (PureSpec.execute_BEQ_pure beq_input).success = true

/-- Irreducible per-row residuals for the `bne` archetype — the binders of
    `construction_bne_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bne
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  bne_input : PureSpec.BneInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BNE `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_EQ
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_input_imm : bne_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
    = EStateM.Result.ok bne_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
    = EStateM.Result.ok bne_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bne_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BNE_pure bne_input).nextPC
  h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false
  h_success : (PureSpec.execute_BNE_pure bne_input).success = true

/-- Irreducible per-row residuals for the `blt` archetype — the binders of
    `construction_blt_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_blt
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  blt_input : PureSpec.BltInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BLT `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_input_imm : blt_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
    = EStateM.Result.ok blt_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
    = EStateM.Result.ok blt_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some blt_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BLT_pure blt_input).nextPC
  h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false
  h_success : (PureSpec.execute_BLT_pure blt_input).success = true

/-- Irreducible per-row residuals for the `bge` archetype — the binders of
    `construction_bge_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bge
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  bge_input : PureSpec.BgeInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BGE `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_input_imm : bge_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
    = EStateM.Result.ok bge_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
    = EStateM.Result.ok bge_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bge_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BGE_pure bge_input).nextPC
  h_not_throws : (PureSpec.execute_BGE_pure bge_input).throws = false
  h_success : (PureSpec.execute_BGE_pure bge_input).success = true

/-- Irreducible per-row residuals for the `bltu` archetype — the binders of
    `construction_bltu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bltu
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  bltu_input : PureSpec.BltuInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BLTU `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_input_imm : bltu_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
    = EStateM.Result.ok bltu_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
    = EStateM.Result.ok bltu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bltu_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BLTU_pure bltu_input).nextPC
  h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false
  h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true

/-- Irreducible per-row residuals for the `bgeu` archetype — the binders of
    `construction_bgeu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bgeu
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  bgeu_input : PureSpec.BgeuInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BGEU `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_input_imm : bgeu_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
    = EStateM.Result.ok bgeu_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
    = EStateM.Result.ok bgeu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bgeu_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BGEU_pure bgeu_input).nextPC
  h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false
  h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true

/-- Irreducible per-row residuals for the `jal` archetype — the binders of
    `construction_jal_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_jal
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  jal_input : PureSpec.JalInput
  imm : BitVec 21
  rd : regidx
  misa_val : RegisterType Register.misa
  nextPC_val : BitVec 64
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 1
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = jal_input.PC.toNat
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = nextPC_val
  h_input_rd : jal_input.rd = regidx_to_fin rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jal_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JAL_pure jal_input).success = true
  h_nextPC_option : (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val
  h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_input_imm : jal_input.imm = imm
  h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false
  h_pc_bound : jal_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296

/-- Irreducible per-row residuals for the `jalr` archetype — the binders of
    `construction_jalr_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_jalr
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  jalr_input : PureSpec.JalrInput
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  misa_val : RegisterType Register.misa
  mseccfg : RegisterType Register.mseccfg
  nextPC_val : BitVec 64
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_flag :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).flag
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 1
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = nextPC_val
  h_input_rd : jalr_input.rd = regidx_to_fin rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jalr_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JALR_pure jalr_input).success = true
  h_nextPC_option : (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val
  h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_input_imm : jalr_input.imm = imm
  h_input_rs1 : read_xreg (regidx_to_fin rs1) (binding i)
    = EStateM.Result.ok jalr_input.rs1_val (binding i)
  h_cur_privilege : Sail.readReg Register.cur_privilege (binding i)
    = EStateM.Result.ok Privilege.Machine (binding i)
  h_mseccfg : Sail.readReg Register.mseccfg (binding i)
    = EStateM.Result.ok mseccfg (binding i)
  h_link_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val
      + (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
          i.val).val
      = (jalr_input.PC + 4#64).toNat
  h_pc_bound : jalr_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296

/-- Irreducible per-row residuals for the `fence` archetype — the FENCE decode arm.

    FENCE is the FENCE-decode-gap opcode (`ZISK-DEFECT-FENCE-INCOMPLETE`).  It is
    routed through the OpEnvelope just like `beq` (direct-construct, carrying the
    `FencePromises` facts + bridge pins as binders), with ONE extra ingredient: the
    THREE honest-shape facts (`fm = 0`, `rs = x0`, `rd = x0`) that the FENCE defect
    gate (`Defects.FenceKnownGoodShape`) requires.  These three facts make the
    threaded `StepNoKnownDefect` obligation — the GENUINE `NoKnownDefect` of the
    SPECIFIC `OpEnvelope.fence` env this row constructs — SATISFIABLE (see
    `stepStrong_fence`): for an honest FENCE row the env is the honest env and
    `NoKnownDefect` is TRUE.  This is NOT the (false) selector-∀ shape, and it is
    NOT a contradictory `False`-binder: the malicious FENCE shapes are excluded by
    the honest caller supplying these three pins, exactly as the FENCE defect ledger
    documents.  Non-vacuous: a real trace with a generic `fm=0,rs1=x0,rd=x0` FENCE
    row supplies all binders and proves the `NoKnownDefect` obligation. -/
structure RowData_fence
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  fence_input : PureSpec.FenceInput
  fm : BitVec 4
  fenceP : BitVec 4
  fenceS : BitVec 4
  rs : regidx
  rd : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (the two facts the FENCE `aeneasBridgeTrust` consumes).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  -- FENCE `FencePromises` residuals (the six structural binders).
  h_input_pc : (binding i).regs.get? Register.PC = .some fence_input.PC
  h_input_priv :
    (binding i).regs.get? Register.cur_privilege = .some Privilege.Machine
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_FENCE_pure fence_input).nextPC
  -- Honest-shape facts: the modeled (ZisK-accepted) generic FENCE subset.
  -- These make the threaded `NoKnownDefect` obligation SATISFIABLE (not vacuous).
  h_fm_zero : fm = 0#4
  h_rs_x0 : ZiskFv.Compliance.Defects.IsX0Reg rs
  h_rd_x0 : ZiskFv.Compliance.Defects.IsX0Reg rd


end ZiskFv.Compliance
