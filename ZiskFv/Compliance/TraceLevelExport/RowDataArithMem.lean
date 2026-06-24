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

/-- Irreducible per-row residuals for the `add` archetype — the binders of
    `construction_add_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_add
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  add_input : PureSpec.AddInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok add_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok add_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some add_input.PC
  h_input_rd : add_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_add_pure add_input).nextPC
  h_rd_idx :
    add_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `addi` archetype — the binders of
    `construction_addi_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_addi
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  addi_input : PureSpec.AddiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok addi_input.r1_val (binding.stateAt i)
  h_input_imm : addi_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some addi_input.PC
  h_input_rd : addi_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_addi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val addi_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
  h_rd_idx :
    addi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `subw` archetype — the binders of
    `construction_subw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_subw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  subw_input : PureSpec.SubwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SUB_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok subw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok subw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some subw_input.PC
  h_input_rd : subw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
  h_rd_idx :
    subw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `addw` archetype — the binders of
    `construction_addw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_addw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  addw_input : PureSpec.AddwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok addw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok addw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some addw_input.PC
  h_input_rd : addw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
  h_rd_idx :
    addw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `addiw` archetype — the binders of
    `construction_addiw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_addiw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  addiw_input : PureSpec.AddiwInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok addiw_input.r1_val (binding.stateAt i)
  h_input_imm : addiw_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some addiw_input.PC
  h_input_rd : addiw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_addiw_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val addiw_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
  h_rd_idx :
    addiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `lui` archetype — the binders of
    `construction_lui_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lui
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lui_input : PureSpec.LuiInput
  imm : BitVec 20
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
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
      i.val = 0
  h_input_imm : lui_input.imm = imm
  h_input_rd : lui_input.rd = regidx_to_fin rd
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some lui_input.PC
  h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (imm ++ (0 : BitVec 12)).toNat
  h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_LUI_pure lui_input).nextPC
  h_rd_idx :
    lui_input.rd =
      Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr

/-- Irreducible per-row residuals for the `auipc` archetype — the binders of
    `construction_auipc_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_auipc
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  auipc_input : PureSpec.AuipcInput
  imm : BitVec 20
  rd : regidx
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
  h_input_imm : auipc_input.imm = imm
  h_input_rd : auipc_input.rd = regidx_to_fin rd
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some auipc_input.PC
  h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
        i.val).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = auipc_input.PC.toNat
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_AUIPC_pure auipc_input).nextPC
  h_rd_idx :
    auipc_input.rd =
      Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_no_wrap : auipc_input.PC.toNat
    + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < GL_prime
  h_pc_offset_lt_2_32 :
    (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < 4294967296

/-- Irreducible per-row residuals for the `mulw` archetype — the binders of
    `construction_mulw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_mulw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  mulw_input : PureSpec.MulwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok mulw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok mulw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some mulw_input.PC
  h_input_rd : mulw_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_MULW_pure mulw_input).nextPC
  h_rd_idx :
    mulw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  h_a23 :
    ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_3 0).val = 0
  h_b23 :
    ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_3 0).val = 0
  h_sext_choice :
    ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
        ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_1 0).val * 65536
              < 2147483648)
      ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
        ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_1 0).val * 65536
              ≥ 2147483648))
  h_rs1_value :
    (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
      = (((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_1 0).val * 65536 : ℤ)
          - ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).na 0).val * (2:ℤ)^32
  h_rs2_value :
    (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
      = (((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_1 0).val * 65536 : ℤ)
          - ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).nb 0).val * (2:ℤ)^32

/-- Irreducible per-row residuals for the `mul` archetype — the signed low-half
    MUL (op `180`).

    Unlike `mulw`/`mulhu`, signed `MUL` has NO `construction_mul_sound` and NO
    op-180 ArithMul balance selector (it was one of the seven signed-M ops with
    no sound construction).  It is therefore routed on the OpEnvelope route in the
    FENCE style: the `OpEnvelope.mul` ingredients (the `Valid_ArithMul` provider
    view `v` at row `r_a`, the primary op-bus match, the `RTypePromises`, the Arith
    rd-write memory witness, the byte bounds, the row-constraint set, and the three
    ArithMul lookup-witness structures plus the operand byte-pack equations) are
    carried as honest residual binders — exactly the facts a real honest MUL trace
    row supplies.  One extra ingredient, mirroring `RowData_fence`'s honest-shape
    facts: `h_not_forge`, the honest product-sign shape (`np = na XOR nb`, i.e. NOT
    one of the two exceptional `(na,nb,np)` shapes the shared ArithTable admits for
    op 180).  This makes the threaded `StepNoKnownDefect` obligation — the GENUINE
    `NoKnownDefect (mulEnvOf …)` of the SPECIFIC env this row constructs —
    SATISFIABLE (see `stepStrong_mul`): for an honest MUL row `¬ forge` holds and
    so `NoKnownDefect` is TRUE.  This is NOT the (false) selector-∀ shape and NOT a
    contradictory `False`-binder.  Non-vacuous: a real trace with an honest signed
    MUL row supplies all binders. -/
structure RowData_mul
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  mul_input : PureSpec.MulInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  srs1 : Signedness
  srs2 : Signedness
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  -- Decode pins (the two facts the FENCE-style `aeneasBridgeTrust` consumes), plus
  -- the four Main-row mode pins the ArithMul `aeneasBridgeTrust` reads.
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- `OpEnvelope.mul` ingredients, carried as honest residual binders.
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
      (PureSpec.execute_MULH_mul_pure mul_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a
  h_rs1_value : mul_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
  h_rs2_value : mul_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val
  -- Honest product-sign shape: NOT the exceptional forge the ArithTable admits
  -- for op 180.  Makes the threaded `NoKnownDefect` obligation SATISFIABLE.
  h_not_forge :
    ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0))

/-- Irreducible per-row residuals for the `mulh` archetype (signed × signed
    high half, op 181) — an OpEnvelope-route arm in the FENCE/MUL style.  Carries
    the `OpEnvelope.mulh` ingredients as honest residual binders, plus the honest
    `h_not_forge` shape AND the **SIGN-RANGE RESIDUAL** `h_sign_a`/`h_sign_b`
    (`na = MSB(op1)`, `nb = MSB(op2)`).  The latter stands in for the real ZisK
    indexed `range_ab` POS/NEG lookup (`arith.pil:286/289/303`) that the FV
    extraction collapses to the full `rangeTable16`; it is CARRIED, not derived.
    Non-vacuous: a real trace with an honest signed MULH row supplies all
    binders (`h_not_forge` holds, `h_sign_*` are the true operand MSBs). -/
structure RowData_mulh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  mulh_input : PureSpec.MulhInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
      (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a
  h_rs1_value : mulh_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
  h_rs2_value : mulh_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val
  -- Honest product-sign shape (forge excluded) ⇒ threaded `NoKnownDefect` SAT.
  h_not_forge :
    ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0))
  -- SIGN-RANGE RESIDUAL (carried, not derived).
  h_sign_a : (v.na r_a).val
    = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0
  h_sign_b : (v.nb r_a).val
    = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0

/-- Irreducible per-row residuals for the `mulhsu` archetype (signed × unsigned
    high half, op 179).  Mirror of `RowData_mulh` but the table pins `nb = 0`
    (op2 unsigned), so only ONE sign-range residual `h_sign_a` is carried. -/
structure RowData_mulhsu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  mulhsu_input : PureSpec.MulhsuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
      (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a
  h_rs1_value : mulhsu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
  h_rs2_value : mulhsu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val
  h_not_forge :
    ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0))
  -- SIGN-RANGE RESIDUAL on op1 only (op2 unsigned, table pins `nb = 0`).
  h_sign_a : (v.na r_a).val
    = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0

/-- Irreducible per-row residuals for the `div` archetype — the signed 64-bit
    division (op `184`, primary ArithDiv lane).

    DIV is the signed division opcode, landed on the OpEnvelope route in the
    FENCE/MUL style.  Like signed MUL it has NO `construction_div_sound` direct-lift
    (the `LT_ABS_NP` byte chain is a genuine circuit bug at `|r|=|op2|`,
    codygunton/zisk#5), so instead of a direct lift it CONSTRUCTS `OpEnvelope.div`
    and asks for the GENUINE `NoKnownDefect (divEnvOf …)` of that env, with the defect
    predicate narrowed to the exact `|r|=|op2|` forge.  The `OpEnvelope.div`
    ingredients (the `Valid_ArithDiv`
    provider view `v` at row `r_a`, the primary op-bus match, the `RTypePromises`,
    the Arith rd-write memory witness, the byte bounds, the div-by-zero / overflow
    pins, the row-constraint set, the three ArithDiv lookup-witness structures, the
    sign-bit booleans, the `np`/`nr` pins, the operand packing equations, and the
    WEAK signed remainder bound `|r| ≤ |op2|` + sign) are carried as honest residual
    binders — exactly the facts a real honest signed DIV trace row supplies.  One
    extra ingredient, mirroring `RowData_mul`'s honest-shape fact: `h_not_forge`,
    the narrowed honest shape `|r| ≠ |op2|` (NOT the exact `|r| = |op2|` false
    positive the `LT_ABS_NP` chain admits).  This makes the threaded
    `StepNoKnownDefect` obligation — the GENUINE `NoKnownDefect (divEnvOf …)` of the
    SPECIFIC env this row constructs — SATISFIABLE (see `stepStrong_div`): for an
    honest signed DIV row with a nonzero divisor has `|r| < |op2|` strictly
    (e.g. `7 / 2` rem `1`, `|1| ≠ |2|`), so `NoKnownDefect` is TRUE.  This is
    NOT the false selector-∀ and NOT a contradictory `False`-binder.  Div-by-zero
    is handled by the ArithDiv boundary constraints; signed overflow is handled
    by the signed DIV bridge.
    Non-vacuous: a real trace with an honest signed DIV row supplies all binders
    (anti-vacuity witness `honest_div_witness_not_forge`). -/
structure RowData_div
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  div_input : PureSpec.DivInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  -- Decode pins (the FENCE-style `aeneasBridgeTrust` 7-tuple).
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- `OpEnvelope.div` ingredients, carried as honest residual binders.
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) div_input.r1_val div_input.r2_val div_input.rd div_input.PC
      (PureSpec.execute_DIVREM_div_pure div_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  h_boundary :
    ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
              * (65536 * 65536 * 65536)) * 0 = 0
        ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
        ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_rs1_value :
    div_input.r1_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
          - (v.np r_a).val * (2:ℤ)^64
  h_rs2_value :
    div_input.r2_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
          - (v.nb r_a).val * (2:ℤ)^64
  -- WEAK signed remainder bound `|r| ≤ |op2|` (extraction-fidelity residual;
  -- the STRICT bound is recovered at the canonical layer from the narrowed
  -- `h_not_forge` `|r| ≠ |op2|`).
  h_r_le :
    ((ZiskFv.PackedBitVec.MulNoWrap.packed4
        (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
      - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs
  h_r_sign :
    0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
          - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt
  -- Narrowed honest shape: NOT the nonzero-divisor `|r| = |op2|` false positive.
  -- Makes the threaded `NoKnownDefect` obligation SATISFIABLE for honest DIV rows.
  h_not_forge :
    ¬ (div_input.r2_val.toInt ≠ 0
        ∧ (ZiskFv.Compliance.Defects.signedRemainderInt v r_a).natAbs
          = div_input.r2_val.toInt.natAbs)

/-- Irreducible per-row residuals for the `rem` archetype — the signed 64-bit
    remainder (op `185`, secondary ArithDiv lane).  Mirror of `RowData_div` for the
    remainder lane (`opBus_row_ArithDivSecondary`).  Carries the narrowed honest
    shape `|r| ≠ |op2|`; the divisor-zero residual stays carried. -/
structure RowData_rem
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  rem_input : PureSpec.RemInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
      (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
              * (65536 * 65536 * 65536)) * 0 = 0
        ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
        ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_rs1_value :
    rem_input.r1_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
          - (v.np r_a).val * (2:ℤ)^64
  h_rs2_value :
    rem_input.r2_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
          - (v.nb r_a).val * (2:ℤ)^64
  h_r_le :
    ((ZiskFv.PackedBitVec.MulNoWrap.packed4
        (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
      - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ rem_input.r2_val.toInt.natAbs
  h_r_sign :
    0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
          - (v.nr r_a).val * (2:ℤ)^64) * rem_input.r1_val.toInt
  h_not_forge :
    ¬ ((ZiskFv.Compliance.Defects.signedRemainderInt v r_a).natAbs
        = rem_input.r2_val.toInt.natAbs)

/-- Irreducible per-row residuals for the `divw` archetype — the signed 32-bit
    division (op `188`, `m32 = 1`, primary ArithDiv lane).  W-mode analogue of
    `RowData_div`: carries the W-mode chunk-zero pins (`h_a23`/`h_b23`/`h_d23`/
    `h_c23`), the sign-extension choice, the W-mode packing equations, and the
    narrowed W honest shape excluding the nonzero-divisor `|r₃₂| = |op2₃₂|`
    false positive. -/
structure RowData_divw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  divw_input : PureSpec.DivwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV_W
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
      (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  h_boundary :
    ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0)
  h_m32_v : v.m32 r_a = 1
  h_div_v : v.div r_a = 1
  h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0
  h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0
  h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0
  h_byte_lo :
    (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
      = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536
  h_sext_choice :
    (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0)
      ∧ (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648)
    ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255)
      ∧ (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648)
  h_rs1_value :
    (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
      = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32
  h_rs2_value :
    (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
      = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32
  -- WEAK signed-W remainder bound `|r₃₂| ≤ |op2₃₂|` (extraction-fidelity residual).
  h_r_le :
    (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
      - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs
  h_r_sign :
    0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
        * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
  h_not_forge :
    ¬ (Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32
        ∧ (ZiskFv.Compliance.Defects.signedRemainderIntW v r_a).natAbs
          = (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)

/-- Irreducible per-row residuals for the `remw` archetype — the signed 32-bit
    remainder (op `189`, `m32 = 1`, secondary ArithDiv lane).  W-mode analogue of
    `RowData_rem`; mirror of `RowData_divw` on the secondary (remainder) lane. -/
structure RowData_remw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  remw_input : PureSpec.RemwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM_W
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
      (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val bus.e2
  bounds : ZiskFv.Compliance.ByteBounds bus.e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0)
  h_m32_v : v.m32 r_a = 1
  h_div_v : v.div r_a = 1
  h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0
  h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0
  h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0
  h_byte_lo :
    (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
      = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
  h_sext_choice :
    (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0)
      ∧ (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648)
    ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255)
      ∧ (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648)
  h_rs1_value :
    (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
      = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32
  h_rs2_value :
    (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
      = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32
  h_r_le :
    (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
      - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
      ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs
  h_r_sign :
    0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
        * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
  h_not_forge :
    ¬ (Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32
        ∧ (ZiskFv.Compliance.Defects.signedRemainderIntW v r_a).natAbs
          = (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)

/-- Irreducible per-row residuals for the `mulhu` archetype — the binders of
    `construction_mulhu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_mulhu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  mulhu_input : PureSpec.MulhuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok mulhu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok mulhu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some mulhu_input.PC
  h_input_rd : mulhu_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
  h_rd_idx :
    mulhu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  h_rs1_value : mulhu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_0 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_1 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_2 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_3 0).val
  h_rs2_value : mulhu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_0 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_1 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_2 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_3 0).val

/-- Irreducible per-row residuals for the `divu` archetype — the binders of
    `construction_divu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_divu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  divu_input : PureSpec.DivuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok divu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok divu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some divu_input.PC
  h_input_rd : divu_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
  h_rd_idx :
    divu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (divuArow trace binding i h_main_active h_main_op)) 0
  h_rs1_value : divu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_0).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_1).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_2).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_3).val
  h_rs2_value : divu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_0).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_1).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_2).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_3).val

/-- Irreducible per-row residuals for the `divuw` archetype — the binders of
    `construction_divuw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_divuw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  divuw_input : PureSpec.DivuwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok divuw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok divuw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some divuw_input.PC
  h_input_rd : divuw_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
  h_rd_idx :
    divuw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (divuwArow trace binding i h_main_active h_main_op)) 0
  h_b23 :
    ((divuwArow trace binding i h_main_active h_main_op).chunks.b_2).val = 0
      ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.b_3).val = 0
  h_c23 :
    ((divuwArow trace binding i h_main_active h_main_op).chunks.c_2).val = 0
      ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.c_3).val = 0
  h_sext_choice :
    ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
        ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.a_0).val
            + ((divuwArow trace binding i h_main_active h_main_op).chunks.a_1).val * 65536
              < 2147483648)
      ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
        ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.a_0).val
            + ((divuwArow trace binding i h_main_active h_main_op).chunks.a_1).val * 65536
              ≥ 2147483648))
  h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
    = ((divuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
        + ((divuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536
  h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
    = ((divuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
        + ((divuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536

/-- Irreducible per-row residuals for the `remu` archetype — the binders of
    `construction_remu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_remu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  remu_input : PureSpec.RemuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok remu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok remu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some remu_input.PC
  h_input_rd : remu_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
  h_rd_idx :
    remu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (remuArow trace binding i h_main_active h_main_op)) 0
  h_rs1_value : remu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_0).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_1).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_2).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_3).val
  h_rs2_value : remu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_0).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_1).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_2).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_3).val

/-- Irreducible per-row residuals for the `remuw` archetype — the binders of
    `construction_remuw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_remuw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  remuw_input : PureSpec.RemuwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok remuw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok remuw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some remuw_input.PC
  h_input_rd : remuw_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
  h_rd_idx :
    remuw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (remuwArow trace binding i h_main_active h_main_op)) 0
  h_b23 :
    ((remuwArow trace binding i h_main_active h_main_op).chunks.b_2).val = 0
      ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.b_3).val = 0
  h_c23 :
    ((remuwArow trace binding i h_main_active h_main_op).chunks.c_2).val = 0
      ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.c_3).val = 0
  h_sext_choice :
    ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
            + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
              < 2147483648)
      ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
            + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
              ≥ 2147483648))
  h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
    = ((remuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
        + ((remuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536
  h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
    = ((remuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
        + ((remuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536

/-- Irreducible per-row residuals for the `sb` archetype — the binders of
    `construction_sb_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sb
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sb_input : PureSpec.SbInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = 1
  h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sb_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sb_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREB_pure sb_input).nextPC
  h_m1 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 1]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 1 : BitVec 8)
  h_m2 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 2 : BitVec 8)
  h_m3 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 3 : BitVec 8)
  h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8)
  h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8)
  h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8)
  h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)

/-- Irreducible per-row residuals for the `sh` archetype — the binders of
    `construction_sh_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sh_input : PureSpec.ShInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = 2
  h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sh_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sh_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREH_pure sh_input).nextPC
  h_m2 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 2 : BitVec 8)
  h_m3 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 3 : BitVec 8)
  h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8)
  h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8)
  h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8)
  h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)

/-- Irreducible per-row residuals for the `sw` archetype — the binders of
    `construction_sw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sw_input : PureSpec.SwInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = 4
  h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sw_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sw_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREW_pure sw_input).nextPC
  h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8)
  h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8)
  h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8)
  h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)

/-- Irreducible per-row residuals for the `sd` archetype — the binders of
    `construction_sd_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sd
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sd_input : PureSpec.SdInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sd_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sd_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STORED_pure sd_input).nextPC

/-- Irreducible per-row residuals for the `ld` archetype — the binders of
    `construction_ld_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_ld
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  ld_input : PureSpec.LdInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (8 : FGL)
  h_opcode_assumptions : PureSpec.ld_state_assumptions ld_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      ld_input.rd = 0
  h_addr2_idx :
    ld_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADD_pure ld_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lbu` archetype — the binders of
    `construction_lbu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lbu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lbu_input : PureSpec.LbuInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  execRow : List (Interaction.ExecutionBusEntry FGL)
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace binding i execRow).e1
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (1 : FGL)
  h_opcode_assumptions : PureSpec.lbu_state_assumptions lbu_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lbu_input.r1_val.toNat + (BitVec.signExtend 64 lbu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lbu_input.rd = 0
  h_addr2_idx :
    lbu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADBU_pure lbu_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lhu` archetype — the binders of
    `construction_lhu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lhu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lhu_input : PureSpec.LhuInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  execRow : List (Interaction.ExecutionBusEntry FGL)
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace binding i execRow).e1
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (2 : FGL)
  h_opcode_assumptions : PureSpec.lhu_state_assumptions lhu_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lhu_input.r1_val.toNat + (BitVec.signExtend 64 lhu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lhu_input.rd = 0
  h_addr2_idx :
    lhu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADHU_pure lhu_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lwu` archetype — the binders of
    `construction_lwu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lwu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lwu_input : PureSpec.LwuInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  execRow : List (Interaction.ExecutionBusEntry FGL)
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace binding i execRow).e1
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (4 : FGL)
  h_opcode_assumptions : PureSpec.lwu_state_assumptions lwu_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lwu_input.r1_val.toNat + (BitVec.signExtend 64 lwu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lwu_input.rd = 0
  h_addr2_idx :
    lwu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADWU_pure lwu_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lb` archetype — the binders of
    `construction_lb_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lb
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lb_input : PureSpec.LbInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_B
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (1 : FGL)
  h_opcode_assumptions : PureSpec.lb_state_assumptions lb_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lb_input.r1_val.toNat + (BitVec.signExtend 64 lb_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lb_input.rd = 0
  h_addr2_idx :
    lb_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADB_pure lb_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lh` archetype — the binders of
    `construction_lh_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lh_input : PureSpec.LhInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_H
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (2 : FGL)
  h_opcode_assumptions : PureSpec.lh_state_assumptions lh_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lh_input.r1_val.toNat + (BitVec.signExtend 64 lh_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lh_input.rd = 0
  h_addr2_idx :
    lh_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADH_pure lh_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lw` archetype — the binders of
    `construction_lw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  lw_input : PureSpec.LwInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_W
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (4 : FGL)
  h_opcode_assumptions : PureSpec.lw_state_assumptions lw_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lw_input.r1_val.toNat + (BitVec.signExtend 64 lw_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lw_input.rd = 0
  h_addr2_idx :
    lw_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADW_pure lw_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0


end ZiskFv.Compliance
