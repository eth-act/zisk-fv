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

/-- Irreducible per-row residuals for the `sub` archetype — the binders of
    `construction_sub_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sub
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sub_input : PureSpec.SubInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SUB
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
      = EStateM.Result.ok sub_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sub_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sub_input.PC
  h_input_rd : sub_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
  h_rd_idx :
    sub_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `and` archetype — the binders of
    `construction_and_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_and
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  and_input : PureSpec.AndInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
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
      = EStateM.Result.ok and_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok and_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some and_input.PC
  h_input_rd : and_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_and_pure and_input).nextPC
  h_rd_idx :
    and_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `or` archetype — the binders of
    `construction_or_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_or
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  or_input : PureSpec.OrInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_OR
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
      = EStateM.Result.ok or_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok or_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some or_input.PC
  h_input_rd : or_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_or_pure or_input).nextPC
  h_rd_idx :
    or_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `xor` archetype — the binders of
    `construction_xor_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_xor
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  xor_input : PureSpec.XorInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_XOR
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
      = EStateM.Result.ok xor_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok xor_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some xor_input.PC
  h_input_rd : xor_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
  h_rd_idx :
    xor_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slt` archetype — the binders of
    `construction_slt_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  slt_input : PureSpec.SltInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
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
      = EStateM.Result.ok slt_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok slt_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slt_input.PC
  h_input_rd : slt_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
  h_rd_idx :
    slt_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sltu` archetype — the binders of
    `construction_sltu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sltu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sltu_input : PureSpec.SltuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
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
      = EStateM.Result.ok sltu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sltu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sltu_input.PC
  h_input_rd : sltu_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
  h_rd_idx :
    sltu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `andi` archetype — the binders of
    `construction_andi_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_andi
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  andi_input : PureSpec.AndiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
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
      = EStateM.Result.ok andi_input.r1_val (binding.stateAt i)
  h_input_imm : andi_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some andi_input.PC
  h_input_rd : andi_input.rd = regidx_to_fin rd
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
  h_andi_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val andi_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
  h_rd_idx :
    andi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `ori` archetype — the binders of
    `construction_ori_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_ori
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  ori_input : PureSpec.OriInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_OR
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
      = EStateM.Result.ok ori_input.r1_val (binding.stateAt i)
  h_input_imm : ori_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some ori_input.PC
  h_input_rd : ori_input.rd = regidx_to_fin rd
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
  h_ori_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val ori_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
  h_rd_idx :
    ori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `xori` archetype — the binders of
    `construction_xori_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_xori
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  xori_input : PureSpec.XoriInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_XOR
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
      = EStateM.Result.ok xori_input.r1_val (binding.stateAt i)
  h_input_imm : xori_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some xori_input.PC
  h_input_rd : xori_input.rd = regidx_to_fin rd
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
  h_xori_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val xori_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
  h_rd_idx :
    xori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slti` archetype — the binders of
    `construction_slti_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slti
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  slti_input : PureSpec.SltiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
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
      = EStateM.Result.ok slti_input.r1_val (binding.stateAt i)
  h_input_imm : slti_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slti_input.PC
  h_input_rd : slti_input.rd = regidx_to_fin rd
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
  h_slti_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val slti_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
  h_rd_idx :
    slti_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sltiu` archetype — the binders of
    `construction_sltiu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sltiu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sltiu_input : PureSpec.SltiuInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
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
      = EStateM.Result.ok sltiu_input.r1_val (binding.stateAt i)
  h_input_imm : sltiu_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sltiu_input.PC
  h_input_rd : sltiu_input.rd = regidx_to_fin rd
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
  h_sltiu_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val sltiu_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
  h_rd_idx :
    sltiu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sll` archetype — the binders of
    `construction_sll_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sll
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sll_input : PureSpec.SllInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL
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
      = EStateM.Result.ok sll_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sll_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sll_input.PC
  h_input_rd : sll_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
  h_rd_idx :
    sll_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srl` archetype — the binders of
    `construction_srl_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srl
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  srl_input : PureSpec.SrlInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL
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
      = EStateM.Result.ok srl_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok srl_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srl_input.PC
  h_input_rd : srl_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
  h_rd_idx :
    srl_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sra` archetype — the binders of
    `construction_sra_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sra
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sra_input : PureSpec.SraInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA
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
      = EStateM.Result.ok sra_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sra_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sra_input.PC
  h_input_rd : sra_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
  h_rd_idx :
    sra_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slli` archetype — the binders of
    `construction_slli_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slli
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  slli_input : PureSpec.SlliInput
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL
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
      = EStateM.Result.ok slli_input.r1_val (binding.stateAt i)
  h_input_shamt : slli_input.shamt = shamt
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slli_input.PC
  h_input_rd : slli_input.rd = regidx_to_fin rd
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
      shamt_b_lo shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
  h_rd_idx :
    slli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srli` archetype — the binders of
    `construction_srli_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srli
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  srli_input : PureSpec.SrliInput
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL
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
      = EStateM.Result.ok srli_input.r1_val (binding.stateAt i)
  h_input_shamt : srli_input.shamt = shamt
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srli_input.PC
  h_input_rd : srli_input.rd = regidx_to_fin rd
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
      shamt_b_lo shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
  h_rd_idx :
    srli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srai` archetype — the binders of
    `construction_srai_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srai
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  srai_input : PureSpec.SraiInput
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA
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
      = EStateM.Result.ok srai_input.r1_val (binding.stateAt i)
  h_input_shamt : srai_input.shamt = shamt
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srai_input.PC
  h_input_rd : srai_input.rd = regidx_to_fin rd
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
      shamt_b_lo shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
  h_rd_idx :
    srai_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sllw` archetype — the binders of
    `construction_sllw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sllw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sllw_input : PureSpec.SllwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL_W
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
      = EStateM.Result.ok sllw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sllw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sllw_input.PC
  h_input_rd : sllw_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC
  h_rd_idx :
    sllw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srlw` archetype — the binders of
    `construction_srlw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srlw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  srlw_input : PureSpec.SrlwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL_W
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
      = EStateM.Result.ok srlw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok srlw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srlw_input.PC
  h_input_rd : srlw_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
  h_rd_idx :
    srlw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sraw` archetype — the binders of
    `construction_sraw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sraw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sraw_input : PureSpec.SrawInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA_W
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
      = EStateM.Result.ok sraw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sraw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sraw_input.PC
  h_input_rd : sraw_input.rd = regidx_to_fin rd
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
      = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC
  h_rd_idx :
    sraw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slliw` archetype — the binders of
    `construction_slliw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slliw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  slliw_input : PureSpec.SlliwInput
  r1 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL_W
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
      = EStateM.Result.ok slliw_input.r1_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slliw_input.PC
  h_input_rd : slliw_input.rd = regidx_to_fin rd
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
      shamt_w_b_lo slliw_input.shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
  h_rd_idx :
    slliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srliw` archetype — the binders of
    `construction_srliw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srliw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  srliw_input : PureSpec.SrliwInput
  r1 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL_W
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
      = EStateM.Result.ok srliw_input.r1_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srliw_input.PC
  h_input_rd : srliw_input.rd = regidx_to_fin rd
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
      shamt_w_b_lo srliw_input.shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
  h_rd_idx :
    srliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sraiw` archetype — the binders of
    `construction_sraiw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sraiw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  sraiw_input : PureSpec.SraiwInput
  r1 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA_W
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
      = EStateM.Result.ok sraiw_input.r1_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sraiw_input.PC
  h_input_rd : sraiw_input.rd = regidx_to_fin rd
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
      shamt_w_b_lo sraiw_input.shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
  h_rd_idx :
    sraiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr


end ZiskFv.Compliance
