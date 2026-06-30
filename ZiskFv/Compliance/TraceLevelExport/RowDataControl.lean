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

structure Claim_beq (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx

structure Decode_beq (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_beq trace i) : Type where
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
  -- #100: taken on flag=1 (`r1 == r2`); `jmp_offset2 = 4` fall-through.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_beq (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_beq trace i) : Type where
  beq_input : PureSpec.BeqInput
  misa_val : RegisterType Register.misa
  h_input_imm : beq_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok beq_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok beq_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some beq_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  -- #100: operand-provenance lane bridges (feeding the EQ flag derivation).
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  -- #100: taken-offset bridge (`jmp_offset1 = signExtend imm`) + PC bridge /
  -- no-wrap / bound. Replace `h_nextPC_matches`, now DERIVED via
  -- `Pilot.branch_nextPC_flag1_taken` + `branch_flag_eq_provided`.
  h_off_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val
      = (BitVec.signExtend 64 beq_input.imm).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = beq_input.PC.toNat
  h_no_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
          i.val).val
      < GL_prime
  h_pc_bound : beq_input.PC.toNat < 18446744069414584321 - 4
  h_success : (PureSpec.execute_BEQ_pure beq_input).success = true

/-- Per-op residual bundle for the `beq` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_beq` bundles them. -/
structure RowData_beq
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_beq trace i
  toDecode : Decode_beq trace i toClaim
  toInputs : Inputs_beq trace binding i toClaim

def toRowData_beq {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_beq trace i) (dec : Decode_beq trace i c)
    (ia : Inputs_beq trace binding i c) : RowData_beq trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_bne (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx

structure Decode_bne (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bne trace i) : Type where
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
  -- #100: `neg` polarity (taken on flag=0, `r1 ≠ r2`); the taken offset rides on
  -- `jmp_offset2`, `jmp_offset1 = 4` is the fall-through side.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_bne (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bne trace i) : Type where
  bne_input : PureSpec.BneInput
  misa_val : RegisterType Register.misa
  h_input_imm : bne_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bne_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bne_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bne_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  -- #100: operand-provenance lane bridges (feeding the EQ flag derivation).
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  -- #100: taken-offset bridge on `jmp_offset2` (the flag=0 side) + PC bridge /
  -- no-wrap / bound. Replace `h_nextPC_matches`, now DERIVED via
  -- `Pilot.branch_nextPC_flag0_taken` + `branch_flag_eq_provided`.
  h_off_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
        i.val).val
      = (BitVec.signExtend 64 bne_input.imm).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bne_input.PC.toNat
  h_no_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
          i.val).val
      < GL_prime
  h_pc_bound : bne_input.PC.toNat < 18446744069414584321 - 4
  h_success : (PureSpec.execute_BNE_pure bne_input).success = true

/-- Per-op residual bundle for the `bne` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_bne` bundles them. -/
structure RowData_bne
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_bne trace i
  toDecode : Decode_bne trace i toClaim
  toInputs : Inputs_bne trace binding i toClaim

def toRowData_bne {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_bne trace i) (dec : Decode_bne trace i c)
    (ia : Inputs_bne trace binding i c) : RowData_bne trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_blt (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx

structure Decode_blt (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_blt trace i) : Type where
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
  -- #100: taken on flag=1 (signed `r1 <s r2`); `jmp_offset2 = 4` fall-through.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_blt (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_blt trace i) : Type where
  blt_input : PureSpec.BltInput
  misa_val : RegisterType Register.misa
  h_input_imm : blt_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok blt_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok blt_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some blt_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  -- #100: operand-provenance lane bridges (feeding the signed LT flag derivation).
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  -- #100: taken-offset bridge (`jmp_offset1 = signExtend imm`) + PC bridge /
  -- no-wrap / bound. Replace `h_nextPC_matches`, now DERIVED via
  -- `Pilot.branch_nextPC_flag1_taken` + `branch_flag_lt_provided`.
  h_off_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val
      = (BitVec.signExtend 64 blt_input.imm).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = blt_input.PC.toNat
  h_no_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
          i.val).val
      < GL_prime
  h_pc_bound : blt_input.PC.toNat < 18446744069414584321 - 4
  h_success : (PureSpec.execute_BLT_pure blt_input).success = true

/-- Per-op residual bundle for the `blt` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_blt` bundles them. -/
structure RowData_blt
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_blt trace i
  toDecode : Decode_blt trace i toClaim
  toInputs : Inputs_blt trace binding i toClaim

def toRowData_blt {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_blt trace i) (dec : Decode_blt trace i c)
    (ia : Inputs_blt trace binding i c) : RowData_blt trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_bge (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx

structure Decode_bge (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bge trace i) : Type where
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
  -- #100: `neg` polarity (taken on flag=0, signed `r1 ≥s r2`); the taken offset
  -- rides on `jmp_offset2`, `jmp_offset1 = 4` is the fall-through side.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_bge (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bge trace i) : Type where
  bge_input : PureSpec.BgeInput
  misa_val : RegisterType Register.misa
  h_input_imm : bge_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bge_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bge_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bge_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  -- #100: operand-provenance lane bridges (feeding the signed LT flag derivation).
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  -- #100: taken-offset bridge on `jmp_offset2` (the flag=0 side) + PC bridge /
  -- no-wrap / bound. Replace `h_nextPC_matches`, now DERIVED via
  -- `Pilot.branch_nextPC_flag0_taken` + `branch_flag_lt_provided`.
  h_off_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
        i.val).val
      = (BitVec.signExtend 64 bge_input.imm).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bge_input.PC.toNat
  h_no_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
          i.val).val
      < GL_prime
  h_pc_bound : bge_input.PC.toNat < 18446744069414584321 - 4
  h_success : (PureSpec.execute_BGE_pure bge_input).success = true

/-- Per-op residual bundle for the `bge` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_bge` bundles them. -/
structure RowData_bge
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_bge trace i
  toDecode : Decode_bge trace i toClaim
  toInputs : Inputs_bge trace binding i toClaim

def toRowData_bge {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_bge trace i) (dec : Decode_bge trace i c)
    (ia : Inputs_bge trace binding i c) : RowData_bge trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_bltu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx

structure Decode_bltu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bltu trace i) : Type where
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
  -- #100 next-PC transition input (replaces the exec artifacts): the next row
  -- exists. The taken-offset pin (`jmp_offset1 = signExtend imm`) and the no-wrap
  -- bound live in `Inputs` (they reference `bltu_input`). `flag = comparison` is
  -- DERIVED in `stepStrong_bltu` from the LTU Binary provider.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_bltu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bltu trace i) : Type where
  bltu_input : PureSpec.BltuInput
  misa_val : RegisterType Register.misa
  h_input_imm : bltu_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bltu_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bltu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bltu_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  -- #100: operand-provenance lane bridges (the `a_0/a_1/b_0/b_1` Main columns
  -- carry r1/r2 — same as SLT/SLTU), feeding the LTU flag derivation.
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  -- #100: the taken-offset decode/ROM bridge (`jmp_offset1 = signExtend imm`),
  -- the PC provenance bridge, the taken-target no-wrap bound, and the PC
  -- trajectory bound. These replace the cross-world `h_nextPC_matches`, now
  -- DERIVED via `Pilot.branch_nextPC_flag1_taken` + `branch_flag_ltu_provided`.
  h_off_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val
      = (BitVec.signExtend 64 bltu_input.imm).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bltu_input.PC.toNat
  h_no_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
          i.val).val
      < GL_prime
  h_pc_bound : bltu_input.PC.toNat < 18446744069414584321 - 4
  h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true

/-- Per-op residual bundle for the `bltu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_bltu` bundles them. -/
structure RowData_bltu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_bltu trace i
  toDecode : Decode_bltu trace i toClaim
  toInputs : Inputs_bltu trace binding i toClaim

def toRowData_bltu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_bltu trace i) (dec : Decode_bltu trace i c)
    (ia : Inputs_bltu trace binding i c) : RowData_bltu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_bgeu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx

structure Decode_bgeu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bgeu trace i) : Type where
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
  -- #100 next-PC transition input (replaces the exec artifacts): the next row
  -- exists. BGEU is the `create_branch_op`-`neg` polarity (taken on `flag = 0`):
  -- the taken offset rides on `jmp_offset2` (`Inputs`); `jmp_offset1 = 4` is the
  -- fall-through side. `flag = comparison` is DERIVED in `stepStrong_bgeu`.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_bgeu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bgeu trace i) : Type where
  bgeu_input : PureSpec.BgeuInput
  misa_val : RegisterType Register.misa
  h_input_imm : bgeu_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bgeu_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bgeu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bgeu_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  -- #100: operand-provenance lane bridges (feeding the LTU flag derivation).
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  -- #100: the taken-offset decode/ROM bridge — for BGEU the taken offset rides
  -- on `jmp_offset2` (the `flag = 0` side) — plus PC bridge / no-wrap / bound.
  -- These replace `h_nextPC_matches`, now DERIVED via
  -- `Pilot.branch_nextPC_flag0_taken` + `branch_flag_ltu_provided`.
  h_off_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
        i.val).val
      = (BitVec.signExtend 64 bgeu_input.imm).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bgeu_input.PC.toNat
  h_no_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
          i.val).val
      < GL_prime
  h_pc_bound : bgeu_input.PC.toNat < 18446744069414584321 - 4
  h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true

/-- Per-op residual bundle for the `bgeu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_bgeu` bundles them. -/
structure RowData_bgeu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_bgeu trace i
  toDecode : Decode_bgeu trace i toClaim
  toInputs : Inputs_bgeu trace binding i toClaim

def toRowData_bgeu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_bgeu trace i) (dec : Decode_bgeu trace i c)
    (ia : Inputs_bgeu trace binding i c) : RowData_bgeu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_jal (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 21
  rd : regidx

structure Decode_jal (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i) : Type where
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
  h_store_ind :
    (mainRowWithRomLui trace i).rom.store_ind = 0
  h_store_offset :
    (mainRowWithRomLui trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  -- #100 next-PC transition input (replaces the exec artifacts; JAL already
  -- carries h_set_pc above): the next row exists. The taken-offset pin
  -- (`jmp_offset1 = signExtend imm`) and the target no-wrap bound live in
  -- Inputs (they reference `jal_input.imm`). `flag = 1` is DERIVED in
  -- `stepStrong_jal` from the OP_FLAG decode pins + `internal_op0_sets_flag`.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure Inputs_jal (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i) : Type where
  jal_input : PureSpec.JalInput
  misa_val : RegisterType Register.misa
  nextPC_val : BitVec 64
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = jal_input.PC.toNat
  -- #100: the taken-offset decode/ROM bridge (`jmp_offset1 = signExtend imm`,
  -- Rust lowerer `zib.j(imm, 4)`; cf. `RowShape/Contract.lean` JAL arm, line 246)
  -- — the same unsigned-equal offset contract AUIPC's `h_offset_bridge` uses —
  -- plus the JAL-target no-wrap bound (target stays below the GL bound). These
  -- replace the cross-world `h_nextPC_matches`, now DERIVED via
  -- `Pilot.flag_path_nextPC_discharged` + `Pilot.ofNat_fgl_pc_plus_offset_eq`.
  h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val
      = (BitVec.signExtend 64 jal_input.imm).toNat
  h_no_fgl_wrap :
    jal_input.PC.toNat + (BitVec.signExtend 64 jal_input.imm).toNat < GL_prime
  h_input_rd : jal_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jal_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JAL_pure jal_input).success = true
  h_nextPC_option : (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val
  h_input_imm : jal_input.imm = c.imm
  h_pc_bound : jal_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296

/-- Per-op residual bundle for the `jal` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_jal` bundles them. -/
structure RowData_jal
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_jal trace i
  toDecode : Decode_jal trace i toClaim
  toInputs : Inputs_jal trace binding i toClaim

def toRowData_jal {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_jal trace i) (dec : Decode_jal trace i c)
    (ia : Inputs_jal trace binding i c) : RowData_jal trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_jalr (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  -- #100: the `jmp_offset1` offset as a `BitVec 64` (aligned: `signExtend imm`;
  -- unaligned: `0`). Bridged to the committed `jmp_offset1` column in `Decode`.
  offset_bv : BitVec 64

structure Decode_jalr (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type where
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
  h_store_ind :
    (mainRowWithRomLui trace i).rom.store_ind = 0
  h_store_offset :
    (mainRowWithRomLui trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  -- #100 next-PC transition inputs (replace the exec artifacts; the next-PC
  -- residual is now DERIVED via `jalr_setpc_nextPC_discharged`). All are
  -- same-world circuit / decode / ROM pins (no Sail-binding dependency).
  --   * `h_idx`: the next Main row exists (cross-row boundary marker).
  h_idx : i.val + 1 < trace.mainTable.table.length
  --   * mask `a`-lane pins (`JALR_MASK = 0xFFFFFFFFFFFFFFFE` loaded into `a`,
  --     `riscv2zisk_context.rs::jalr` `src_a("imm", JALR_MASK)`):
  --     `a_0 = 0xFFFFFFFE`, `a_1 = 0xFFFFFFFF`.
  h_a_mask_lo :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0
      i.val = 4294967294
  h_a_mask_hi :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1
      i.val = 4294967295
  --   * the 32-bit-PC scope pin `c_1 = 0` (JALR analogue of JAL/AUIPC's
  --     `h_pc_offset_lt_2_32`: the AND result's hi lane is dropped by the
  --     set-PC handshake, so the jump must stay inside ZisK's 32-bit PC space).
  h_c1_zero :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_1
      i.val = 0
  --   * the `jmp_offset1` field ↔ `offset_bv` bridge (unsigned-equal offset
  --     contract, same shape AUIPC/JAL use) + the evenness ROM guard
  --     (aligned `imm % 4 == 0` ⇒ `offset_bv` even; trivial for unaligned
  --     `offset_bv = 0`) + the field-level no-FGL-wrap bound.
  h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val = c.offset_bv.toNat
  h_offset_even : c.offset_bv &&& 1#64 = 0#64
  h_no_fgl_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0 i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
          i.val).val < GL_prime

structure Inputs_jalr (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type where
  jalr_input : PureSpec.JalrInput
  misa_val : RegisterType Register.misa
  mseccfg : RegisterType Register.mseccfg
  nextPC_val : BitVec 64
  -- #100: the per-lowering operand identity replacing the cross-world
  -- `h_nextPC_matches`. The committed Main `b`-lane (`b_0 + b_1 · 2^32`) plus
  -- `offset_bv` equals Sail's pre-mask target `rs1_val + signExtend 64 imm`:
  --   * aligned   (`b = rs1`,        `offset_bv = signExtend imm`);
  --   * unaligned (`b = rs1 + imm`,  `offset_bv = 0`).
  -- A TRUE, satisfiable fact for a real JALR row in BOTH lowerings (the masking
  -- itself is handled downstream by `jalr_setpc_nextPC_discharged`).
  h_operand_offset :
    BitVec.ofNat 64
        (((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
          + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1
              i.val).val * 4294967296)
      + c.offset_bv
      = jalr_input.rs1_val + BitVec.signExtend 64 jalr_input.imm
  h_input_rd : jalr_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jalr_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JALR_pure jalr_input).success = true
  h_nextPC_option : (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val
  h_input_imm : jalr_input.imm = c.imm
  h_input_rs1 : read_xreg (regidx_to_fin c.rs1) (binding i)
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

/-- Per-op residual bundle for the `jalr` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_jalr` bundles them. -/
structure RowData_jalr
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_jalr trace i
  toDecode : Decode_jalr trace i toClaim
  toInputs : Inputs_jalr trace binding i toClaim

def toRowData_jalr {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_jalr trace i) (dec : Decode_jalr trace i c)
    (ia : Inputs_jalr trace binding i c) : RowData_jalr trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_fence (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  fm : BitVec 4
  fenceP : BitVec 4
  fenceS : BitVec 4
  rs : regidx
  rd : regidx

structure Decode_fence (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the FENCE-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `self.nop()` →
  -- `riscv2zisk_context.rs:772`, `j(4, 4)`; cf. `ZiskFv/SailSpec/fence.lean:13`).
  -- FENCE is op = OP_FLAG (flag = 1), but with jmp1 = jmp2 = 4 the handshake's
  -- `flag * (jmp1 - jmp2)` term vanishes, so the mux still collapses to pc + 4.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_fm_zero : c.fm = 0#4
  h_rs_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rs
  h_rd_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rd

structure Inputs_fence (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i) : Type where
  fence_input : PureSpec.FenceInput
  h_input_pc : (binding i).regs.get? Register.PC = .some fence_input.PC
  h_input_priv :
    (binding i).regs.get? Register.cur_privilege = .some Privilege.Machine
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = fence_input.PC.toNat
  h_pc_bound : fence_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `fence` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_fence` bundles them. -/
structure RowData_fence
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_fence trace i
  toDecode : Decode_fence trace i toClaim
  toInputs : Inputs_fence trace binding i toClaim

def toRowData_fence {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_fence trace i) (dec : Decode_fence trace i c)
    (ia : Inputs_fence trace binding i c) : RowData_fence trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

end ZiskFv.Compliance
