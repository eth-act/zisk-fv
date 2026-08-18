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

/-- Branch theorem-domain range assumptions.

This is not a decoded placement fact: it is the explicit soundness-domain condition needed by the
branch next-PC cast. Keeping it separate from `Inputs_<branch>` leaves those input records focused
on Sail/ZisK state and value agreement. -/
def BranchRangeDomain (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (pc takenOffset : BitVec 64) : Prop :=
  0 ≤ (pc.toNat : Int) + takenOffset.toInt
    ∧ (pc.toNat : Int) + takenOffset.toInt < GL_prime
    ∧ pc.toNat < GL_prime - 4

/-- JAL theorem-domain range assumptions.

These preserve the old JAL target no-wrap, PC-bound, and 32-bit next-PC obligations at the explicit
soundness theorem boundary instead of mixing them into `Inputs_jal` state/value agreement. -/
structure JalRangeDomain (jal_input : PureSpec.JalInput) : Prop where
  h_target_nonneg :
    0 ≤ (jal_input.PC.toNat : Int) + (BitVec.signExtend 64 jal_input.imm).toInt
  h_target_lt :
    (jal_input.PC.toNat : Int) + (BitVec.signExtend 64 jal_input.imm).toInt < GL_prime
  h_pc_bound : jal_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296

/-- JALR theorem-domain range assumptions.

These preserve the old JALR link-PC range obligations at the explicit soundness theorem boundary
instead of mixing them into `Inputs_jalr` state/value agreement. -/
structure JalrRangeDomain (jalr_input : PureSpec.JalrInput) : Prop where
  h_pc_bound : jalr_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296

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
  h_jmp_offset1_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100: taken on flag=1 (`r1 == r2`); `jmp_offset2 = 4` fall-through.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_beq (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_success : (PureSpec.execute_BEQ_pure beq_input).success = true

/-- The PC agreement `Inputs_beq` carries on top of `InputsCore_beq`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_beq (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_beq trace i) : Type extends InputsCore_beq trace binding i c where
  -- #100: PC bridge. The range/domain facts used by the branch next-PC cast live
  -- in `RowOutsideDefectRegion` as `BranchRangeDomain`.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = beq_input.PC.toNat

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
  h_jmp_offset2_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100: `neg` polarity (taken on flag=0, `r1 ≠ r2`); the taken offset rides on
  -- `jmp_offset2`, `jmp_offset1 = 4` is the fall-through side.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_bne (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_success : (PureSpec.execute_BNE_pure bne_input).success = true

/-- The PC agreement `Inputs_bne` carries on top of `InputsCore_bne`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_bne (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bne trace i) : Type extends InputsCore_bne trace binding i c where
  -- #100: PC bridge. The range/domain facts used by the branch next-PC cast live
  -- in `RowOutsideDefectRegion` as `BranchRangeDomain`.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bne_input.PC.toNat

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
  h_jmp_offset1_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100: taken on flag=1 (signed `r1 <s r2`); `jmp_offset2 = 4` fall-through.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_blt (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_success : (PureSpec.execute_BLT_pure blt_input).success = true

/-- The PC agreement `Inputs_blt` carries on top of `InputsCore_blt`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_blt (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_blt trace i) : Type extends InputsCore_blt trace binding i c where
  -- #100: PC bridge. The range/domain facts used by the branch next-PC cast live
  -- in `RowOutsideDefectRegion` as `BranchRangeDomain`.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = blt_input.PC.toNat

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
  h_jmp_offset2_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100: `neg` polarity (taken on flag=0, signed `r1 ≥s r2`); the taken offset
  -- rides on `jmp_offset2`, `jmp_offset1 = 4` is the fall-through side.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_bge (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_success : (PureSpec.execute_BGE_pure bge_input).success = true

/-- The PC agreement `Inputs_bge` carries on top of `InputsCore_bge`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_bge (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bge trace i) : Type extends InputsCore_bge trace binding i c where
  -- #100: PC bridge. The range/domain facts used by the branch next-PC cast live
  -- in `RowOutsideDefectRegion` as `BranchRangeDomain`.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bge_input.PC.toNat

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
  h_jmp_offset1_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100 next-PC transition input (replaces the exec artifacts): the next row
  -- exists. The taken-offset pin (`jmp_offset1 = signExtend imm`) is decoded from
  -- the committed program; `flag = comparison` is DERIVED in `stepStrong_bltu`
  -- from the LTU Binary provider.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_bltu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true

/-- The PC agreement `Inputs_bltu` carries on top of `InputsCore_bltu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_bltu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bltu trace i) : Type extends InputsCore_bltu trace binding i c where
  -- #100: PC bridge. The range/domain facts used by the branch next-PC cast live
  -- in `RowOutsideDefectRegion` as `BranchRangeDomain`.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bltu_input.PC.toNat

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
  h_jmp_offset2_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100 next-PC transition input (replaces the exec artifacts): the next row
  -- exists. BGEU is the `create_branch_op`-`neg` polarity (taken on `flag = 0`):
  -- the taken offset rides on `jmp_offset2`; `jmp_offset1 = 4` is the fall-through
  -- side. `flag = comparison` is DERIVED in `stepStrong_bgeu`.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_bgeu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true

/-- The PC agreement `Inputs_bgeu` carries on top of `InputsCore_bgeu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_bgeu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_bgeu trace i) : Type extends InputsCore_bgeu trace binding i c where
  -- #100: PC bridge. The range/domain facts used by the branch next-PC cast live
  -- in `RowOutsideDefectRegion` as `BranchRangeDomain`.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = bgeu_input.PC.toNat

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
  h_jmp_offset1_imm :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = ((BitVec.signExtend 64 c.imm).toInt : FGL)
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  -- #100 next-PC transition input (replaces the exec artifacts; JAL already
  -- carries h_set_pc above): the next row exists. The taken-offset pin is
  -- committed-program decode (`h_jmp_offset1_imm`); the target no-wrap bound
  -- still lives in Inputs because it references `jal_input.PC`. `flag = 1` is DERIVED in
  -- the dispatcher's `jal` arm from the OP_FLAG decode pins via
  -- `flag_eq_one_of_internal_op_zero`.
  h_idx : i.val + 1 < trace.mainTable.table.length

structure InputsCore_jal (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i) : Type where
  jal_input : PureSpec.JalInput
  misa_val : RegisterType Register.misa
  -- #100: PC bridge. The JAL range/domain facts live in `RowOutsideDefectRegion`
  -- as `JalRangeDomain`.
  h_input_rd : jal_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jal_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JAL_pure jal_input).success = true
  h_input_imm : jal_input.imm = c.imm

/-- The PC agreement `Inputs_jal` carries on top of `InputsCore_jal`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_jal (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i) : Type extends InputsCore_jal trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = jal_input.PC.toNat

-- `jal` and `jalr` have no `RowData_<op>` bundle: their dispatch arms consume
-- the `Claim`/`Decode`/`Inputs` triple directly (the `jalr` conclusion is stated
-- at the decode-selected lowering row, which a `RowData` bundle cannot index).

/-- Physical Main-row placement for one architectural JALR.

The aligned lowering occupies one Main row. The unaligned lowering occupies an
`OP_ADD` row followed immediately by the terminal `OP_AND` row. These indices
are decode/placement evidence about committed rows; they are not an
accepted-trace certificate or an architectural-to-physical map. -/
structure JalrLoweringRows
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (imm : BitVec 12)
    (rs1 : regidx)
    (offset_bv : BitVec 64) where
  start : Fin trace.mainTable.table.length
  finish : Fin trace.mainTable.table.length
  architectural_start : start.val = i.val
  finish_has_successor : finish.val + 1 < trace.mainTable.table.length
  lowering :
    (start = finish
      ∧ offset_bv = BitVec.signExtend 64 imm)
    ∨
    (start.val + 1 = finish.val
      ∧ offset_bv = 0#64
      ∧ (mainOfTable trace.program trace.mainTable).op start.val = ZiskFv.Trusted.OP_ADD
      ∧ (mainOfTable trace.program trace.mainTable).is_external_op start.val = 1
      ∧ (mainOfTable trace.program trace.mainTable).m32 start.val = 0
      ∧ (mainOfTable trace.program trace.mainTable).flag start.val = 0
      ∧ (mainOfTable trace.program trace.mainTable).set_pc start.val = 0
      ∧ (mainOfTable trace.program trace.mainTable).jmp_offset2 start.val = 1
      ∧ BitVec.ofNat 64
          (((mainOfTable trace.program trace.mainTable).a_0 start.val).val
            + ((mainOfTable trace.program trace.mainTable).a_1 start.val).val * 4294967296)
          = BitVec.signExtend 64 imm
      ∧ (mainRowWithRomAt trace start).rom.b_src_imm =
          ZiskFv.AirsClean.boolF (decide ((regidx_to_fin rs1).val = 0))
      ∧ (mainRowWithRomAt trace start).rom.b_src_reg =
          ZiskFv.AirsClean.boolF (decide ((regidx_to_fin rs1).val ≠ 0))
      ∧ (mainRowWithRomAt trace finish).rom.b_src_imm = 0
      ∧ (mainRowWithRomAt trace finish).rom.b_src_mem = 0
      ∧ (mainRowWithRomAt trace finish).rom.b_src_ind = 0
      ∧ (mainRowWithRomAt trace finish).rom.b_src_reg = 0)

structure Claim_jalr (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  -- #100: the `jmp_offset1` offset as a `BitVec 64` (aligned: `signExtend imm`;
  -- unaligned: `0`). Bridged to the committed `jmp_offset1` column in `Decode`.
  offset_bv : BitVec 64

structure Decode_jalr (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type where
  rows : JalrLoweringRows trace i c.imm c.rs1 c.offset_bv
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      rows.finish.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      rows.finish.val = 1
  h_flag :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).flag
      rows.finish.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      rows.finish.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      rows.finish.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      rows.finish.val =
        ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0))
  h_store_ind :
    (mainRowWithRomAt trace rows.finish).rom.store_ind = 0
  h_store_offset :
    (mainRowWithRomAt trace rows.finish).rom.store_offset =
      if (regidx_to_fin c.rd).val = 0 then 0 else Transpiler.ind (regidx_to_fin c.rd)
  -- #100 next-PC transition inputs (replace the exec artifacts; the next-PC
  -- residual is now DERIVED via `jalr_setpc_nextPC_discharged`). All are
  -- same-world circuit / decode / ROM pins (no Sail-binding dependency).
  --   * `h_idx`: the next Main row exists (cross-row boundary marker).
  h_idx : rows.finish.val + 1 < trace.mainTable.table.length
  --   * mask `a`-lane pins (`JALR_MASK = 0xFFFFFFFFFFFFFFFE` loaded into `a`,
  --     `riscv2zisk_context.rs::jalr` `src_a("imm", JALR_MASK)`):
  --     `a_0 = 0xFFFFFFFE`, `a_1 = 0xFFFFFFFF`.
  h_a_mask_lo :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0
      rows.finish.val = 4294967294
  h_a_mask_hi :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1
      rows.finish.val = 4294967295
  --   * the 32-bit-PC scope pin `c_1 = 0` (JALR analogue of JAL/AUIPC's
  --     `h_pc_offset_lt_2_32`: the AND result's hi lane is dropped by the
  --     set-PC handshake, so the jump must stay inside ZisK's 32-bit PC space).
  h_c1_zero :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_1
      rows.finish.val = 0
  h_jmp2 :
    (rows.start = rows.finish
      ∧ (mainOfTable trace.program trace.mainTable).jmp_offset2 rows.finish.val = 4)
    ∨
    (rows.start.val + 1 = rows.finish.val
      ∧ (mainOfTable trace.program trace.mainTable).jmp_offset2 rows.finish.val = 3)
  --   * the `jmp_offset1` field ↔ `offset_bv` bridge (unsigned-equal offset
  --     contract, same shape AUIPC/JAL use) + the evenness ROM guard
  --     (aligned `imm % 4 == 0` ⇒ `offset_bv` even; trivial for unaligned
  --     `offset_bv = 0`) + the field-level no-FGL-wrap bound.
  h_offset_bridge :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      rows.finish.val = (c.offset_bv.toInt : FGL)
  h_offset_even : c.offset_bv &&& 1#64 = 0#64
  h_target_nonneg :
    0 ≤ (((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0
      rows.finish.val).val : Int) + c.offset_bv.toInt
  h_target_lt :
    (((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0
      rows.finish.val).val : Int) + c.offset_bv.toInt < GL_prime

structure InputsCore_jalr (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type where
  jalr_input : PureSpec.JalrInput
  misa_val : RegisterType Register.misa
  mseccfg : RegisterType Register.mseccfg
  /-- Genuine cross-world input agreement at the lowering's source row.

  This says only that the committed register-sourced `b` operand equals Sail's
  `rs1` value. For an unaligned lowering, the ADD result, source-C copy into the
  terminal AND row, and zero terminal offset are derived from live circuit,
  provider, transition, and decode evidence. -/
  h_rs1_start :
    BitVec.ofNat 64
        (((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0
            i.val).val
          + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1
              i.val).val * 4294967296)
      = jalr_input.rs1_val
  h_input_rd : jalr_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jalr_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JALR_pure jalr_input).success = true
  h_input_imm : jalr_input.imm = c.imm
  h_input_rs1 : read_xreg (regidx_to_fin c.rs1) (binding i)
    = EStateM.Result.ok jalr_input.rs1_val (binding i)
  h_cur_privilege : Sail.readReg Register.cur_privilege (binding i)
    = EStateM.Result.ok Privilege.Machine (binding i)
  h_mseccfg : Sail.readReg Register.mseccfg (binding i)
    = EStateM.Result.ok mseccfg (binding i)
  -- #100: JALR link-PC range/domain facts live in `RowOutsideDefectRegion`
  -- as `JalrRangeDomain`.

/-- The PC agreement `Inputs_jalr` carries on top of `InputsCore_jalr`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_jalr (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type extends InputsCore_jalr trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = jalr_input.PC.toNat


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

structure InputsCore_fence (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i) : Type where
  fence_input : PureSpec.FenceInput
  h_input_pc : (binding i).regs.get? Register.PC = .some fence_input.PC
  h_input_priv :
    (binding i).regs.get? Register.cur_privilege = .some Privilege.Machine

/-- The PC agreement `Inputs_fence` carries on top of `InputsCore_fence`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_fence (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i) : Type extends InputsCore_fence trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = fence_input.PC.toNat

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
