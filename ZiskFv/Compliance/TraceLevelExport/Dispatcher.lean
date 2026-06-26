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
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl
import ZiskFv.Compliance.TraceLevelExport.EnvOf
import ZiskFv.Compliance.TraceLevelExport.StepStrongAluArith
import ZiskFv.Compliance.TraceLevelExport.StepStrongControlStore
import ZiskFv.Compliance.TraceLevelExport.StepStrongLoadMext
import ZiskFv.Compliance.TraceLevelExport.StepStrongSignedM
import ZiskFv.Compliance.TraceLevelExport.RowDataSplit

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

/-! ## Strong sum + dispatcher + top-level strengthened export -/


/-- The ZisK side of one trace step: which RV64IM op the row decoded to,
    together with that op's `Claim_<op>` (decoded operand / destination
    indices + committed bus row).  One constructor per RV64IM archetype. -/

inductive ZiskStep (ziskTrace : AcceptedZiskTrace numInstructions) (i : Fin ziskTrace.numInstructions) where
  | sub (c : Claim_sub ziskTrace i) : ZiskStep ziskTrace i
  | and (c : Claim_and ziskTrace i) : ZiskStep ziskTrace i
  | or (c : Claim_or ziskTrace i) : ZiskStep ziskTrace i
  | xor (c : Claim_xor ziskTrace i) : ZiskStep ziskTrace i
  | slt (c : Claim_slt ziskTrace i) : ZiskStep ziskTrace i
  | sltu (c : Claim_sltu ziskTrace i) : ZiskStep ziskTrace i
  | andi (c : Claim_andi ziskTrace i) : ZiskStep ziskTrace i
  | ori (c : Claim_ori ziskTrace i) : ZiskStep ziskTrace i
  | xori (c : Claim_xori ziskTrace i) : ZiskStep ziskTrace i
  | slti (c : Claim_slti ziskTrace i) : ZiskStep ziskTrace i
  | sltiu (c : Claim_sltiu ziskTrace i) : ZiskStep ziskTrace i
  | sll (c : Claim_sll ziskTrace i) : ZiskStep ziskTrace i
  | srl (c : Claim_srl ziskTrace i) : ZiskStep ziskTrace i
  | sra (c : Claim_sra ziskTrace i) : ZiskStep ziskTrace i
  | slli (c : Claim_slli ziskTrace i) : ZiskStep ziskTrace i
  | srli (c : Claim_srli ziskTrace i) : ZiskStep ziskTrace i
  | srai (c : Claim_srai ziskTrace i) : ZiskStep ziskTrace i
  | add (c : Claim_add ziskTrace i) : ZiskStep ziskTrace i
  | addi (c : Claim_addi ziskTrace i) : ZiskStep ziskTrace i
  | subw (c : Claim_subw ziskTrace i) : ZiskStep ziskTrace i
  | addw (c : Claim_addw ziskTrace i) : ZiskStep ziskTrace i
  | addiw (c : Claim_addiw ziskTrace i) : ZiskStep ziskTrace i
  | sllw (c : Claim_sllw ziskTrace i) : ZiskStep ziskTrace i
  | srlw (c : Claim_srlw ziskTrace i) : ZiskStep ziskTrace i
  | sraw (c : Claim_sraw ziskTrace i) : ZiskStep ziskTrace i
  | slliw (c : Claim_slliw ziskTrace i) : ZiskStep ziskTrace i
  | srliw (c : Claim_srliw ziskTrace i) : ZiskStep ziskTrace i
  | sraiw (c : Claim_sraiw ziskTrace i) : ZiskStep ziskTrace i
  | mul (c : Claim_mul ziskTrace i) : ZiskStep ziskTrace i
  | mulh (c : Claim_mulh ziskTrace i) : ZiskStep ziskTrace i
  | mulhsu (c : Claim_mulhsu ziskTrace i) : ZiskStep ziskTrace i
  | mulw (c : Claim_mulw ziskTrace i) : ZiskStep ziskTrace i
  | mulhu (c : Claim_mulhu ziskTrace i) : ZiskStep ziskTrace i
  | div (c : Claim_div ziskTrace i) : ZiskStep ziskTrace i
  | rem (c : Claim_rem ziskTrace i) : ZiskStep ziskTrace i
  | divw (c : Claim_divw ziskTrace i) : ZiskStep ziskTrace i
  | remw (c : Claim_remw ziskTrace i) : ZiskStep ziskTrace i
  | divu (c : Claim_divu ziskTrace i) : ZiskStep ziskTrace i
  | divuw (c : Claim_divuw ziskTrace i) : ZiskStep ziskTrace i
  | remu (c : Claim_remu ziskTrace i) : ZiskStep ziskTrace i
  | remuw (c : Claim_remuw ziskTrace i) : ZiskStep ziskTrace i
  | beq (c : Claim_beq ziskTrace i) : ZiskStep ziskTrace i
  | bne (c : Claim_bne ziskTrace i) : ZiskStep ziskTrace i
  | blt (c : Claim_blt ziskTrace i) : ZiskStep ziskTrace i
  | bge (c : Claim_bge ziskTrace i) : ZiskStep ziskTrace i
  | bltu (c : Claim_bltu ziskTrace i) : ZiskStep ziskTrace i
  | bgeu (c : Claim_bgeu ziskTrace i) : ZiskStep ziskTrace i
  | lui (c : Claim_lui ziskTrace i) : ZiskStep ziskTrace i
  | auipc (c : Claim_auipc ziskTrace i) : ZiskStep ziskTrace i
  | jal (c : Claim_jal ziskTrace i) : ZiskStep ziskTrace i
  | jalr (c : Claim_jalr ziskTrace i) : ZiskStep ziskTrace i
  | sb (c : Claim_sb ziskTrace i) : ZiskStep ziskTrace i
  | sh (c : Claim_sh ziskTrace i) : ZiskStep ziskTrace i
  | sw (c : Claim_sw ziskTrace i) : ZiskStep ziskTrace i
  | sd (c : Claim_sd ziskTrace i) : ZiskStep ziskTrace i
  | ld (c : Claim_ld ziskTrace i) : ZiskStep ziskTrace i
  | lbu (c : Claim_lbu ziskTrace i) : ZiskStep ziskTrace i
  | lhu (c : Claim_lhu ziskTrace i) : ZiskStep ziskTrace i
  | lwu (c : Claim_lwu ziskTrace i) : ZiskStep ziskTrace i
  | lb (c : Claim_lb ziskTrace i) : ZiskStep ziskTrace i
  | lh (c : Claim_lh ziskTrace i) : ZiskStep ziskTrace i
  | lw (c : Claim_lw ziskTrace i) : ZiskStep ziskTrace i
  | fence (c : Claim_fence ziskTrace i) : ZiskStep ziskTrace i

def RowDecode (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Type
  | .sub c => Decode_sub ziskTrace i c
  | .and c => Decode_and ziskTrace i c
  | .or c => Decode_or ziskTrace i c
  | .xor c => Decode_xor ziskTrace i c
  | .slt c => Decode_slt ziskTrace i c
  | .sltu c => Decode_sltu ziskTrace i c
  | .andi c => Decode_andi ziskTrace i c
  | .ori c => Decode_ori ziskTrace i c
  | .xori c => Decode_xori ziskTrace i c
  | .slti c => Decode_slti ziskTrace i c
  | .sltiu c => Decode_sltiu ziskTrace i c
  | .sll c => Decode_sll ziskTrace i c
  | .srl c => Decode_srl ziskTrace i c
  | .sra c => Decode_sra ziskTrace i c
  | .slli c => Decode_slli ziskTrace i c
  | .srli c => Decode_srli ziskTrace i c
  | .srai c => Decode_srai ziskTrace i c
  | .add c => Decode_add ziskTrace i c
  | .addi c => Decode_addi ziskTrace i c
  | .subw c => Decode_subw ziskTrace i c
  | .addw c => Decode_addw ziskTrace i c
  | .addiw c => Decode_addiw ziskTrace i c
  | .sllw c => Decode_sllw ziskTrace i c
  | .srlw c => Decode_srlw ziskTrace i c
  | .sraw c => Decode_sraw ziskTrace i c
  | .slliw c => Decode_slliw ziskTrace i c
  | .srliw c => Decode_srliw ziskTrace i c
  | .sraiw c => Decode_sraiw ziskTrace i c
  | .mul c => Decode_mul ziskTrace i c
  | .mulh c => Decode_mulh ziskTrace i c
  | .mulhsu c => Decode_mulhsu ziskTrace i c
  | .mulw c => Decode_mulw ziskTrace i c
  | .mulhu c => Decode_mulhu ziskTrace i c
  | .div c => Decode_div ziskTrace i c
  | .rem c => Decode_rem ziskTrace i c
  | .divw c => Decode_divw ziskTrace i c
  | .remw c => Decode_remw ziskTrace i c
  | .divu c => Decode_divu ziskTrace i c
  | .divuw c => Decode_divuw ziskTrace i c
  | .remu c => Decode_remu ziskTrace i c
  | .remuw c => Decode_remuw ziskTrace i c
  | .beq c => Decode_beq ziskTrace i c
  | .bne c => Decode_bne ziskTrace i c
  | .blt c => Decode_blt ziskTrace i c
  | .bge c => Decode_bge ziskTrace i c
  | .bltu c => Decode_bltu ziskTrace i c
  | .bgeu c => Decode_bgeu ziskTrace i c
  | .lui c => Decode_lui ziskTrace i c
  | .auipc c => Decode_auipc ziskTrace i c
  | .jal c => Decode_jal ziskTrace i c
  | .jalr c => Decode_jalr ziskTrace i c
  | .sb c => Decode_sb ziskTrace i c
  | .sh c => Decode_sh ziskTrace i c
  | .sw c => Decode_sw ziskTrace i c
  | .sd c => Decode_sd ziskTrace i c
  | .ld c => Decode_ld ziskTrace i c
  | .lbu c => Decode_lbu ziskTrace i c
  | .lhu c => Decode_lhu ziskTrace i c
  | .lwu c => Decode_lwu ziskTrace i c
  | .lb c => Decode_lb ziskTrace i c
  | .lh c => Decode_lh ziskTrace i c
  | .lw c => Decode_lw ziskTrace i c
  | .fence c => Decode_fence ziskTrace i c

def InputsAgree (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Type
  | .sub c => Inputs_sub ziskTrace sailTrace i c
  | .and c => Inputs_and ziskTrace sailTrace i c
  | .or c => Inputs_or ziskTrace sailTrace i c
  | .xor c => Inputs_xor ziskTrace sailTrace i c
  | .slt c => Inputs_slt ziskTrace sailTrace i c
  | .sltu c => Inputs_sltu ziskTrace sailTrace i c
  | .andi c => Inputs_andi ziskTrace sailTrace i c
  | .ori c => Inputs_ori ziskTrace sailTrace i c
  | .xori c => Inputs_xori ziskTrace sailTrace i c
  | .slti c => Inputs_slti ziskTrace sailTrace i c
  | .sltiu c => Inputs_sltiu ziskTrace sailTrace i c
  | .sll c => Inputs_sll ziskTrace sailTrace i c
  | .srl c => Inputs_srl ziskTrace sailTrace i c
  | .sra c => Inputs_sra ziskTrace sailTrace i c
  | .slli c => Inputs_slli ziskTrace sailTrace i c
  | .srli c => Inputs_srli ziskTrace sailTrace i c
  | .srai c => Inputs_srai ziskTrace sailTrace i c
  | .add c => Inputs_add ziskTrace sailTrace i c
  | .addi c => Inputs_addi ziskTrace sailTrace i c
  | .subw c => Inputs_subw ziskTrace sailTrace i c
  | .addw c => Inputs_addw ziskTrace sailTrace i c
  | .addiw c => Inputs_addiw ziskTrace sailTrace i c
  | .sllw c => Inputs_sllw ziskTrace sailTrace i c
  | .srlw c => Inputs_srlw ziskTrace sailTrace i c
  | .sraw c => Inputs_sraw ziskTrace sailTrace i c
  | .slliw c => Inputs_slliw ziskTrace sailTrace i c
  | .srliw c => Inputs_srliw ziskTrace sailTrace i c
  | .sraiw c => Inputs_sraiw ziskTrace sailTrace i c
  | .mul c => Inputs_mul ziskTrace sailTrace i c
  | .mulh c => Inputs_mulh ziskTrace sailTrace i c
  | .mulhsu c => Inputs_mulhsu ziskTrace sailTrace i c
  | .mulw c => Inputs_mulw ziskTrace sailTrace i c
  | .mulhu c => Inputs_mulhu ziskTrace sailTrace i c
  | .div c => Inputs_div ziskTrace sailTrace i c
  | .rem c => Inputs_rem ziskTrace sailTrace i c
  | .divw c => Inputs_divw ziskTrace sailTrace i c
  | .remw c => Inputs_remw ziskTrace sailTrace i c
  | .divu c => Inputs_divu ziskTrace sailTrace i c
  | .divuw c => Inputs_divuw ziskTrace sailTrace i c
  | .remu c => Inputs_remu ziskTrace sailTrace i c
  | .remuw c => Inputs_remuw ziskTrace sailTrace i c
  | .beq c => Inputs_beq ziskTrace sailTrace i c
  | .bne c => Inputs_bne ziskTrace sailTrace i c
  | .blt c => Inputs_blt ziskTrace sailTrace i c
  | .bge c => Inputs_bge ziskTrace sailTrace i c
  | .bltu c => Inputs_bltu ziskTrace sailTrace i c
  | .bgeu c => Inputs_bgeu ziskTrace sailTrace i c
  | .lui c => Inputs_lui ziskTrace sailTrace i c
  | .auipc c => Inputs_auipc ziskTrace sailTrace i c
  | .jal c => Inputs_jal ziskTrace sailTrace i c
  | .jalr c => Inputs_jalr ziskTrace sailTrace i c
  | .sb c => Inputs_sb ziskTrace sailTrace i c
  | .sh c => Inputs_sh ziskTrace sailTrace i c
  | .sw c => Inputs_sw ziskTrace sailTrace i c
  | .sd c => Inputs_sd ziskTrace sailTrace i c
  | .ld c => Inputs_ld ziskTrace sailTrace i c
  | .lbu c => Inputs_lbu ziskTrace sailTrace i c
  | .lhu c => Inputs_lhu ziskTrace sailTrace i c
  | .lwu c => Inputs_lwu ziskTrace sailTrace i c
  | .lb c => Inputs_lb ziskTrace sailTrace i c
  | .lh c => Inputs_lh ziskTrace sailTrace i c
  | .lw c => Inputs_lw ziskTrace sailTrace i c
  | .fence c => Inputs_fence ziskTrace sailTrace i c



/-- Per-row known-defect exclusion obligation, stated DIRECTLY over the row data
    (no `OpEnvelope` detour).

    The 8 defect-capable arms carry the genuine forge exclusion, read off the
    arith witness / claim fields that live in `ia` (the `inputsAgree` half) or in
    the matched `ZiskStep` claim payload:
      * MUL / MULH / MULHSU → `¬ SignedMulForge` of the ArithMul sign witnesses;
      * DIV / REM → `¬ DivRemForge` of the 64-bit remainder/divisor magnitudes;
      * DIVW / REMW → `¬ DivRemForgeW` of the 32-bit remainder/divisor magnitudes;
      * FENCE → `FenceKnownGood` of the claim's `fm` / `rs` / `rd`.
    Each is DEFINITIONALLY the same proposition as the corresponding `<op>EnvOf`
    `OpEnvelope` defect shape (the `Iff.rfl` bridge lemmas in `EnvOf`), so the
    re-expression off `OpEnvelope` carries no change of meaning.  Every other
    (non-defect) arm carries no defect obligation (`True`). -/
def RowOutsideDefectRegion (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (ia : InputsAgree ziskTrace sailTrace i zs) : Prop :=
  match zs, ia with
  | .mul _, ia => ¬ Defects.SignedMulForge ia.v ia.r_a
  | .mulh _, ia => ¬ Defects.SignedMulForge ia.v ia.r_a
  | .mulhsu _, ia => ¬ Defects.SignedMulForge ia.v ia.r_a
  | .div _, ia => ¬ Defects.DivRemForge ia.div_input.r2_val ia.v ia.r_a
  | .rem _, ia => ¬ Defects.DivRemForge ia.rem_input.r2_val ia.v ia.r_a
  | .divw _, ia => ¬ Defects.DivRemForgeW ia.divw_input.r2_val ia.v ia.r_a
  | .remw _, ia => ¬ Defects.DivRemForgeW ia.remw_input.r2_val ia.v ia.r_a
  | .fence c, _ => Defects.FenceKnownGood c.fm c.rs c.rd
  | _, _ => True

def StepSound
    (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions) (i : Fin ziskTrace.numInstructions) :
    ZiskStep ziskTrace i → Prop
  | .sub c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SUB))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .and c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.AND))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .or c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.OR))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .xor c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.XOR))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .slt c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLT))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sltu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLTU))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .andi c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.ANDI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .ori c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.ORI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .xori c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.XORI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .slti c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.SLTI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sltiu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.SLTIU))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sll c =>
      execute_instruction (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLL)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .srl c =>
      execute_instruction (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SRL)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sra c =>
      execute_instruction (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SRA)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .slli c =>
      execute_instruction (instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SLLI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .srli c =>
      execute_instruction (instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SRLI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .srai c =>
      execute_instruction (instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SRAI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .add c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.ADD))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .addi c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.ADDI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .subw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SUBW))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .addw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.ADDW))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .addiw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (c.imm, c.r1, c.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sllw c =>
      execute_instruction (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SLLW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .srlw c =>
      execute_instruction (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SRLW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sraw c =>
      execute_instruction (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SRAW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .slliw c =>
      execute_instruction
        (instruction.SHIFTIWOP (c.slliw_input.shamt, c.r1, c.rd, sopw.SLLIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .srliw c =>
      execute_instruction
        (instruction.SHIFTIWOP (c.srliw_input.shamt, c.r1, c.rd, sopw.SRLIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sraiw c =>
      execute_instruction
        (instruction.SHIFTIWOP (c.sraiw_input.shamt, c.r1, c.rd, sopw.SRAIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .mul c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (c.r2, c.r1, c.rd,
           { result_part := VectorHalf.Low
             signed_rs1 := c.srs1
             signed_rs2 := c.srs2 }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .mulh c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (c.r2, c.r1, c.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .mulhsu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (c.r2, c.r1, c.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .div c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .rem c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .divw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .remw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.bus.exec_row, [c.bus.e0, c.bus.e1, c.bus.e2]⟩ (sailTrace i)
  | .mulw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (c.r2, c.r1, c.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .mulhu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (c.r2, c.r1, c.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .divu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .divuw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .remu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .remuw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i c.execRow).exec_row,
           [(busSub ziskTrace i c.execRow).e0, (busSub ziskTrace i c.execRow).e1,
            (busSub ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .beq c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BEQ)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)
  | .bne c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BNE)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)
  | .blt c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BLT)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)
  | .bge c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BGE)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)
  | .bltu c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BLTU)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)
  | .bgeu c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BGEU)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)
  | .lui c =>
      execute_instruction (instruction.UTYPE (c.imm, c.rd, uop.LUI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.execRow, [eRdLui ziskTrace i]⟩ (sailTrace i)
  | .auipc c =>
      execute_instruction (instruction.UTYPE (c.imm, c.rd, uop.AUIPC)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.execRow, [eRdLui ziskTrace i]⟩ (sailTrace i)
  | .jal c =>
      execute_instruction (instruction.JAL (c.imm, c.rd)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.execRow, [eRdLui ziskTrace i]⟩ (sailTrace i)
  | .jalr c =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (c.imm, c.rs1, c.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨c.execRow, [eRdLui ziskTrace i]⟩ (sailTrace i)
  | .sb c =>
      execute_instruction (instruction.STORE
          (c.sb_input.imm, regidx.Regidx c.sb_input.r2, regidx.Regidx c.sb_input.r1, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i c.execRow).exec_row,
           [(busSt ziskTrace i c.execRow).e0, (busSt ziskTrace i c.execRow).e1,
            (busSt ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sh c =>
      execute_instruction (instruction.STORE
          (c.sh_input.imm, regidx.Regidx c.sh_input.r2, regidx.Regidx c.sh_input.r1, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i c.execRow).exec_row,
           [(busSt ziskTrace i c.execRow).e0, (busSt ziskTrace i c.execRow).e1,
            (busSt ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sw c =>
      execute_instruction (instruction.STORE
          (c.sw_input.imm, regidx.Regidx c.sw_input.r2, regidx.Regidx c.sw_input.r1, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i c.execRow).exec_row,
           [(busSt ziskTrace i c.execRow).e0, (busSt ziskTrace i c.execRow).e1,
            (busSt ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .sd c =>
      execute_instruction (instruction.STORE
          (c.sd_input.imm, regidx.Regidx c.sd_input.r2, regidx.Regidx c.sd_input.r1, 8))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i c.execRow).exec_row,
           [(busSt ziskTrace i c.execRow).e0, (busSt ziskTrace i c.execRow).e1,
            (busSt ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .ld c =>
      execute_instruction (instruction.LOAD
          (c.ld_input.imm, regidx.Regidx c.ld_input.r1, regidx.Regidx c.ld_input.rd, false, 8))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .lbu c =>
      execute_instruction (instruction.LOAD
          (c.lbu_input.imm, regidx.Regidx c.lbu_input.r1, regidx.Regidx c.lbu_input.rd, true, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .lhu c =>
      execute_instruction (instruction.LOAD
          (c.lhu_input.imm, regidx.Regidx c.lhu_input.r1, regidx.Regidx c.lhu_input.rd, true, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .lwu c =>
      execute_instruction (instruction.LOAD
          (c.lwu_input.imm, regidx.Regidx c.lwu_input.r1, regidx.Regidx c.lwu_input.rd, true, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .lb c =>
      execute_instruction (instruction.LOAD
          (c.lb_input.imm, regidx.Regidx c.lb_input.r1, regidx.Regidx c.lb_input.rd, false, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .lh c =>
      execute_instruction (instruction.LOAD
          (c.lh_input.imm, regidx.Regidx c.lh_input.r1, regidx.Regidx c.lh_input.rd, false, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .lw c =>
      execute_instruction (instruction.LOAD
          (c.lw_input.imm, regidx.Regidx c.lw_input.r1, regidx.Regidx c.lw_input.rd, false, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i c.execRow).exec_row,
           [(busLd ziskTrace i c.execRow).e0, (busLd ziskTrace i c.execRow).e1,
            (busLd ziskTrace i c.execRow).e2]⟩ (sailTrace i)
  | .fence c =>
      execute_instruction (instruction.FENCE (c.fm, c.fenceP, c.fenceS, c.rs, c.rd)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨c.exec_row, []⟩ (sailTrace i)

/-- Per-row dispatch to the matching strengthened step theorem.

    The `hAvoidKnownBugs` parameter carries the per-row defect-exclusion obligation
    (`RowOutsideDefectRegion`), stated directly over the row data.  For the 8
    defect-capable arms it is the row-data forge-negation / FENCE-known-good
    fact; the dispatcher hands it straight to the corresponding `stepStrong_<op>`,
    which assembles `NoKnownDefect (<op>EnvOf …)` from it (via
    `noKnownDefect_of_shapes`) and feeds that to
    `zisk_riscv_compliant_program_bus`.  For every other (non-defect) arm the
    obligation is `True` and is ignored — the arm builds its own `NoKnownDefect`. -/

theorem stepSound_of_evidence (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) (ia : InputsAgree ziskTrace sailTrace i zs)
    (hAvoidKnownBugs : RowOutsideDefectRegion ziskTrace sailTrace i zs ia) :
    StepSound ziskTrace sailTrace i zs := by
  cases zs with
  | sub c => exact stepStrong_sub ziskTrace sailTrace i (toRowData_sub c rd ia) hAvoidKnownBugs
  | and c => exact stepStrong_and ziskTrace sailTrace i (toRowData_and c rd ia) hAvoidKnownBugs
  | or c => exact stepStrong_or ziskTrace sailTrace i (toRowData_or c rd ia) hAvoidKnownBugs
  | xor c => exact stepStrong_xor ziskTrace sailTrace i (toRowData_xor c rd ia) hAvoidKnownBugs
  | slt c => exact stepStrong_slt ziskTrace sailTrace i (toRowData_slt c rd ia) hAvoidKnownBugs
  | sltu c => exact stepStrong_sltu ziskTrace sailTrace i (toRowData_sltu c rd ia) hAvoidKnownBugs
  | andi c => exact stepStrong_andi ziskTrace sailTrace i (toRowData_andi c rd ia) hAvoidKnownBugs
  | ori c => exact stepStrong_ori ziskTrace sailTrace i (toRowData_ori c rd ia) hAvoidKnownBugs
  | xori c => exact stepStrong_xori ziskTrace sailTrace i (toRowData_xori c rd ia) hAvoidKnownBugs
  | slti c => exact stepStrong_slti ziskTrace sailTrace i (toRowData_slti c rd ia) hAvoidKnownBugs
  | sltiu c => exact stepStrong_sltiu ziskTrace sailTrace i (toRowData_sltiu c rd ia) hAvoidKnownBugs
  | sll c => exact stepStrong_sll ziskTrace sailTrace i (toRowData_sll c rd ia) hAvoidKnownBugs
  | srl c => exact stepStrong_srl ziskTrace sailTrace i (toRowData_srl c rd ia) hAvoidKnownBugs
  | sra c => exact stepStrong_sra ziskTrace sailTrace i (toRowData_sra c rd ia) hAvoidKnownBugs
  | slli c => exact stepStrong_slli ziskTrace sailTrace i (toRowData_slli c rd ia) hAvoidKnownBugs
  | srli c => exact stepStrong_srli ziskTrace sailTrace i (toRowData_srli c rd ia) hAvoidKnownBugs
  | srai c => exact stepStrong_srai ziskTrace sailTrace i (toRowData_srai c rd ia) hAvoidKnownBugs
  | add c => exact stepStrong_add ziskTrace sailTrace i (toRowData_add c rd ia) hAvoidKnownBugs
  | addi c => exact stepStrong_addi ziskTrace sailTrace i (toRowData_addi c rd ia) hAvoidKnownBugs
  | subw c => exact stepStrong_subw ziskTrace sailTrace i (toRowData_subw c rd ia) hAvoidKnownBugs
  | addw c => exact stepStrong_addw ziskTrace sailTrace i (toRowData_addw c rd ia) hAvoidKnownBugs
  | addiw c => exact stepStrong_addiw ziskTrace sailTrace i (toRowData_addiw c rd ia) hAvoidKnownBugs
  | sllw c => exact stepStrong_sllw ziskTrace sailTrace i (toRowData_sllw c rd ia) hAvoidKnownBugs
  | srlw c => exact stepStrong_srlw ziskTrace sailTrace i (toRowData_srlw c rd ia) hAvoidKnownBugs
  | sraw c => exact stepStrong_sraw ziskTrace sailTrace i (toRowData_sraw c rd ia) hAvoidKnownBugs
  | slliw c => exact stepStrong_slliw ziskTrace sailTrace i (toRowData_slliw c rd ia) hAvoidKnownBugs
  | srliw c => exact stepStrong_srliw ziskTrace sailTrace i (toRowData_srliw c rd ia) hAvoidKnownBugs
  | sraiw c => exact stepStrong_sraiw ziskTrace sailTrace i (toRowData_sraiw c rd ia) hAvoidKnownBugs
  | mul c => exact stepStrong_mul ziskTrace sailTrace i (toRowData_mul c rd ia) hAvoidKnownBugs
  | mulh c => exact stepStrong_mulh ziskTrace sailTrace i (toRowData_mulh c rd ia) hAvoidKnownBugs
  | mulhsu c => exact stepStrong_mulhsu ziskTrace sailTrace i (toRowData_mulhsu c rd ia) hAvoidKnownBugs
  | mulw c => exact stepStrong_mulw ziskTrace sailTrace i (toRowData_mulw c rd ia) hAvoidKnownBugs
  | mulhu c => exact stepStrong_mulhu ziskTrace sailTrace i (toRowData_mulhu c rd ia) hAvoidKnownBugs
  | div c => exact stepStrong_div ziskTrace sailTrace i (toRowData_div c rd ia) hAvoidKnownBugs
  | rem c => exact stepStrong_rem ziskTrace sailTrace i (toRowData_rem c rd ia) hAvoidKnownBugs
  | divw c => exact stepStrong_divw ziskTrace sailTrace i (toRowData_divw c rd ia) hAvoidKnownBugs
  | remw c => exact stepStrong_remw ziskTrace sailTrace i (toRowData_remw c rd ia) hAvoidKnownBugs
  | divu c => exact stepStrong_divu ziskTrace sailTrace i (toRowData_divu c rd ia) hAvoidKnownBugs
  | divuw c => exact stepStrong_divuw ziskTrace sailTrace i (toRowData_divuw c rd ia) hAvoidKnownBugs
  | remu c => exact stepStrong_remu ziskTrace sailTrace i (toRowData_remu c rd ia) hAvoidKnownBugs
  | remuw c => exact stepStrong_remuw ziskTrace sailTrace i (toRowData_remuw c rd ia) hAvoidKnownBugs
  | beq c => exact stepStrong_beq ziskTrace sailTrace i (toRowData_beq c rd ia) hAvoidKnownBugs
  | bne c => exact stepStrong_bne ziskTrace sailTrace i (toRowData_bne c rd ia) hAvoidKnownBugs
  | blt c => exact stepStrong_blt ziskTrace sailTrace i (toRowData_blt c rd ia) hAvoidKnownBugs
  | bge c => exact stepStrong_bge ziskTrace sailTrace i (toRowData_bge c rd ia) hAvoidKnownBugs
  | bltu c => exact stepStrong_bltu ziskTrace sailTrace i (toRowData_bltu c rd ia) hAvoidKnownBugs
  | bgeu c => exact stepStrong_bgeu ziskTrace sailTrace i (toRowData_bgeu c rd ia) hAvoidKnownBugs
  | lui c => exact stepStrong_lui ziskTrace sailTrace i (toRowData_lui c rd ia) hAvoidKnownBugs
  | auipc c => exact stepStrong_auipc ziskTrace sailTrace i (toRowData_auipc c rd ia) hAvoidKnownBugs
  | jal c => exact stepStrong_jal ziskTrace sailTrace i (toRowData_jal c rd ia) hAvoidKnownBugs
  | jalr c => exact stepStrong_jalr ziskTrace sailTrace i (toRowData_jalr c rd ia) hAvoidKnownBugs
  | sb c => exact stepStrong_sb ziskTrace sailTrace i (toRowData_sb c rd ia) hAvoidKnownBugs
  | sh c => exact stepStrong_sh ziskTrace sailTrace i (toRowData_sh c rd ia) hAvoidKnownBugs
  | sw c => exact stepStrong_sw ziskTrace sailTrace i (toRowData_sw c rd ia) hAvoidKnownBugs
  | sd c => exact stepStrong_sd ziskTrace sailTrace i (toRowData_sd c rd ia) hAvoidKnownBugs
  | ld c => exact stepStrong_ld ziskTrace sailTrace i (toRowData_ld c rd ia) hAvoidKnownBugs
  | lbu c => exact stepStrong_lbu ziskTrace sailTrace i (toRowData_lbu c rd ia) hAvoidKnownBugs
  | lhu c => exact stepStrong_lhu ziskTrace sailTrace i (toRowData_lhu c rd ia) hAvoidKnownBugs
  | lwu c => exact stepStrong_lwu ziskTrace sailTrace i (toRowData_lwu c rd ia) hAvoidKnownBugs
  | lb c => exact stepStrong_lb ziskTrace sailTrace i (toRowData_lb c rd ia) hAvoidKnownBugs
  | lh c => exact stepStrong_lh ziskTrace sailTrace i (toRowData_lh c rd ia) hAvoidKnownBugs
  | lw c => exact stepStrong_lw ziskTrace sailTrace i (toRowData_lw c rd ia) hAvoidKnownBugs
  | fence c => exact stepStrong_fence ziskTrace sailTrace i (toRowData_fence c rd ia) hAvoidKnownBugs

end ZiskFv.Compliance
