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

/-- A per-row classification carrying the honest residual binders for ALL 63 RV64IM
    arms, each strengthened to the channel-balance / env-constructed form.  Three
    routes feed the identical channel-balance proposition: the 22 op-bus ALU arms via
    the env-constructed route; the control-flow / U-type / store / load /
    M-ext-unsigned arms via the direct-lift route; and the 7 signed-M arms
    (MUL/MULH/MULHSU/DIV/REM/DIVW/REMW) plus FENCE via the env-constructed route with
    a GENUINE per-row `NoKnownDefect` obligation whose defect predicate is narrowed to
    the exact forge witness (so honest rows are never excluded).  No arm is omitted —
    the export is 63/63 on the OpEnvelope route. -/

inductive StrongRowConstructionData
    (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions) (i : Fin ziskTrace.numInstructions) where
  | sub (d : RowData_sub ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | and (d : RowData_and ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | or (d : RowData_or ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | xor (d : RowData_xor ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | slt (d : RowData_slt ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sltu (d : RowData_sltu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | andi (d : RowData_andi ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | ori (d : RowData_ori ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | xori (d : RowData_xori ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | slti (d : RowData_slti ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sltiu (d : RowData_sltiu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sll (d : RowData_sll ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | srl (d : RowData_srl ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sra (d : RowData_sra ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | slli (d : RowData_slli ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | srli (d : RowData_srli ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | srai (d : RowData_srai ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | add (d : RowData_add ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | addi (d : RowData_addi ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | subw (d : RowData_subw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | addw (d : RowData_addw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | addiw (d : RowData_addiw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sllw (d : RowData_sllw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | srlw (d : RowData_srlw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sraw (d : RowData_sraw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | slliw (d : RowData_slliw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | srliw (d : RowData_srliw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sraiw (d : RowData_sraiw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | mul (d : RowData_mul ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | mulh (d : RowData_mulh ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | mulhsu (d : RowData_mulhsu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | mulw (d : RowData_mulw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | mulhu (d : RowData_mulhu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | div (d : RowData_div ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | rem (d : RowData_rem ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | divw (d : RowData_divw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | remw (d : RowData_remw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | divu (d : RowData_divu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | divuw (d : RowData_divuw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | remu (d : RowData_remu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | remuw (d : RowData_remuw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | beq (d : RowData_beq ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | bne (d : RowData_bne ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | blt (d : RowData_blt ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | bge (d : RowData_bge ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | bltu (d : RowData_bltu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | bgeu (d : RowData_bgeu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lui (d : RowData_lui ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | auipc (d : RowData_auipc ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | jal (d : RowData_jal ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | jalr (d : RowData_jalr ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sb (d : RowData_sb ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sh (d : RowData_sh ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sw (d : RowData_sw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | sd (d : RowData_sd ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | ld (d : RowData_ld ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lbu (d : RowData_lbu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lhu (d : RowData_lhu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lwu (d : RowData_lwu ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lb (d : RowData_lb ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lh (d : RowData_lh ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | lw (d : RowData_lw ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i
  | fence (d : RowData_fence ziskTrace sailTrace i) : StrongRowConstructionData ziskTrace sailTrace i

/-- Per-row defect-exclusion obligation supplied to (and threaded into) the
    strengthened ziskTrace-level export.  For each OpEnvelope-route arm it is the
    `EnvNoKnownDefectFor` fact restricted to that arm's `OpEnvelope` constructor;
    for the direct-lift arms (which never invoke `zisk_riscv_compliant_program_bus`)
    it is `True`.  See `EnvNoKnownDefectFor` for the non-vacuity / generalization
    rationale.

    The `fence` arm is the EXCEPTION to the `EnvNoKnownDefectFor` selector-∀ shape:
    that shape (`∀ env, sel env → NoKnownDefect env`) is FALSE for FENCE (a
    malicious `fm≠0` FENCE matches the `.fence` selector but is NOT `NoKnownDefect`),
    so the fence arm instead asks for the GENUINE `NoKnownDefect` of the SPECIFIC
    honest `OpEnvelope.fence` env built from the row's honest-shape pins.  That
    obligation is SATISFIABLE for an honest FENCE row (see `RowData_fence` /
    `stepStrong_fence`). -/

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

def toFull (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) (ia : InputsAgree ziskTrace sailTrace i zs) :
    StrongRowConstructionData ziskTrace sailTrace i :=
  match zs, rd, ia with
  | .sub c, rd, ia => .sub (toRowData_sub c rd ia)
  | .and c, rd, ia => .and (toRowData_and c rd ia)
  | .or c, rd, ia => .or (toRowData_or c rd ia)
  | .xor c, rd, ia => .xor (toRowData_xor c rd ia)
  | .slt c, rd, ia => .slt (toRowData_slt c rd ia)
  | .sltu c, rd, ia => .sltu (toRowData_sltu c rd ia)
  | .andi c, rd, ia => .andi (toRowData_andi c rd ia)
  | .ori c, rd, ia => .ori (toRowData_ori c rd ia)
  | .xori c, rd, ia => .xori (toRowData_xori c rd ia)
  | .slti c, rd, ia => .slti (toRowData_slti c rd ia)
  | .sltiu c, rd, ia => .sltiu (toRowData_sltiu c rd ia)
  | .sll c, rd, ia => .sll (toRowData_sll c rd ia)
  | .srl c, rd, ia => .srl (toRowData_srl c rd ia)
  | .sra c, rd, ia => .sra (toRowData_sra c rd ia)
  | .slli c, rd, ia => .slli (toRowData_slli c rd ia)
  | .srli c, rd, ia => .srli (toRowData_srli c rd ia)
  | .srai c, rd, ia => .srai (toRowData_srai c rd ia)
  | .add c, rd, ia => .add (toRowData_add c rd ia)
  | .addi c, rd, ia => .addi (toRowData_addi c rd ia)
  | .subw c, rd, ia => .subw (toRowData_subw c rd ia)
  | .addw c, rd, ia => .addw (toRowData_addw c rd ia)
  | .addiw c, rd, ia => .addiw (toRowData_addiw c rd ia)
  | .sllw c, rd, ia => .sllw (toRowData_sllw c rd ia)
  | .srlw c, rd, ia => .srlw (toRowData_srlw c rd ia)
  | .sraw c, rd, ia => .sraw (toRowData_sraw c rd ia)
  | .slliw c, rd, ia => .slliw (toRowData_slliw c rd ia)
  | .srliw c, rd, ia => .srliw (toRowData_srliw c rd ia)
  | .sraiw c, rd, ia => .sraiw (toRowData_sraiw c rd ia)
  | .mul c, rd, ia => .mul (toRowData_mul c rd ia)
  | .mulh c, rd, ia => .mulh (toRowData_mulh c rd ia)
  | .mulhsu c, rd, ia => .mulhsu (toRowData_mulhsu c rd ia)
  | .mulw c, rd, ia => .mulw (toRowData_mulw c rd ia)
  | .mulhu c, rd, ia => .mulhu (toRowData_mulhu c rd ia)
  | .div c, rd, ia => .div (toRowData_div c rd ia)
  | .rem c, rd, ia => .rem (toRowData_rem c rd ia)
  | .divw c, rd, ia => .divw (toRowData_divw c rd ia)
  | .remw c, rd, ia => .remw (toRowData_remw c rd ia)
  | .divu c, rd, ia => .divu (toRowData_divu c rd ia)
  | .divuw c, rd, ia => .divuw (toRowData_divuw c rd ia)
  | .remu c, rd, ia => .remu (toRowData_remu c rd ia)
  | .remuw c, rd, ia => .remuw (toRowData_remuw c rd ia)
  | .beq c, rd, ia => .beq (toRowData_beq c rd ia)
  | .bne c, rd, ia => .bne (toRowData_bne c rd ia)
  | .blt c, rd, ia => .blt (toRowData_blt c rd ia)
  | .bge c, rd, ia => .bge (toRowData_bge c rd ia)
  | .bltu c, rd, ia => .bltu (toRowData_bltu c rd ia)
  | .bgeu c, rd, ia => .bgeu (toRowData_bgeu c rd ia)
  | .lui c, rd, ia => .lui (toRowData_lui c rd ia)
  | .auipc c, rd, ia => .auipc (toRowData_auipc c rd ia)
  | .jal c, rd, ia => .jal (toRowData_jal c rd ia)
  | .jalr c, rd, ia => .jalr (toRowData_jalr c rd ia)
  | .sb c, rd, ia => .sb (toRowData_sb c rd ia)
  | .sh c, rd, ia => .sh (toRowData_sh c rd ia)
  | .sw c, rd, ia => .sw (toRowData_sw c rd ia)
  | .sd c, rd, ia => .sd (toRowData_sd c rd ia)
  | .ld c, rd, ia => .ld (toRowData_ld c rd ia)
  | .lbu c, rd, ia => .lbu (toRowData_lbu c rd ia)
  | .lhu c, rd, ia => .lhu (toRowData_lhu c rd ia)
  | .lwu c, rd, ia => .lwu (toRowData_lwu c rd ia)
  | .lb c, rd, ia => .lb (toRowData_lb c rd ia)
  | .lh c, rd, ia => .lh (toRowData_lh c rd ia)
  | .lw c, rd, ia => .lw (toRowData_lw c rd ia)
  | .fence c, rd, ia => .fence (toRowData_fence c rd ia)

def StepNoKnownDefectOn
    (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions) (i : Fin ziskTrace.numInstructions) :
    StrongRowConstructionData ziskTrace sailTrace i → Prop
  | .sub _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sub .. => True | _ => False)
  | .and _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .and .. => True | _ => False)
  | .or _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .or .. => True | _ => False)
  | .xor _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .xor .. => True | _ => False)
  | .slt _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .slt .. => True | _ => False)
  | .sltu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sltu .. => True | _ => False)
  | .andi _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .andi .. => True | _ => False)
  | .ori _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .ori .. => True | _ => False)
  | .xori _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .xori .. => True | _ => False)
  | .slti _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .slti .. => True | _ => False)
  | .sltiu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sltiu .. => True | _ => False)
  | .sll _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sll .. => True | _ => False)
  | .srl _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .srl .. => True | _ => False)
  | .sra _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sra .. => True | _ => False)
  | .slli _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .slli .. => True | _ => False)
  | .srli _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .srli .. => True | _ => False)
  | .srai _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .srai .. => True | _ => False)
  | .add _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val)
      (fun env => match env with | .add_via_binary .. => True | .add_via_binaryadd .. => True | _ => False)
  | .addi _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val)
      (fun env => match env with | .addi_via_binary .. => True | .addi_via_binaryadd .. => True | _ => False)
  | .subw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .subw .. => True | _ => False)
  | .addw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .addw .. => True | _ => False)
  | .addiw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .addiw .. => True | _ => False)
  | .sllw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sllw .. => True | _ => False)
  | .srlw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .srlw .. => True | _ => False)
  | .sraw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sraw .. => True | _ => False)
  | .slliw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .slliw .. => True | _ => False)
  | .srliw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .srliw .. => True | _ => False)
  | .sraiw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sraiw .. => True | _ => False)
  | .jalr _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .jalr .. => True | _ => False)
  | .beq _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .beq .. => True | _ => False)
  | .bne _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .bne .. => True | _ => False)
  | .blt _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .blt .. => True | _ => False)
  | .bge _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .bge .. => True | _ => False)
  | .bltu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .bltu .. => True | _ => False)
  | .bgeu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .bgeu .. => True | _ => False)
  | .mul d => Defects.NoKnownDefect (mulEnvOf ziskTrace sailTrace i d)
  | .mulh d => Defects.NoKnownDefect (mulhEnvOf ziskTrace sailTrace i d)
  | .mulhsu d => Defects.NoKnownDefect (mulhsuEnvOf ziskTrace sailTrace i d)
  -- Signed DIV/REM/DIVW/REMW: the GENUINE `NoKnownDefect` of the SPECIFIC env,
  -- NOT the (false) selector-∀ shape.  Satisfiable for an honest signed row
  -- (`|r| ≠ |op2|`); see `RowData_div` / `stepStrong_div`.
  | .div d => Defects.NoKnownDefect (divEnvOf ziskTrace sailTrace i d)
  | .rem d => Defects.NoKnownDefect (remEnvOf ziskTrace sailTrace i d)
  | .divw d => Defects.NoKnownDefect (divwEnvOf ziskTrace sailTrace i d)
  | .remw d => Defects.NoKnownDefect (remwEnvOf ziskTrace sailTrace i d)
  | .mulw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .mulw .. => True | _ => False)
  | .mulhu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .mulhu .. => True | _ => False)
  | .divu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .divu .. => True | _ => False)
  | .divuw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .divuw .. => True | _ => False)
  | .remu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .remu .. => True | _ => False)
  | .remuw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .remuw .. => True | _ => False)
  | .lui _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .lui .. => True | _ => False)
  | .auipc _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .auipc .. => True | _ => False)
  | .jal _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .jal .. => True | _ => False)
  | .sb _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sb .. => True | _ => False)
  | .sh _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sh .. => True | _ => False)
  | .sw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sw .. => True | _ => False)
  | .sd _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .sd .. => True | _ => False)
  | .ld _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .ld .. => True | _ => False)
  | .lbu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .lbu .. => True | _ => False)
  | .lhu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .lhu .. => True | _ => False)
  | .lwu _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val) (fun env => match env with | .lwu .. => True | _ => False)
  | .lb _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val)
      (fun env => match env with | .lb_via_static_match .. => True | _ => False)
  | .lh _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val)
      (fun env => match env with | .lh_via_static_match .. => True | _ => False)
  | .lw _ => EnvNoKnownDefectFor
      (state := sailTrace i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable)
      (r := i.val)
      (fun env => match env with | .lw_via_static_match .. => True | _ => False)
  -- FENCE: the GENUINE `NoKnownDefect` of the SPECIFIC honest env, NOT the
  -- (false) selector-∀ shape.  Satisfiable for an honest FENCE row.
  | .fence d => Defects.NoKnownDefect (fenceEnvOf ziskTrace sailTrace i d)

/-- The strengthened per-step conclusion: the channel-balance
    (`state_effect_via_channels`) form — the OLD global theorem's per-arm
    conclusion — keyed on the row archetype. -/

def StepNoKnownDefect (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) (ia : InputsAgree ziskTrace sailTrace i zs) : Prop :=
  StepNoKnownDefectOn ziskTrace sailTrace i (toFull ziskTrace sailTrace i zs rd ia)

def StepFaithful
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

    The `h_known` parameter carries the per-row defect-exclusion obligation
    (`StepNoKnownDefect`).  For the 22 OpEnvelope-route arms it is the
    `EnvNoKnownDefectFor` fact for that arm's constructor; the dispatcher hands it
    straight to the corresponding `stepStrong_<op>`, which feeds it to
    `zisk_riscv_compliant_program_bus`.  For the direct-lift arms (which never call
    the old theorem) the obligation is `True` and is ignored. -/

theorem stepFaithful_of_evidence (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) (ia : InputsAgree ziskTrace sailTrace i zs)
    (h_known : StepNoKnownDefect ziskTrace sailTrace i zs rd ia) :
    StepFaithful ziskTrace sailTrace i zs := by
  cases zs with
  | sub c => exact stepStrong_sub ziskTrace sailTrace i (toRowData_sub c rd ia) h_known
  | and c => exact stepStrong_and ziskTrace sailTrace i (toRowData_and c rd ia) h_known
  | or c => exact stepStrong_or ziskTrace sailTrace i (toRowData_or c rd ia) h_known
  | xor c => exact stepStrong_xor ziskTrace sailTrace i (toRowData_xor c rd ia) h_known
  | slt c => exact stepStrong_slt ziskTrace sailTrace i (toRowData_slt c rd ia) h_known
  | sltu c => exact stepStrong_sltu ziskTrace sailTrace i (toRowData_sltu c rd ia) h_known
  | andi c => exact stepStrong_andi ziskTrace sailTrace i (toRowData_andi c rd ia) h_known
  | ori c => exact stepStrong_ori ziskTrace sailTrace i (toRowData_ori c rd ia) h_known
  | xori c => exact stepStrong_xori ziskTrace sailTrace i (toRowData_xori c rd ia) h_known
  | slti c => exact stepStrong_slti ziskTrace sailTrace i (toRowData_slti c rd ia) h_known
  | sltiu c => exact stepStrong_sltiu ziskTrace sailTrace i (toRowData_sltiu c rd ia) h_known
  | sll c => exact stepStrong_sll ziskTrace sailTrace i (toRowData_sll c rd ia) h_known
  | srl c => exact stepStrong_srl ziskTrace sailTrace i (toRowData_srl c rd ia) h_known
  | sra c => exact stepStrong_sra ziskTrace sailTrace i (toRowData_sra c rd ia) h_known
  | slli c => exact stepStrong_slli ziskTrace sailTrace i (toRowData_slli c rd ia) h_known
  | srli c => exact stepStrong_srli ziskTrace sailTrace i (toRowData_srli c rd ia) h_known
  | srai c => exact stepStrong_srai ziskTrace sailTrace i (toRowData_srai c rd ia) h_known
  | add c => exact stepStrong_add ziskTrace sailTrace i (toRowData_add c rd ia) h_known
  | addi c => exact stepStrong_addi ziskTrace sailTrace i (toRowData_addi c rd ia) h_known
  | subw c => exact stepStrong_subw ziskTrace sailTrace i (toRowData_subw c rd ia) h_known
  | addw c => exact stepStrong_addw ziskTrace sailTrace i (toRowData_addw c rd ia) h_known
  | addiw c => exact stepStrong_addiw ziskTrace sailTrace i (toRowData_addiw c rd ia) h_known
  | sllw c => exact stepStrong_sllw ziskTrace sailTrace i (toRowData_sllw c rd ia) h_known
  | srlw c => exact stepStrong_srlw ziskTrace sailTrace i (toRowData_srlw c rd ia) h_known
  | sraw c => exact stepStrong_sraw ziskTrace sailTrace i (toRowData_sraw c rd ia) h_known
  | slliw c => exact stepStrong_slliw ziskTrace sailTrace i (toRowData_slliw c rd ia) h_known
  | srliw c => exact stepStrong_srliw ziskTrace sailTrace i (toRowData_srliw c rd ia) h_known
  | sraiw c => exact stepStrong_sraiw ziskTrace sailTrace i (toRowData_sraiw c rd ia) h_known
  | mul c => exact stepStrong_mul ziskTrace sailTrace i (toRowData_mul c rd ia) h_known
  | mulh c => exact stepStrong_mulh ziskTrace sailTrace i (toRowData_mulh c rd ia) h_known
  | mulhsu c => exact stepStrong_mulhsu ziskTrace sailTrace i (toRowData_mulhsu c rd ia) h_known
  | mulw c => exact stepStrong_mulw ziskTrace sailTrace i (toRowData_mulw c rd ia) h_known
  | mulhu c => exact stepStrong_mulhu ziskTrace sailTrace i (toRowData_mulhu c rd ia) h_known
  | div c => exact stepStrong_div ziskTrace sailTrace i (toRowData_div c rd ia) h_known
  | rem c => exact stepStrong_rem ziskTrace sailTrace i (toRowData_rem c rd ia) h_known
  | divw c => exact stepStrong_divw ziskTrace sailTrace i (toRowData_divw c rd ia) h_known
  | remw c => exact stepStrong_remw ziskTrace sailTrace i (toRowData_remw c rd ia) h_known
  | divu c => exact stepStrong_divu ziskTrace sailTrace i (toRowData_divu c rd ia) h_known
  | divuw c => exact stepStrong_divuw ziskTrace sailTrace i (toRowData_divuw c rd ia) h_known
  | remu c => exact stepStrong_remu ziskTrace sailTrace i (toRowData_remu c rd ia) h_known
  | remuw c => exact stepStrong_remuw ziskTrace sailTrace i (toRowData_remuw c rd ia) h_known
  | beq c => exact stepStrong_beq ziskTrace sailTrace i (toRowData_beq c rd ia) h_known
  | bne c => exact stepStrong_bne ziskTrace sailTrace i (toRowData_bne c rd ia) h_known
  | blt c => exact stepStrong_blt ziskTrace sailTrace i (toRowData_blt c rd ia) h_known
  | bge c => exact stepStrong_bge ziskTrace sailTrace i (toRowData_bge c rd ia) h_known
  | bltu c => exact stepStrong_bltu ziskTrace sailTrace i (toRowData_bltu c rd ia) h_known
  | bgeu c => exact stepStrong_bgeu ziskTrace sailTrace i (toRowData_bgeu c rd ia) h_known
  | lui c => exact stepStrong_lui ziskTrace sailTrace i (toRowData_lui c rd ia) h_known
  | auipc c => exact stepStrong_auipc ziskTrace sailTrace i (toRowData_auipc c rd ia) h_known
  | jal c => exact stepStrong_jal ziskTrace sailTrace i (toRowData_jal c rd ia) h_known
  | jalr c => exact stepStrong_jalr ziskTrace sailTrace i (toRowData_jalr c rd ia) h_known
  | sb c => exact stepStrong_sb ziskTrace sailTrace i (toRowData_sb c rd ia) h_known
  | sh c => exact stepStrong_sh ziskTrace sailTrace i (toRowData_sh c rd ia) h_known
  | sw c => exact stepStrong_sw ziskTrace sailTrace i (toRowData_sw c rd ia) h_known
  | sd c => exact stepStrong_sd ziskTrace sailTrace i (toRowData_sd c rd ia) h_known
  | ld c => exact stepStrong_ld ziskTrace sailTrace i (toRowData_ld c rd ia) h_known
  | lbu c => exact stepStrong_lbu ziskTrace sailTrace i (toRowData_lbu c rd ia) h_known
  | lhu c => exact stepStrong_lhu ziskTrace sailTrace i (toRowData_lhu c rd ia) h_known
  | lwu c => exact stepStrong_lwu ziskTrace sailTrace i (toRowData_lwu c rd ia) h_known
  | lb c => exact stepStrong_lb ziskTrace sailTrace i (toRowData_lb c rd ia) h_known
  | lh c => exact stepStrong_lh ziskTrace sailTrace i (toRowData_lh c rd ia) h_known
  | lw c => exact stepStrong_lw ziskTrace sailTrace i (toRowData_lw c rd ia) h_known
  | fence c => exact stepStrong_fence ziskTrace sailTrace i (toRowData_fence c rd ia) h_known

end ZiskFv.Compliance
