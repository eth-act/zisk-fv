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
open Air.Flat

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

/-- The per-op memory-coherence residual each memory `stepStrong_<op>` core
    consumes, dispatched by op-kind: the load memory-timeline evidence for the
    seven loads, the sub-doubleword RMW evidence for `sb`/`sh`/`sw`, and `True`
    for every non-memory op (and `sd`, a full-doubleword store that overwrites the
    whole lane).  A single seed-derived value of this type is threaded through
    `stepSound_of_evidence` in place of the ten former per-op `Inputs_<op>` memory
    fields — see `BootSegmentMemorySeed` / `memEvidence_of_bootSeed`. -/
def MemoryOpEvidenceFor
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ =>
      LoadMemoryTimelineCoherenceEvidence (sailTrace i)
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .sb _ =>
      StoreRmwMemoryCoherenceEvidence (sailTrace i)
        (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 1
  | .sh _ =>
      StoreRmwMemoryCoherenceEvidence (sailTrace i)
        (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 2
  | .sw _ =>
      StoreRmwMemoryCoherenceEvidence (sailTrace i)
        (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 4
  | _ => True



/-- Per-row known-defect exclusion obligation, stated over the accepted ZisK row
    only (no `OpEnvelope`, `SailTrace`, or `InputsAgree` detour).

    The defect-capable arith arms quantify over arith witness rows whose
    operation-bus entry matches the accepted Main row:
      * MUL uses the primary ArithMul lane;
      * MULH / MULHSU use the secondary ArithMul lane;
      * DIV / DIVW use the primary ArithDiv lane;
      * REM / REMW use the secondary ArithDiv lane.

    DIV/REM divisor operands are tied to the witness chunks via
    `Defects.signedDivisorInt` / `Defects.signedDivisorIntW`, so the defect gate
    no longer reads Sail operand values from `Inputs_<op>`.  The dispatcher later
    instantiates this trace-local predicate with the arith row already present in
    the existing step evidence; the predicate itself is independent of that
    evidence.

    The sequential, branch, and jump-like arms also carry their theorem-domain
    range assumptions, but phrased over trace-local row facts.  The dispatcher
    later bridges them to the matching `Inputs_<op>` PC through the per-op
    `h_pc_bridge` fields; this keeps `InputsAgree` out of the residual while
    preserving the explicit domain obligations from the step theorems. -/

noncomputable def mainPcVal (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Nat :=
  ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val

def MainSequentialPcDomain (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Prop :=
  mainPcVal ziskTrace i < GL_prime - 4

def MainBranchRangeDomain (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) (takenOffset : BitVec 64) : Prop :=
  0 ≤ (mainPcVal ziskTrace i : Int) + takenOffset.toInt ∧
    (mainPcVal ziskTrace i : Int) + takenOffset.toInt < GL_prime ∧
    MainSequentialPcDomain ziskTrace i

structure MainAuipcRangeDomain (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) (imm : BitVec 20) : Prop where
  h_pc_bound : MainSequentialPcDomain ziskTrace i
  h_target_nonneg :
    0 ≤ (mainPcVal ziskTrace i : Int)
      + (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toInt
  h_target_lt :
    (mainPcVal ziskTrace i : Int)
      + (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toInt < GL_prime
  h_pc_offset_lt_2_32 :
    ∀ pc : BitVec 64, mainPcVal ziskTrace i = pc.toNat →
      (pc + BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat < 4294967296

structure MainJalRangeDomain (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) (imm : BitVec 21) : Prop where
  h_target_nonneg :
    0 ≤ (mainPcVal ziskTrace i : Int) + (BitVec.signExtend 64 imm).toInt
  h_target_lt :
    (mainPcVal ziskTrace i : Int) + (BitVec.signExtend 64 imm).toInt < GL_prime
  h_pc_bound : MainSequentialPcDomain ziskTrace i
  h_pc_offset_lt_2_32 :
    ∀ pc : BitVec 64, mainPcVal ziskTrace i = pc.toNat →
      (pc + 4#64).toNat < 4294967296

structure MainJalrRangeDomain (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Prop where
  h_pc_bound : MainSequentialPcDomain ziskTrace i
  h_pc_offset_lt_2_32 :
    ∀ pc : BitVec 64, mainPcVal ziskTrace i = pc.toNat →
      (pc + 4#64).toNat < 4294967296

theorem sequentialPcDomain_of_main
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions} {pc : BitVec 64}
    (h_bridge : mainPcVal ziskTrace i = pc.toNat)
    (h_domain : MainSequentialPcDomain ziskTrace i) :
    SequentialPcDomain pc := by
  unfold SequentialPcDomain
  rw [← h_bridge]
  simpa [MainSequentialPcDomain] using h_domain

theorem branchRangeDomain_of_main
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions} {pc takenOffset : BitVec 64}
    (h_bridge : mainPcVal ziskTrace i = pc.toNat)
    (h_domain : MainBranchRangeDomain ziskTrace i takenOffset) :
    BranchRangeDomain ziskTrace i pc takenOffset := by
  unfold BranchRangeDomain
  unfold MainBranchRangeDomain MainSequentialPcDomain at h_domain
  rw [h_bridge] at h_domain
  exact h_domain

theorem auipcRangeDomain_of_main
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions} {imm : BitVec 20}
    {auipc_input : PureSpec.AuipcInput}
    (h_input_imm : auipc_input.imm = imm)
    (h_bridge : mainPcVal ziskTrace i = auipc_input.PC.toNat)
    (h_domain : MainAuipcRangeDomain ziskTrace i imm) :
    AuipcRangeDomain auipc_input where
  h_pc_bound := sequentialPcDomain_of_main h_bridge h_domain.h_pc_bound
  h_target_nonneg := by
    rw [h_input_imm, ← h_bridge]
    exact h_domain.h_target_nonneg
  h_target_lt := by
    rw [h_input_imm, ← h_bridge]
    exact h_domain.h_target_lt
  h_pc_offset_lt_2_32 := by
    simpa [h_input_imm] using h_domain.h_pc_offset_lt_2_32 auipc_input.PC h_bridge

theorem jalRangeDomain_of_main
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions} {imm : BitVec 21}
    {jal_input : PureSpec.JalInput}
    (h_input_imm : jal_input.imm = imm)
    (h_bridge : mainPcVal ziskTrace i = jal_input.PC.toNat)
    (h_domain : MainJalRangeDomain ziskTrace i imm) :
    JalRangeDomain jal_input where
  h_target_nonneg := by
    rw [h_input_imm, ← h_bridge]
    exact h_domain.h_target_nonneg
  h_target_lt := by
    rw [h_input_imm, ← h_bridge]
    exact h_domain.h_target_lt
  h_pc_bound := sequentialPcDomain_of_main h_bridge h_domain.h_pc_bound
  h_pc_offset_lt_2_32 := h_domain.h_pc_offset_lt_2_32 jal_input.PC h_bridge

theorem jalrRangeDomain_of_main
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions} {jalr_input : PureSpec.JalrInput}
    (h_bridge : mainPcVal ziskTrace i = jalr_input.PC.toNat)
    (h_domain : MainJalrRangeDomain ziskTrace i) :
    JalrRangeDomain jalr_input where
  h_pc_bound := sequentialPcDomain_of_main h_bridge h_domain.h_pc_bound
  h_pc_offset_lt_2_32 := h_domain.h_pc_offset_lt_2_32 jalr_input.PC h_bridge

def RowOutsideDefectRegion (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .mul _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ),
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a) →
          ¬ Defects.SignedMulForge v r_a
  | .mulh _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ),
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a) →
          ¬ Defects.SignedMulForge v r_a
  | .mulhsu _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ),
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a) →
          ¬ Defects.SignedMulForge v r_a
  | .div _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (providerTable : Air.Flat.Table FGL),
          providerTable ∈ ziskTrace.witness.allTables →
          ∀ (providerRow : Array FGL), providerRow ∈ providerTable.table →
          providerTable.component =
              ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent →
          providerTable.component.Spec (providerTable.environment providerRow) →
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) →
          ∀ (op2 : BitVec 64),
            let v := vOfDivuRow
              (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                (providerTable.environment providerRow))
            op2.toInt = Defects.signedDivisorInt v 0 →
              ¬ Defects.DivRemForge op2 v 0
                ∧ ¬ Defects.SignedDivQuotientSignForge v 0
  | .rem _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
            (op2 : BitVec 64),
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a) →
          op2.toInt = Defects.signedDivisorInt v r_a →
          ¬ Defects.DivRemForge op2 v r_a
  | .divw _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
            (op2 : BitVec 64),
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a) →
          (Sail.BitVec.extractLsb op2 31 0).toInt = Defects.signedDivisorIntW v r_a →
          ¬ Defects.DivRemForgeW op2 v r_a
  | .remw _ =>
      MainSequentialPcDomain ziskTrace i ∧
        ∀ (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
            (op2 : BitVec 64),
          ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val)
            (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a) →
          (Sail.BitVec.extractLsb op2 31 0).toInt = Defects.signedDivisorIntW v r_a →
          ¬ Defects.DivRemForgeW op2 v r_a
  | .mulw _ => MainSequentialPcDomain ziskTrace i
  | .mulhu _ => MainSequentialPcDomain ziskTrace i
  | .divu _ => MainSequentialPcDomain ziskTrace i
  | .divuw _ => MainSequentialPcDomain ziskTrace i
  | .remu _ => MainSequentialPcDomain ziskTrace i
  | .remuw _ => MainSequentialPcDomain ziskTrace i
  | .sub _ => MainSequentialPcDomain ziskTrace i
  | .and _ => MainSequentialPcDomain ziskTrace i
  | .or _ => MainSequentialPcDomain ziskTrace i
  | .xor _ => MainSequentialPcDomain ziskTrace i
  | .slt _ => MainSequentialPcDomain ziskTrace i
  | .sltu _ => MainSequentialPcDomain ziskTrace i
  | .andi _ => MainSequentialPcDomain ziskTrace i
  | .ori _ => MainSequentialPcDomain ziskTrace i
  | .xori _ => MainSequentialPcDomain ziskTrace i
  | .slti _ => MainSequentialPcDomain ziskTrace i
  | .sltiu _ => MainSequentialPcDomain ziskTrace i
  | .sll _ => MainSequentialPcDomain ziskTrace i
  | .srl _ => MainSequentialPcDomain ziskTrace i
  | .sra _ => MainSequentialPcDomain ziskTrace i
  | .slli _ => MainSequentialPcDomain ziskTrace i
  | .srli _ => MainSequentialPcDomain ziskTrace i
  | .srai _ => MainSequentialPcDomain ziskTrace i
  | .add _ => MainSequentialPcDomain ziskTrace i
  | .addi _ => MainSequentialPcDomain ziskTrace i
  | .subw _ => MainSequentialPcDomain ziskTrace i
  | .addw _ => MainSequentialPcDomain ziskTrace i
  | .addiw _ => MainSequentialPcDomain ziskTrace i
  | .sllw _ => MainSequentialPcDomain ziskTrace i
  | .srlw _ => MainSequentialPcDomain ziskTrace i
  | .sraw _ => MainSequentialPcDomain ziskTrace i
  | .slliw c => SequentialPcDomain c.slliw_input.PC
  | .srliw c => SequentialPcDomain c.srliw_input.PC
  | .sraiw c => SequentialPcDomain c.sraiw_input.PC
  | .beq c =>
      MainBranchRangeDomain ziskTrace i
        (BitVec.signExtend 64 c.imm)
  | .bne c =>
      MainBranchRangeDomain ziskTrace i
        (BitVec.signExtend 64 c.imm)
  | .blt c =>
      MainBranchRangeDomain ziskTrace i
        (BitVec.signExtend 64 c.imm)
  | .bge c =>
      MainBranchRangeDomain ziskTrace i
        (BitVec.signExtend 64 c.imm)
  | .bltu c =>
      MainBranchRangeDomain ziskTrace i
        (BitVec.signExtend 64 c.imm)
  | .bgeu c =>
      MainBranchRangeDomain ziskTrace i
        (BitVec.signExtend 64 c.imm)
  | .auipc c => MainAuipcRangeDomain ziskTrace i c.imm
  | .jal c => MainJalRangeDomain ziskTrace i c.imm
  | .jalr _ => MainJalrRangeDomain ziskTrace i
  | .lui _ => MainSequentialPcDomain ziskTrace i
  | .sb c => SequentialPcDomain c.sb_input.PC
  | .sh c => SequentialPcDomain c.sh_input.PC
  | .sw c => SequentialPcDomain c.sw_input.PC
  | .sd c => SequentialPcDomain c.sd_input.PC
  | .ld c => SequentialPcDomain c.ld_input.PC
  | .lbu c =>
      SequentialPcDomain c.lbu_input.PC ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
          1 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .lhu c =>
      SequentialPcDomain c.lhu_input.PC ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
          2 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .lwu c =>
      SequentialPcDomain c.lwu_input.PC ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
          4 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .lb c =>
      SequentialPcDomain c.lb_input.PC ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
          1 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .lh c =>
      SequentialPcDomain c.lh_input.PC ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
          2 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .lw c =>
      SequentialPcDomain c.lw_input.PC ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
          4 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
  | .fence c => MainSequentialPcDomain ziskTrace i ∧
      Defects.FenceKnownGood c.fm c.rs c.rd

/-- The LBU arm's trace-local defect boundary is exactly the selected Main
    load-row's no-forge fact. -/
theorem no_memAlignNarrowLoadLaneForge_of_lbu_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lbu ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lbu c)) :
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
      1 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.1

/-- The LHU arm's trace-local defect boundary is exactly the selected Main
    load-row's no-forge fact. -/
theorem no_memAlignNarrowLoadLaneForge_of_lhu_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lhu ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lhu c)) :
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
      2 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.1

/-- The LWU arm's trace-local defect boundary is exactly the selected Main
    load-row's no-forge fact. -/
theorem no_memAlignNarrowLoadLaneForge_of_lwu_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lwu ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lwu c)) :
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
      4 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.1

/-- The LB arm's trace-local defect boundary is exactly the selected Main
    load-row's no-forge fact. -/
theorem no_memAlignNarrowLoadLaneForge_of_lb_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lb ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lb c)) :
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
      1 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.1

/-- The LH arm's trace-local defect boundary is exactly the selected Main
    load-row's no-forge fact. -/
theorem no_memAlignNarrowLoadLaneForge_of_lh_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lh ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lh c)) :
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
      2 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.1

/-- The LW arm's trace-local defect boundary is exactly the selected Main
    load-row's no-forge fact. -/
theorem no_memAlignNarrowLoadLaneForge_of_lw_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lw ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lw c)) :
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
      4 (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.1

/-- The LBU arm's #1142 boundary excludes exactly a selected general-MemAlign
    interaction that lacks the prove-side pins. -/
theorem no_memAlignSkippableProveForge_of_lbu_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lbu ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lbu c)) :
    ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.2

/-- The LHU arm's #1142 boundary excludes exactly a selected general-MemAlign
    interaction that lacks the prove-side pins. -/
theorem no_memAlignSkippableProveForge_of_lhu_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lhu ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lhu c)) :
    ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.2

/-- The LWU arm's #1142 boundary excludes exactly a selected general-MemAlign
    interaction that lacks the prove-side pins. -/
theorem no_memAlignSkippableProveForge_of_lwu_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lwu ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lwu c)) :
    ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.2

/-- The LB arm's #1142 boundary excludes exactly a selected general-MemAlign
    interaction that lacks the prove-side pins. -/
theorem no_memAlignSkippableProveForge_of_lb_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lb ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lb c)) :
    ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.2

/-- The LH arm's #1142 boundary excludes exactly a selected general-MemAlign
    interaction that lacks the prove-side pins. -/
theorem no_memAlignSkippableProveForge_of_lh_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lh ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lh c)) :
    ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.2

/-- The LW arm's #1142 boundary excludes exactly a selected general-MemAlign
    interaction that lacks the prove-side pins. -/
theorem no_memAlignSkippableProveForge_of_lw_rowOutside
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (c : Claim_lw ziskTrace i)
    (h_outside : RowOutsideDefectRegion ziskTrace i (.lw c)) :
    ¬ Defects.MemAlignSkippableProveForge ziskTrace.program ziskTrace.witness
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :=
  h_outside.2.2

private def StepSoundWithoutDecode
    (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions) (i : Fin ziskTrace.numInstructions) :
    ZiskStep ziskTrace i → Prop
  | .sub c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SUB))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .and c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.AND))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .or c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.OR))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .xor c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.XOR))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .slt c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLT))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sltu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLTU))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .andi c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.ANDI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .ori c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.ORI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .xori c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.XORI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .slti c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.SLTI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sltiu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.SLTIU))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sll c =>
      execute_instruction (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLL)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .srl c =>
      execute_instruction (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SRL)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sra c =>
      execute_instruction (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SRA)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .slli c =>
      execute_instruction (instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SLLI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .srli c =>
      execute_instruction (instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SRLI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .srai c =>
      execute_instruction (instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SRAI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .add c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (c.r2, c.r1, c.rd, rop.ADD))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .addi c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (c.imm, c.r1, c.rd, iop.ADDI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .subw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SUBW))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .addw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.ADDW))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .addiw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (c.imm, c.r1, c.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sllw c =>
      execute_instruction (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SLLW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .srlw c =>
      execute_instruction (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SRLW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sraw c =>
      execute_instruction (instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SRAW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .slliw c =>
      execute_instruction
        (instruction.SHIFTIWOP (c.slliw_input.shamt, c.r1, c.rd, sopw.SLLIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .srliw c =>
      execute_instruction
        (instruction.SHIFTIWOP (c.srliw_input.shamt, c.r1, c.rd, sopw.SRLIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sraiw c =>
      execute_instruction
        (instruction.SHIFTIWOP (c.sraiw_input.shamt, c.r1, c.rd, sopw.SRAIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
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
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
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
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
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
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .div c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .rem c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .divw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .remw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (c.r2, c.r1, c.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .mulw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (c.r2, c.r1, c.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
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
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .divu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .divuw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .remu c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .remuw c =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (c.r2, c.r1, c.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .beq c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BEQ)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)
  | .bne c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BNE)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)
  | .blt c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BLT)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)
  | .bge c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BGE)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)
  | .bltu c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BLTU)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)
  | .bgeu c =>
      execute_instruction (instruction.BTYPE (c.imm, c.r2, c.r1, bop.BGEU)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)
  | .lui c =>
      execute_instruction (instruction.UTYPE (c.imm, c.rd, uop.LUI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf ziskTrace i, [eRdLui ziskTrace i]⟩ (sailTrace i)
  | .auipc c =>
      execute_instruction (instruction.UTYPE (c.imm, c.rd, uop.AUIPC)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf ziskTrace i, [eRdLui ziskTrace i]⟩ (sailTrace i)
  | .jal c =>
      execute_instruction (instruction.JAL (c.imm, c.rd)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf ziskTrace i, [eRdLui ziskTrace i]⟩ (sailTrace i)
  -- UNREACHABLE, and kept only so this match stays exhaustive: the public
  -- `StepSound` matches `.jalr` against its own decode-indexed arm before ever
  -- falling through to here. That arm supersedes this weaker existential form
  -- (it fixes the lowering row from the caller's decode instead of positing one).
  | .jalr c =>
      ∃ decode : Decode_jalr ziskTrace i c,
        (do
          Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
          LeanRV64D.Functions.execute (instruction.JALR (c.imm, c.rs1, c.rd))) (sailTrace i)
        = ZiskFv.Channels.state_effect_via_channels
            ⟨Pilot.execRowAt ziskTrace decode.rows.finish,
              [eRdAt ziskTrace decode.rows.finish]⟩ (sailTrace i)
  | .sb c =>
      execute_instruction (instruction.STORE
          (c.sb_input.imm, regidx.Regidx c.sb_input.r2, regidx.Regidx c.sb_input.r1, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sh c =>
      execute_instruction (instruction.STORE
          (c.sh_input.imm, regidx.Regidx c.sh_input.r2, regidx.Regidx c.sh_input.r1, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sw c =>
      execute_instruction (instruction.STORE
          (c.sw_input.imm, regidx.Regidx c.sw_input.r2, regidx.Regidx c.sw_input.r1, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .sd c =>
      execute_instruction (instruction.STORE
          (c.sd_input.imm, regidx.Regidx c.sd_input.r2, regidx.Regidx c.sd_input.r1, 8))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .ld c =>
      execute_instruction (instruction.LOAD
          (c.ld_input.imm, regidx.Regidx c.ld_input.r1, regidx.Regidx c.ld_input.rd, false, 8))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .lbu c =>
      execute_instruction (instruction.LOAD
          (c.lbu_input.imm, regidx.Regidx c.lbu_input.r1, regidx.Regidx c.lbu_input.rd, true, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .lhu c =>
      execute_instruction (instruction.LOAD
          (c.lhu_input.imm, regidx.Regidx c.lhu_input.r1, regidx.Regidx c.lhu_input.rd, true, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .lwu c =>
      execute_instruction (instruction.LOAD
          (c.lwu_input.imm, regidx.Regidx c.lwu_input.r1, regidx.Regidx c.lwu_input.rd, true, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .lb c =>
      execute_instruction (instruction.LOAD
          (c.lb_input.imm, regidx.Regidx c.lb_input.r1, regidx.Regidx c.lb_input.rd, false, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .lh c =>
      execute_instruction (instruction.LOAD
          (c.lh_input.imm, regidx.Regidx c.lh_input.r1, regidx.Regidx c.lh_input.rd, false, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .lw c =>
      execute_instruction (instruction.LOAD
          (c.lw_input.imm, regidx.Regidx c.lw_input.r1, regidx.Regidx c.lw_input.rd, false, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
           [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
            (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩ (sailTrace i)
  | .fence c =>
      execute_instruction (instruction.FENCE (c.fm, c.fenceP, c.fenceS, c.rs, c.rd)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf ziskTrace i, []⟩ (sailTrace i)

/-- Per-step soundness indexed by the checked row decode. JALR needs this
    index because one architectural instruction may occupy an aligned singleton
    Main row or an unaligned ADD/AND pair. Other families retain their existing
    identity-row effects until the decode-driven export migration. -/
def StepSound
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions)
    (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) : Prop :=
  match zs, rd with
  | .jalr c, decode =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.JALR (c.imm, c.rs1, c.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowAt ziskTrace decode.rows.finish,
            [eRdAt ziskTrace decode.rows.finish]⟩ (sailTrace i)
  | other, _ => StepSoundWithoutDecode ziskTrace sailTrace i other

/-- Per-row dispatch to the matching strengthened step theorem.

    The `hAvoidKnownBugs` parameter carries the per-row defect-exclusion obligation
    (`RowOutsideDefectRegion`), stated over the accepted ZisK trace row without
    `SailTrace` or `InputsAgree`.  For the 8 defect-capable arms it universally
    excludes forge shapes for arith witness rows whose op-bus entry matches the
    Main row, or requires FENCE-known-good pins directly from the decoded row.  The
    dispatcher instantiates that trace-local matcher with the arith row evidence
    already present in the step evidence and hands the resulting forge-negation to
    the matching `stepStrong_<op>`, which assembles `NoKnownDefect (<op>EnvOf …)`
    from it.  For every other (non-defect) arm the obligation is `True` and is
    ignored — the arm builds its own `NoKnownDefect`. -/

private theorem div_exclusions_of_selected_provider
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (c : Claim_div ziskTrace i)
    (rd : Decode_div ziskTrace i c) (ia : Inputs_div ziskTrace sailTrace i c)
    (hAvoidKnownBugs : RowOutsideDefectRegion ziskTrace i (.div c)) :
    ¬ Defects.DivRemForge ia.div_input.r2_val
        (divV ziskTrace sailTrace i rd.h_main_active rd.h_main_op) 0
      ∧ ¬ Defects.SignedDivQuotientSignForge
        (divV ziskTrace sailTrace i rd.h_main_active rd.h_main_op) 0 := by
  have h_divisor :
      ia.div_input.r2_val.toInt =
        Defects.signedDivisorInt
          (divV ziskTrace sailTrace i rd.h_main_active rd.h_main_op) 0 := by
    simpa only [Defects.signedDivisorInt] using
      ia.h_rs2_value rd.h_main_active rd.h_main_op
  apply divV_exclusions_of_provider_rows ziskTrace sailTrace i
    rd.h_main_active rd.h_main_op ia.div_input.r2_val
  · intro providerTable h_table providerRow h_row h_component h_spec h_match
    exact hAvoidKnownBugs.2 providerTable h_table providerRow h_row
      h_component h_spec h_match ia.div_input.r2_val
  · exact h_divisor

theorem stepSound_of_evidence (ziskTrace : AcceptedZiskTrace numInstructions) (sailTrace : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) (ia : InputsAgree ziskTrace sailTrace i zs)
    (memEv : MemoryOpEvidenceFor ziskTrace sailTrace i zs)
    (hAvoidKnownBugs : RowOutsideDefectRegion ziskTrace i zs) :
    StepSound ziskTrace sailTrace i zs rd := by
  cases zs with
  | sub c =>
      exact stepStrong_sub ziskTrace sailTrace i (toRowData_sub c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | and c =>
      exact stepStrong_and ziskTrace sailTrace i (toRowData_and c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | or c =>
      exact stepStrong_or ziskTrace sailTrace i (toRowData_or c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | xor c =>
      exact stepStrong_xor ziskTrace sailTrace i (toRowData_xor c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | slt c =>
      exact stepStrong_slt ziskTrace sailTrace i (toRowData_slt c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | sltu c =>
      exact stepStrong_sltu ziskTrace sailTrace i (toRowData_sltu c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | andi c =>
      exact stepStrong_andi ziskTrace sailTrace i (toRowData_andi c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | ori c =>
      exact stepStrong_ori ziskTrace sailTrace i (toRowData_ori c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | xori c =>
      exact stepStrong_xori ziskTrace sailTrace i (toRowData_xori c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | slti c =>
      exact stepStrong_slti ziskTrace sailTrace i (toRowData_slti c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | sltiu c =>
      exact stepStrong_sltiu ziskTrace sailTrace i (toRowData_sltiu c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | sll c =>
      exact stepStrong_sll ziskTrace sailTrace i (toRowData_sll c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | srl c =>
      exact stepStrong_srl ziskTrace sailTrace i (toRowData_srl c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | sra c =>
      exact stepStrong_sra ziskTrace sailTrace i (toRowData_sra c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | slli c =>
      exact stepStrong_slli ziskTrace sailTrace i (toRowData_slli c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | srli c =>
      exact stepStrong_srli ziskTrace sailTrace i (toRowData_srli c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | srai c =>
      exact stepStrong_srai ziskTrace sailTrace i (toRowData_srai c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | add c =>
      exact stepStrong_add ziskTrace sailTrace i (toRowData_add c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | addi c =>
      exact stepStrong_addi ziskTrace sailTrace i (toRowData_addi c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | subw c =>
      exact stepStrong_subw ziskTrace sailTrace i (toRowData_subw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | addw c =>
      exact stepStrong_addw ziskTrace sailTrace i (toRowData_addw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | addiw c =>
      exact stepStrong_addiw ziskTrace sailTrace i (toRowData_addiw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | sllw c =>
      exact stepStrong_sllw ziskTrace sailTrace i (toRowData_sllw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | srlw c =>
      exact stepStrong_srlw ziskTrace sailTrace i (toRowData_srlw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | sraw c =>
      exact stepStrong_sraw ziskTrace sailTrace i (toRowData_sraw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | slliw c => exact stepStrong_slliw ziskTrace sailTrace i (toRowData_slliw c rd ia) hAvoidKnownBugs
  | srliw c => exact stepStrong_srliw ziskTrace sailTrace i (toRowData_srliw c rd ia) hAvoidKnownBugs
  | sraiw c => exact stepStrong_sraiw ziskTrace sailTrace i (toRowData_sraiw c rd ia) hAvoidKnownBugs
  | mul c =>
      exact stepStrong_mul ziskTrace sailTrace i (toRowData_mul c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        (hAvoidKnownBugs.2 ia.v ia.r_a ia.h_match_primary)
  | mulh c =>
      exact stepStrong_mulh ziskTrace sailTrace i (toRowData_mulh c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        (hAvoidKnownBugs.2 ia.v ia.r_a ia.h_match_secondary)
  | mulhsu c =>
      exact stepStrong_mulhsu ziskTrace sailTrace i (toRowData_mulhsu c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        (hAvoidKnownBugs.2 ia.v ia.r_a ia.h_match_secondary)
  | mulw c =>
      exact stepStrong_mulw ziskTrace sailTrace i (toRowData_mulw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | mulhu c =>
      exact stepStrong_mulhu ziskTrace sailTrace i (toRowData_mulhu c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | div c =>
      have h_exclusions :=
        div_exclusions_of_selected_provider ziskTrace sailTrace i c rd ia
          hAvoidKnownBugs
      exact stepStrong_div ziskTrace sailTrace i (toRowData_div c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        h_exclusions.1 h_exclusions.2
  | rem c =>
      exact stepStrong_rem ziskTrace sailTrace i (toRowData_rem c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        (hAvoidKnownBugs.2 ia.v ia.r_a ia.rem_input.r2_val ia.h_match_secondary
          (by simpa [Defects.signedDivisorInt] using ia.h_rs2_value))
  | divw c =>
      exact stepStrong_divw ziskTrace sailTrace i (toRowData_divw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        (hAvoidKnownBugs.2 ia.v ia.r_a ia.divw_input.r2_val ia.h_match_primary
          (by simpa [Defects.signedDivisorIntW] using ia.h_rs2_value))
  | remw c =>
      exact stepStrong_remw ziskTrace sailTrace i (toRowData_remw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        (hAvoidKnownBugs.2 ia.v ia.r_a ia.remw_input.r2_val ia.h_match_secondary
          (by simpa [Defects.signedDivisorIntW] using ia.h_rs2_value))
  | divu c =>
      exact stepStrong_divu ziskTrace sailTrace i (toRowData_divu c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | divuw c =>
      exact stepStrong_divuw ziskTrace sailTrace i (toRowData_divuw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | remu c =>
      exact stepStrong_remu ziskTrace sailTrace i (toRowData_remu c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | remuw c =>
      exact stepStrong_remuw ziskTrace sailTrace i (toRowData_remuw c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | beq c =>
      exact stepStrong_beq ziskTrace sailTrace i (toRowData_beq c rd ia)
        (by
          change BranchRangeDomain ziskTrace i ia.beq_input.PC
            (BitVec.signExtend 64 ia.beq_input.imm)
          simpa [ia.h_input_imm] using
            branchRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | bne c =>
      exact stepStrong_bne ziskTrace sailTrace i (toRowData_bne c rd ia)
        (by
          change BranchRangeDomain ziskTrace i ia.bne_input.PC
            (BitVec.signExtend 64 ia.bne_input.imm)
          simpa [ia.h_input_imm] using
            branchRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | blt c =>
      exact stepStrong_blt ziskTrace sailTrace i (toRowData_blt c rd ia)
        (by
          change BranchRangeDomain ziskTrace i ia.blt_input.PC
            (BitVec.signExtend 64 ia.blt_input.imm)
          simpa [ia.h_input_imm] using
            branchRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | bge c =>
      exact stepStrong_bge ziskTrace sailTrace i (toRowData_bge c rd ia)
        (by
          change BranchRangeDomain ziskTrace i ia.bge_input.PC
            (BitVec.signExtend 64 ia.bge_input.imm)
          simpa [ia.h_input_imm] using
            branchRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | bltu c =>
      exact stepStrong_bltu ziskTrace sailTrace i (toRowData_bltu c rd ia)
        (by
          change BranchRangeDomain ziskTrace i ia.bltu_input.PC
            (BitVec.signExtend 64 ia.bltu_input.imm)
          simpa [ia.h_input_imm] using
            branchRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | bgeu c =>
      exact stepStrong_bgeu ziskTrace sailTrace i (toRowData_bgeu c rd ia)
        (by
          change BranchRangeDomain ziskTrace i ia.bgeu_input.PC
            (BitVec.signExtend 64 ia.bgeu_input.imm)
          simpa [ia.h_input_imm] using
            branchRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | lui c =>
      exact stepStrong_lui ziskTrace sailTrace i (toRowData_lui c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs)
  | auipc c =>
      exact stepStrong_auipc ziskTrace sailTrace i (toRowData_auipc c rd ia)
        (auipcRangeDomain_of_main ia.h_input_imm ia.h_pc_bridge hAvoidKnownBugs)
  | jal c =>
      let h_domain :=
        jalRangeDomain_of_main ia.h_input_imm ia.h_pc_bridge hAvoidKnownBugs
      let nextPC_val : BitVec 64 :=
        ia.jal_input.PC + BitVec.signExtend 64 ia.jal_input.imm
      have h_nextPC_option :
          (PureSpec.execute_JAL_pure ia.jal_input).nextPC = .some nextPC_val :=
        PureSpec.execute_JAL_pure_succ_nextPC ia.jal_input ia.h_success
      have h_offset_bridge :
          (mainOfTable ziskTrace.program ziskTrace.mainTable).jmp_offset1 i.val =
            ((BitVec.signExtend 64 ia.jal_input.imm).toInt : FGL) := by
        simpa [ia.h_input_imm] using rd.h_jmp_offset1_imm
      have h_spec := mainSpec_at ziskTrace sailTrace i
      have h_subset := ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt
        (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val h_spec
      have h_flag :
          (mainOfTable ziskTrace.program ziskTrace.mainTable).flag i.val = 1 :=
        ZiskFv.Airs.Main.flag_eq_one_of_internal_op_zero
          (mainOfTable ziskTrace.program ziskTrace.mainTable) i.val rd.h_main_active
          (by simpa [ZiskFv.Trusted.OP_FLAG] using rd.h_main_op)
          h_subset.2.2.2.2.1
      have h_nextPC_matches :
          (register_type_pc_equiv ▸
              (BitVec.ofNat 64 ((Pilot.execRowOf ziskTrace i)[1]!.pc).val))
            = nextPC_val := by
        simpa [nextPC_val] using jal_nextPC_matches_of_physical ziskTrace i
          ia.jal_input.PC ia.jal_input.imm rd.h_idx rd.h_set_pc h_flag
          ia.h_pc_bridge h_offset_bridge h_domain.h_target_nonneg h_domain.h_target_lt
      have h_not_throws :
          (PureSpec.execute_JAL_pure ia.jal_input).throws = false :=
        PureSpec.execute_JAL_pure_succ_throws ia.jal_input ia.h_success
      have h_rd_idx :
          ia.jal_input.rd =
            Transpiler.wrap_to_regidx (eRdLui ziskTrace i).ptr :=
        ia.h_input_rd.trans
          (eRdLui_rd_idx_of_decode (trace := ziskTrace) (i := i)
            (rd := c.rd) rd.h_store_ind rd.h_store_offset)
      exact construction_jal_sound_claimed_dead ziskTrace sailTrace i
        ia.jal_input c.imm c.rd ia.misa_val nextPC_val
        rd.h_main_op rd.h_main_active rd.h_m32 rd.h_set_pc rd.h_store_pc
        rd.h_jmp2 ia.h_pc_bridge (Pilot.execRowOf ziskTrace i)
        (by rfl) (by rfl) (by rfl) h_nextPC_matches
        ia.h_input_rd ia.h_input_pc ia.h_input_misa ia.h_misa_c ia.h_success
        h_nextPC_option h_rd_idx
        ia.h_input_imm h_not_throws h_domain.h_pc_bound
        h_domain.h_pc_offset_lt_2_32
  | jalr c =>
      let h_domain :=
        jalrRangeDomain_of_main ia.h_pc_bridge hAvoidKnownBugs
      set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable ziskTrace.program ziskTrace.mainTable with hm
      set state := sailTrace i with hstate
      let finish := rd.rows.finish
      let r := finish.val
      let e_rd := eRdAt ziskTrace finish
      -- (a) Main per-row Spec ⇒ the JALR Main constraint subset.
      have h_spec := mainSpec_at_physical ziskTrace finish
      have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m r :=
        ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m r h_spec
      obtain ⟨_h_c0, _h_b0, _h_c1, _h_b1, _h_set_flag, _h_clear_flag, h_disjoint,
          h_flag_bool, h_ext_bool⟩ := h_add_subset
      -- (a) the handshake is definitional: pick `next_pc` as its RHS.
      let next_pc : FGL :=
        m.set_pc r * (m.c_0 r + m.jmp_offset1 r)
          + (1 - m.set_pc r) * (m.pc r + m.jmp_offset2 r)
          + m.flag r * (m.jmp_offset1 r - m.jmp_offset2 r)
      have h_handshake :
          ZiskFv.Airs.Main.pc_handshake_with_next_pc m r next_pc := rfl
      have h_jalr_subset :
          ZiskFv.Airs.Main.flag_boolean m r
          ∧ ZiskFv.Airs.Main.is_external_op_boolean m r
          ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r
          ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r next_pc :=
        ⟨h_flag_bool, h_ext_bool, h_disjoint, h_handshake⟩
      -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
      have h_row_core :
          (mainRowWithRomAt ziskTrace finish).core =
            ZiskFv.AirsClean.Main.rowAt m r := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          ziskTrace.program ziskTrace.mainTable finish
        simpa [mainRowWithRomAt, m, r, finish,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := finish)] using this.symm
      let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r e_rd :=
        { row := mainRowWithRomAt ziskTrace finish
          row_eq := h_row_core
          rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
      let pins : ZiskFv.Compliance.MainRowPins m r 1 OP_AND :=
        ⟨rd.h_main_active, rd.h_main_op⟩
      -- (b) Binary `OP_AND` provider witnesses for the JALR row (mirrors
      --     `stepStrong_and`): the static Binary table row backing the masked-AND.
      obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
          h_component, h_table_spec, h_match⟩ :=
        main_request_logic_provided_at
          ziskTrace finish rd.h_main_active (Or.inl rd.h_main_op)
      let providerInput :=
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)
      obtain ⟨h_core, h_facts⟩ :=
        ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
          h_component h_table_spec h_provider_row
      have h_static :
          ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
        ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
          h_component h_table_spec h_provider_row
      have h_m32_zero : m.m32 r = 0 := rd.h_m32
      have h_emit :
          providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
            (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
        have h_match_op := h_match
        simp only [ZiskFv.Airs.OperationBus.matches_entry,
          ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
        have h_op_match :
            m.op r = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
          h_match_op.2.1
        rw [← h_op_match]
        simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
          rd.h_main_op
      obtain ⟨h_row_m32, h_bop, _⟩ :=
        ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
          providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
            simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
          h_core h_emit
      have h_out :=
        ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
          providerInput h_facts
          ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
      have h_matches :
          ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
            providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
        allByteMatchesOfStaticOut64_local h_out
      -- (c) lane projections: `a = mask`, `b = operand` (committed `b`-lane packing),
      --     and the carry-free `c` lanes (from `flag = 0`).
      have h_a_mask :
          ZiskFv.EquivCore.Add.binaryRowA64 providerInput = 0xFFFFFFFFFFFFFFFE#64 := by
        have h_a_pack : ZiskFv.EquivCore.Add.binaryRowA64 providerInput
            = BitVec.ofNat 64 ((m.a_0 r).val + (m.a_1 r).val * 4294967296) := by
          simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
            (ZiskFv.EquivCore.Bridge.Binary.main_a_packing_of_match
              m providerInput r h_matches h_m32_zero h_match).symm
        rw [h_a_pack, rd.h_a_mask_lo, rd.h_a_mask_hi]
        decide
      have h_b_operand :
          ZiskFv.EquivCore.Add.binaryRowB64 providerInput
            = BitVec.ofNat 64 ((m.b_0 r).val + (m.b_1 r).val * 4294967296) := by
        simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
          (ZiskFv.EquivCore.Bridge.Binary.main_b_packing_of_match
            m providerInput r h_matches h_m32_zero h_match).symm
      obtain ⟨h_match_clo, h_match_chi⟩ :=
        ZiskFv.EquivCore.Bridge.Binary.main_c_lanes_carryfree_of_match
          m providerInput r h_match rd.h_flag
      obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
        ZiskFv.EquivCore.Bridge.Binary.cByte_ranges_of_all_byte_matches_row
          providerInput h_matches
      let nextPC_val : BitVec 64 :=
        0xFFFFFFFFFFFFFFFE &&&
          (ia.jalr_input.rs1_val + BitVec.signExtend 64 ia.jalr_input.imm)
      have h_nextPC_option :
          (PureSpec.execute_JALR_pure ia.jalr_input).nextPC = .some nextPC_val :=
        PureSpec.execute_JALR_pure_succ_nextPC ia.jalr_input ia.h_success
      have h_nextPC_disch :
          (register_type_pc_equiv ▸
              (BitVec.ofNat 64 ((Pilot.execRowAt ziskTrace finish)[1]!.pc).val))
            = nextPC_val := by
        have hoo :
            BitVec.ofNat 64 ((m.b_0 r).val + (m.b_1 r).val * 4294967296)
                + c.offset_bv
              = ia.jalr_input.rs1_val
                + BitVec.signExtend 64 ia.jalr_input.imm := by
          rcases rd.rows.lowering with h_aligned | h_unaligned
          · obtain ⟨h_start_finish, h_offset⟩ := h_aligned
            have h_rs1 := ia.h_rs1_start
            rw [← rd.rows.architectural_start, h_start_finish] at h_rs1
            rw [h_offset, ia.h_input_imm, h_rs1]
          · obtain ⟨h_adj, h_offset, h_add_op, h_add_active, h_add_m32,
                _h_start_flag, _h_start_set_pc, _h_start_jmp2, h_start_a,
                _h_start_b_imm, _h_start_b_reg, h_finish_b_imm, h_finish_b_mem,
                h_finish_b_ind, h_finish_b_reg⟩ := h_unaligned
            have h_add := main_add_packed_result_at ziskTrace rd.rows.start
              h_add_active h_add_op h_add_m32
            let transitionIndex : Fin ziskTrace.mainTable.length :=
              ⟨finish.val, by simpa only [Table.length, Table.table_length]
                using finish.isLt⟩
            have h_trans := ziskTrace.transitions_hold ziskTrace.mainTable
              ziskTrace.mainTable_mem transitionIndex
            rw [ziskTrace.mainTable_component] at h_trans
            have h_transition :
                ZiskFv.AirsClean.Main.transitionBetween
                  ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                      ziskTrace.programLength ziskTrace.program).rowInput
                    (ziskTrace.mainTable.previousEnvironment transitionIndex))
                  ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                      ziskTrace.programLength ziskTrace.program).rowInput
                    (ziskTrace.mainTable.environmentAt transitionIndex)) :=
              transitionBetween_of_pcHandshakeTransition
                ziskTrace.programLength ziskTrace.program transitionIndex.val
                (ziskTrace.mainTable.previousEnvironment transitionIndex)
                (ziskTrace.mainTable.environmentAt transitionIndex) h_trans
            have h_positive : 0 < transitionIndex.val := by
              dsimp [transitionIndex]
              omega
            have h_prev_idx :
                transitionIndex.val - 1 = rd.rows.start.val := by
              dsimp [transitionIndex]
              omega
            have h_previous :=
              rowInputPrevious_eq_mainTableRowAtOrZero
                ziskTrace.program ziskTrace.mainTable transitionIndex h_positive
            have h_current :=
              rowInputAt_eq_mainTableRowAtOrZero
                ziskTrace.program ziskTrace.mainTable transitionIndex
            rw [h_previous, h_current] at h_transition
            rw [h_prev_idx] at h_transition
            have h_between :
                ZiskFv.AirsClean.Main.transitionBetween
                  (mainRowWithRomAt ziskTrace rd.rows.start)
                  (mainRowWithRomAt ziskTrace finish) := by
              exact h_transition
            have h_copy := source_c_copy_lanes_of_between
              (mainRowWithRomAt ziskTrace rd.rows.start)
              (mainRowWithRomAt ziskTrace finish) h_between
              (by
                have h_seg :=
                  ziskTrace.mainTable_fixed.segment_l1_succ rd.rows.start.val
                    (by simpa [h_adj] using finish.isLt)
                rw [h_adj] at h_seg
                exact h_seg)
              h_finish_b_imm h_finish_b_mem h_finish_b_ind h_finish_b_reg
            exact jalr_unaligned_operand_target m i.val rd.rows.start.val r
              c.offset_bv c.imm ia.jalr_input.imm ia.jalr_input.rs1_val
              h_offset h_add h_copy h_start_a rd.rows.architectural_start
              ia.h_rs1_start ia.h_input_imm
        have h_exec :=
          ZiskFv.Compliance.Pilot.jalr_setpc_nextPC_discharged
            ziskTrace finish providerInput
            (BitVec.ofNat 64 ((m.b_0 r).val + (m.b_1 r).val * 4294967296))
            c.offset_bv
            rd.h_idx rd.h_set_pc rd.h_flag
            h_matches h_match_clo h_match_chi h_a_mask h_b_operand
            hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
            rd.h_c1_zero rd.h_offset_bridge
            rd.h_offset_even rd.h_target_nonneg rd.h_target_lt
        exact jalr_nextPC_matches_of_target
          (register_type_pc_equiv ▸
            BitVec.ofNat 64 ((Pilot.execRowAt ziskTrace finish)[1]!.pc).val)
          (BitVec.ofNat 64 ((m.b_0 r).val + (m.b_1 r).val * 4294967296))
          c.offset_bv
          (ia.jalr_input.rs1_val
            + BitVec.signExtend 64 ia.jalr_input.imm)
          h_exec hoo
      have h_link_bridge :
          (m.pc finish.val + m.jmp_offset2 finish.val).val =
            (ia.jalr_input.PC + 4#64).toNat := by
        dsimp only [finish]
        rcases rd.rows.lowering with h_aligned | h_unaligned
        · obtain ⟨h_start_finish, _⟩ := h_aligned
          have hsf : rd.rows.start.val = finish.val :=
            congrArg Fin.val h_start_finish
          have h_finish_jmp2 : m.jmp_offset2 finish.val = 4 := by
            rcases rd.h_jmp2 with h | h
            · exact h.2
            · rw [hsf] at h
              omega
          have h_pc : (m.pc finish.val).val =
              ia.jalr_input.PC.toNat := by
            rw [← hsf, rd.rows.architectural_start]
            simpa [m] using ia.h_pc_bridge
          exact jalr_link_bridge_scalar (m.pc finish.val)
            (m.pc finish.val) (m.jmp_offset2 finish.val) ia.jalr_input.PC
            (by rw [h_finish_jmp2]) h_pc h_domain.h_pc_bound
        · have h_adj := h_unaligned.1
          have h_start_flag := h_unaligned.2.2.2.2.2.1
          have h_start_set_pc := h_unaligned.2.2.2.2.2.2.1
          have h_start_jmp2 := h_unaligned.2.2.2.2.2.2.2.1
          have h_finish_jmp2 : m.jmp_offset2 finish.val = 3 := by
            rcases rd.h_jmp2 with h | h
            · rw [h.1] at h_adj
              omega
            · exact h.2
          have h_start_pc : (m.pc rd.rows.start.val).val =
              ia.jalr_input.PC.toNat := by
            rw [rd.rows.architectural_start]
            simpa [m] using ia.h_pc_bridge
          have h_seg := ziskTrace.mainTable_fixed.segment_l1_succ
            rd.rows.start.val (by simpa [h_adj] using finish.isLt)
          have h_hand := ziskTrace.mainTransition_to_next_pc rd.rows.start.val
            (by simpa [h_adj] using finish.isLt) h_seg
          have h_pc_step := ZiskFv.Airs.Main.pc_handshake_branch m
            rd.rows.start.val (m.pc (rd.rows.start.val + 1))
            h_start_set_pc h_hand
          rw [h_start_flag, h_start_jmp2] at h_pc_step
          simp only [zero_mul, add_zero] at h_pc_step
          have h_total :
              m.pc finish.val + m.jmp_offset2 finish.val =
                m.pc rd.rows.start.val + 4 := by
            rw [h_finish_jmp2]
            have h_finish_pc :
                m.pc finish.val = m.pc rd.rows.start.val + 1 := by
              simpa [h_adj] using h_pc_step
            rw [h_finish_pc]
            ring
          exact jalr_link_bridge_scalar (m.pc rd.rows.start.val)
            (m.pc finish.val) (m.jmp_offset2 finish.val) ia.jalr_input.PC
            h_total h_start_pc h_domain.h_pc_bound
      by_cases h_rd_zero : (regidx_to_fin c.rd).val = 0
      · let promises : ZiskFv.EquivCore.Promises.JumpNoMemPromises
            state ia.jalr_input.PC ia.jalr_input.rd ia.misa_val
            (PureSpec.execute_JALR_pure ia.jalr_input).success
            (PureSpec.execute_JALR_pure ia.jalr_input).nextPC
            c.rd (Pilot.execRowAt ziskTrace finish) nextPC_val :=
          { input_rd_eq := ia.h_input_rd
            input_rd_zero := by
              rw [ia.h_input_rd]
              exact Fin.ext h_rd_zero
            input_pc_eq := ia.h_input_pc
            input_misa_eq := ia.h_input_misa
            misa_c_zero := ia.h_misa_c
            exec_len := by rfl
            e0_mult := by rfl
            e1_mult := by rfl
            nextPC_matches := h_nextPC_disch
            success := ia.h_success
            nextPC_option := h_nextPC_option }
        have h_store_offset_zero :
            (mainRowWithRomAt ziskTrace finish).rom.store_offset =
              Transpiler.ind (regidx_to_fin c.rd) := by
          simpa [h_rd_zero, Transpiler.ind] using rd.h_store_offset
        have h_rd_idx :
            ia.jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr :=
          ia.h_input_rd.trans
            (eRdAt_rd_idx_of_decode (trace := ziskTrace) (i := finish)
              (rd := c.rd) rd.h_store_ind h_store_offset_zero)
        have h_e_rd_idx_zero :
            Transpiler.wrap_to_regidx e_rd.ptr = 0 := by
          rw [← h_rd_idx]
          exact promises.input_rd_zero
        exact ZiskFv.Compliance.equiv_JALR_x0_no_memory
          state ia.jalr_input c.imm c.rs1 c.rd ia.misa_val ia.mseccfg
          (Pilot.execRowAt ziskTrace finish) e_rd nextPC_val promises
          (by rfl) (by rfl) h_e_rd_idx_zero
          ia.h_input_imm ia.h_input_rs1 ia.h_cur_privilege ia.h_mseccfg
      · have h_store_offset :
            (mainRowWithRomAt ziskTrace finish).rom.store_offset =
              Transpiler.ind (regidx_to_fin c.rd) := by
          simpa [h_rd_zero] using rd.h_store_offset
        let promises : ZiskFv.EquivCore.Promises.JumpPromises
            state ia.jalr_input.PC ia.jalr_input.rd ia.misa_val
            (PureSpec.execute_JALR_pure ia.jalr_input).success
            (PureSpec.execute_JALR_pure ia.jalr_input).nextPC
            c.rd (Pilot.execRowAt ziskTrace finish) e_rd nextPC_val :=
          { input_rd_eq := ia.h_input_rd
            input_pc_eq := ia.h_input_pc
            input_misa_eq := ia.h_input_misa
            misa_c_zero := ia.h_misa_c
            exec_len := by rfl
            e0_mult := by rfl
            e1_mult := by rfl
            nextPC_matches := h_nextPC_disch
            rd_mult := by rfl
            rd_as := by rfl
            success := ia.h_success
            nextPC_option := h_nextPC_option
            rd_idx := ia.h_input_rd.trans
              (eRdAt_rd_idx_of_decode (trace := ziskTrace) (i := finish)
                (rd := c.rd) rd.h_store_ind h_store_offset) }
        have h_store_pc_one : m.store_pc r = 1 := by
          rw [rd.h_store_pc]
          simp [h_rd_zero, ZiskFv.AirsClean.boolF]
        exact ZiskFv.Compliance.equiv_JALR
          state ia.jalr_input c.imm c.rs1 c.rd
          ia.misa_val ia.mseccfg (Pilot.execRowAt ziskTrace finish)
          e_rd nextPC_val m r next_pc store_pc_mem pins rd.h_flag
          rd.h_m32 rd.h_set_pc h_store_pc_one h_jalr_subset
          promises ia.h_input_imm ia.h_input_rs1
          ia.h_cur_privilege ia.h_mseccfg h_link_bridge
          h_domain.h_pc_bound h_domain.h_pc_offset_lt_2_32

  | sb c => exact stepStrong_sb ziskTrace sailTrace i (toRowData_sb c rd ia) memEv hAvoidKnownBugs
  | sh c => exact stepStrong_sh ziskTrace sailTrace i (toRowData_sh c rd ia) memEv hAvoidKnownBugs
  | sw c => exact stepStrong_sw ziskTrace sailTrace i (toRowData_sw c rd ia) memEv hAvoidKnownBugs
  | sd c => exact stepStrong_sd ziskTrace sailTrace i (toRowData_sd c rd ia) hAvoidKnownBugs
  | ld c => exact stepStrong_ld ziskTrace sailTrace i (toRowData_ld c rd ia) memEv hAvoidKnownBugs
  | lbu c => exact stepStrong_lbu ziskTrace sailTrace i (toRowData_lbu c rd ia) memEv hAvoidKnownBugs.1
  | lhu c => exact stepStrong_lhu ziskTrace sailTrace i (toRowData_lhu c rd ia) memEv hAvoidKnownBugs.1
  | lwu c => exact stepStrong_lwu ziskTrace sailTrace i (toRowData_lwu c rd ia) memEv hAvoidKnownBugs.1
  | lb c => exact stepStrong_lb ziskTrace sailTrace i (toRowData_lb c rd ia) memEv hAvoidKnownBugs.1
  | lh c => exact stepStrong_lh ziskTrace sailTrace i (toRowData_lh c rd ia) memEv hAvoidKnownBugs.1
  | lw c => exact stepStrong_lw ziskTrace sailTrace i (toRowData_lw c rd ia) memEv hAvoidKnownBugs.1
  | fence c =>
      exact stepStrong_fence ziskTrace sailTrace i (toRowData_fence c rd ia)
        (sequentialPcDomain_of_main ia.h_pc_bridge hAvoidKnownBugs.1)
        hAvoidKnownBugs.2

end ZiskFv.Compliance
