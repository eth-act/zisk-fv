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
    (ziskTrace : AcceptedZiskTrace) (sailTrace : SailTrace ziskTrace) (i : Fin ziskTrace.numInstructions) where
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
def StepNoKnownDefect
    (ziskTrace : AcceptedZiskTrace) (sailTrace : SailTrace ziskTrace) (i : Fin ziskTrace.numInstructions) :
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
def StepFaithful
    (ziskTrace : AcceptedZiskTrace) (sailTrace : SailTrace ziskTrace) (i : Fin ziskTrace.numInstructions) :
    StrongRowConstructionData ziskTrace sailTrace i → Prop
  | .sub d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SUB))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .and d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.AND))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .or d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.OR))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .xor d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.XOR))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .slt d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLT))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sltu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLTU))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .andi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ANDI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .ori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ORI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .xori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.XORI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .slti d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sltiu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTIU))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sll d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLL)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .srl d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRL)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sra d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRA)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .slli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SLLI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .srli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRLI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .srai d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRAI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .add d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.ADD))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .addi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ADDI))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .subw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SUBW))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .addw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.ADDW))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .addiw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (d.imm, d.r1, d.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sllw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SLLW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .srlw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRLW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sraw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRAW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .slliw d =>
      execute_instruction
        (instruction.SHIFTIWOP (d.slliw_input.shamt, d.r1, d.rd, sopw.SLLIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .srliw d =>
      execute_instruction
        (instruction.SHIFTIWOP (d.srliw_input.shamt, d.r1, d.rd, sopw.SRLIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sraiw d =>
      execute_instruction
        (instruction.SHIFTIWOP (d.sraiw_input.shamt, d.r1, d.rd, sopw.SRAIW)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .mul d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.Low
             signed_rs1 := d.srs1
             signed_rs2 := d.srs2 }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .mulh d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .mulhsu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .div d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .rem d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .divw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .remw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, false))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (sailTrace i)
  | .mulw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (d.r2, d.r1, d.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .mulhu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .divu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .divuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .remu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .remuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, true))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub ziskTrace sailTrace i d.execRow).exec_row,
           [(busSub ziskTrace sailTrace i d.execRow).e0, (busSub ziskTrace sailTrace i d.execRow).e1,
            (busSub ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .beq d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BEQ)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)
  | .bne d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BNE)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)
  | .blt d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLT)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)
  | .bge d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGE)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)
  | .bltu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLTU)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)
  | .bgeu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGEU)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)
  | .lui d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.LUI)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui ziskTrace sailTrace i]⟩ (sailTrace i)
  | .auipc d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.AUIPC)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui ziskTrace sailTrace i]⟩ (sailTrace i)
  | .jal d =>
      execute_instruction (instruction.JAL (d.imm, d.rd)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui ziskTrace sailTrace i]⟩ (sailTrace i)
  | .jalr d =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (d.imm, d.rs1, d.rd))) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui ziskTrace sailTrace i]⟩ (sailTrace i)
  | .sb d =>
      execute_instruction (instruction.STORE
          (d.sb_input.imm, regidx.Regidx d.sb_input.r2, regidx.Regidx d.sb_input.r1, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace sailTrace i d.execRow).exec_row,
           [(busSt ziskTrace sailTrace i d.execRow).e0, (busSt ziskTrace sailTrace i d.execRow).e1,
            (busSt ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sh d =>
      execute_instruction (instruction.STORE
          (d.sh_input.imm, regidx.Regidx d.sh_input.r2, regidx.Regidx d.sh_input.r1, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace sailTrace i d.execRow).exec_row,
           [(busSt ziskTrace sailTrace i d.execRow).e0, (busSt ziskTrace sailTrace i d.execRow).e1,
            (busSt ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sw d =>
      execute_instruction (instruction.STORE
          (d.sw_input.imm, regidx.Regidx d.sw_input.r2, regidx.Regidx d.sw_input.r1, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace sailTrace i d.execRow).exec_row,
           [(busSt ziskTrace sailTrace i d.execRow).e0, (busSt ziskTrace sailTrace i d.execRow).e1,
            (busSt ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .sd d =>
      execute_instruction (instruction.STORE
          (d.sd_input.imm, regidx.Regidx d.sd_input.r2, regidx.Regidx d.sd_input.r1, 8))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt ziskTrace sailTrace i d.execRow).exec_row,
           [(busSt ziskTrace sailTrace i d.execRow).e0, (busSt ziskTrace sailTrace i d.execRow).e1,
            (busSt ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .ld d =>
      execute_instruction (instruction.LOAD
          (d.ld_input.imm, regidx.Regidx d.ld_input.r1, regidx.Regidx d.ld_input.rd, false, 8))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .lbu d =>
      execute_instruction (instruction.LOAD
          (d.lbu_input.imm, regidx.Regidx d.lbu_input.r1, regidx.Regidx d.lbu_input.rd, true, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .lhu d =>
      execute_instruction (instruction.LOAD
          (d.lhu_input.imm, regidx.Regidx d.lhu_input.r1, regidx.Regidx d.lhu_input.rd, true, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .lwu d =>
      execute_instruction (instruction.LOAD
          (d.lwu_input.imm, regidx.Regidx d.lwu_input.r1, regidx.Regidx d.lwu_input.rd, true, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .lb d =>
      execute_instruction (instruction.LOAD
          (d.lb_input.imm, regidx.Regidx d.lb_input.r1, regidx.Regidx d.lb_input.rd, false, 1))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .lh d =>
      execute_instruction (instruction.LOAD
          (d.lh_input.imm, regidx.Regidx d.lh_input.r1, regidx.Regidx d.lh_input.rd, false, 2))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .lw d =>
      execute_instruction (instruction.LOAD
          (d.lw_input.imm, regidx.Regidx d.lw_input.r1, regidx.Regidx d.lw_input.rd, false, 4))
          (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd ziskTrace sailTrace i d.execRow).exec_row,
           [(busLd ziskTrace sailTrace i d.execRow).e0, (busLd ziskTrace sailTrace i d.execRow).e1,
            (busLd ziskTrace sailTrace i d.execRow).e2]⟩ (sailTrace i)
  | .fence d =>
      execute_instruction (instruction.FENCE (d.fm, d.fenceP, d.fenceS, d.rs, d.rd)) (sailTrace i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (sailTrace i)

/-- Per-row dispatch to the matching strengthened step theorem.

    The `h_known` parameter carries the per-row defect-exclusion obligation
    (`StepNoKnownDefect`).  For the 22 OpEnvelope-route arms it is the
    `EnvNoKnownDefectFor` fact for that arm's constructor; the dispatcher hands it
    straight to the corresponding `stepStrong_<op>`, which feeds it to
    `zisk_riscv_compliant_program_bus`.  For the direct-lift arms (which never call
    the old theorem) the obligation is `True` and is ignored. -/
theorem stepFaithful_of_evidence
    (ziskTrace : AcceptedZiskTrace) (sailTrace : SailTrace ziskTrace) (i : Fin ziskTrace.numInstructions)
    (d : StrongRowConstructionData ziskTrace sailTrace i)
    (h_known : StepNoKnownDefect ziskTrace sailTrace i d) :
    StepFaithful ziskTrace sailTrace i d := by
  cases d with
  | sub d => exact stepStrong_sub ziskTrace sailTrace i d h_known
  | and d => exact stepStrong_and ziskTrace sailTrace i d h_known
  | or d => exact stepStrong_or ziskTrace sailTrace i d h_known
  | xor d => exact stepStrong_xor ziskTrace sailTrace i d h_known
  | slt d => exact stepStrong_slt ziskTrace sailTrace i d h_known
  | sltu d => exact stepStrong_sltu ziskTrace sailTrace i d h_known
  | andi d => exact stepStrong_andi ziskTrace sailTrace i d h_known
  | ori d => exact stepStrong_ori ziskTrace sailTrace i d h_known
  | xori d => exact stepStrong_xori ziskTrace sailTrace i d h_known
  | slti d => exact stepStrong_slti ziskTrace sailTrace i d h_known
  | sltiu d => exact stepStrong_sltiu ziskTrace sailTrace i d h_known
  | sll d => exact stepStrong_sll ziskTrace sailTrace i d h_known
  | srl d => exact stepStrong_srl ziskTrace sailTrace i d h_known
  | sra d => exact stepStrong_sra ziskTrace sailTrace i d h_known
  | slli d => exact stepStrong_slli ziskTrace sailTrace i d h_known
  | srli d => exact stepStrong_srli ziskTrace sailTrace i d h_known
  | srai d => exact stepStrong_srai ziskTrace sailTrace i d h_known
  | add d => exact stepStrong_add ziskTrace sailTrace i d h_known
  | addi d => exact stepStrong_addi ziskTrace sailTrace i d h_known
  | subw d => exact stepStrong_subw ziskTrace sailTrace i d h_known
  | addw d => exact stepStrong_addw ziskTrace sailTrace i d h_known
  | addiw d => exact stepStrong_addiw ziskTrace sailTrace i d h_known
  | sllw d => exact stepStrong_sllw ziskTrace sailTrace i d h_known
  | srlw d => exact stepStrong_srlw ziskTrace sailTrace i d h_known
  | sraw d => exact stepStrong_sraw ziskTrace sailTrace i d h_known
  | slliw d => exact stepStrong_slliw ziskTrace sailTrace i d h_known
  | srliw d => exact stepStrong_srliw ziskTrace sailTrace i d h_known
  | sraiw d => exact stepStrong_sraiw ziskTrace sailTrace i d h_known
  | mul d => exact stepStrong_mul ziskTrace sailTrace i d h_known
  | mulh d => exact stepStrong_mulh ziskTrace sailTrace i d h_known
  | mulhsu d => exact stepStrong_mulhsu ziskTrace sailTrace i d h_known
  | div d => exact stepStrong_div ziskTrace sailTrace i d h_known
  | rem d => exact stepStrong_rem ziskTrace sailTrace i d h_known
  | divw d => exact stepStrong_divw ziskTrace sailTrace i d h_known
  | remw d => exact stepStrong_remw ziskTrace sailTrace i d h_known
  | mulw d => exact stepStrong_mulw ziskTrace sailTrace i d h_known
  | mulhu d => exact stepStrong_mulhu ziskTrace sailTrace i d h_known
  | divu d => exact stepStrong_divu ziskTrace sailTrace i d h_known
  | divuw d => exact stepStrong_divuw ziskTrace sailTrace i d h_known
  | remu d => exact stepStrong_remu ziskTrace sailTrace i d h_known
  | remuw d => exact stepStrong_remuw ziskTrace sailTrace i d h_known
  | beq d => exact stepStrong_beq ziskTrace sailTrace i d h_known
  | bne d => exact stepStrong_bne ziskTrace sailTrace i d h_known
  | blt d => exact stepStrong_blt ziskTrace sailTrace i d h_known
  | bge d => exact stepStrong_bge ziskTrace sailTrace i d h_known
  | bltu d => exact stepStrong_bltu ziskTrace sailTrace i d h_known
  | bgeu d => exact stepStrong_bgeu ziskTrace sailTrace i d h_known
  | lui d => exact stepStrong_lui ziskTrace sailTrace i d h_known
  | auipc d => exact stepStrong_auipc ziskTrace sailTrace i d h_known
  | jal d => exact stepStrong_jal ziskTrace sailTrace i d h_known
  | jalr d => exact stepStrong_jalr ziskTrace sailTrace i d h_known
  | sb d => exact stepStrong_sb ziskTrace sailTrace i d h_known
  | sh d => exact stepStrong_sh ziskTrace sailTrace i d h_known
  | sw d => exact stepStrong_sw ziskTrace sailTrace i d h_known
  | sd d => exact stepStrong_sd ziskTrace sailTrace i d h_known
  | ld d => exact stepStrong_ld ziskTrace sailTrace i d h_known
  | lbu d => exact stepStrong_lbu ziskTrace sailTrace i d h_known
  | lhu d => exact stepStrong_lhu ziskTrace sailTrace i d h_known
  | lwu d => exact stepStrong_lwu ziskTrace sailTrace i d h_known
  | lb d => exact stepStrong_lb ziskTrace sailTrace i d h_known
  | lh d => exact stepStrong_lh ziskTrace sailTrace i d h_known
  | lw d => exact stepStrong_lw ziskTrace sailTrace i d h_known
  | fence d => exact stepStrong_fence ziskTrace sailTrace i d h_known

end ZiskFv.Compliance
