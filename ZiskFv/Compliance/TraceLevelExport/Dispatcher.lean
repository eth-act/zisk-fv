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
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) where
  | sub (d : RowData_sub trace binding i) : StrongRowConstructionData trace binding i
  | and (d : RowData_and trace binding i) : StrongRowConstructionData trace binding i
  | or (d : RowData_or trace binding i) : StrongRowConstructionData trace binding i
  | xor (d : RowData_xor trace binding i) : StrongRowConstructionData trace binding i
  | slt (d : RowData_slt trace binding i) : StrongRowConstructionData trace binding i
  | sltu (d : RowData_sltu trace binding i) : StrongRowConstructionData trace binding i
  | andi (d : RowData_andi trace binding i) : StrongRowConstructionData trace binding i
  | ori (d : RowData_ori trace binding i) : StrongRowConstructionData trace binding i
  | xori (d : RowData_xori trace binding i) : StrongRowConstructionData trace binding i
  | slti (d : RowData_slti trace binding i) : StrongRowConstructionData trace binding i
  | sltiu (d : RowData_sltiu trace binding i) : StrongRowConstructionData trace binding i
  | sll (d : RowData_sll trace binding i) : StrongRowConstructionData trace binding i
  | srl (d : RowData_srl trace binding i) : StrongRowConstructionData trace binding i
  | sra (d : RowData_sra trace binding i) : StrongRowConstructionData trace binding i
  | slli (d : RowData_slli trace binding i) : StrongRowConstructionData trace binding i
  | srli (d : RowData_srli trace binding i) : StrongRowConstructionData trace binding i
  | srai (d : RowData_srai trace binding i) : StrongRowConstructionData trace binding i
  | add (d : RowData_add trace binding i) : StrongRowConstructionData trace binding i
  | addi (d : RowData_addi trace binding i) : StrongRowConstructionData trace binding i
  | subw (d : RowData_subw trace binding i) : StrongRowConstructionData trace binding i
  | addw (d : RowData_addw trace binding i) : StrongRowConstructionData trace binding i
  | addiw (d : RowData_addiw trace binding i) : StrongRowConstructionData trace binding i
  | sllw (d : RowData_sllw trace binding i) : StrongRowConstructionData trace binding i
  | srlw (d : RowData_srlw trace binding i) : StrongRowConstructionData trace binding i
  | sraw (d : RowData_sraw trace binding i) : StrongRowConstructionData trace binding i
  | slliw (d : RowData_slliw trace binding i) : StrongRowConstructionData trace binding i
  | srliw (d : RowData_srliw trace binding i) : StrongRowConstructionData trace binding i
  | sraiw (d : RowData_sraiw trace binding i) : StrongRowConstructionData trace binding i
  | mul (d : RowData_mul trace binding i) : StrongRowConstructionData trace binding i
  | mulh (d : RowData_mulh trace binding i) : StrongRowConstructionData trace binding i
  | mulhsu (d : RowData_mulhsu trace binding i) : StrongRowConstructionData trace binding i
  | mulw (d : RowData_mulw trace binding i) : StrongRowConstructionData trace binding i
  | mulhu (d : RowData_mulhu trace binding i) : StrongRowConstructionData trace binding i
  | div (d : RowData_div trace binding i) : StrongRowConstructionData trace binding i
  | rem (d : RowData_rem trace binding i) : StrongRowConstructionData trace binding i
  | divw (d : RowData_divw trace binding i) : StrongRowConstructionData trace binding i
  | remw (d : RowData_remw trace binding i) : StrongRowConstructionData trace binding i
  | divu (d : RowData_divu trace binding i) : StrongRowConstructionData trace binding i
  | divuw (d : RowData_divuw trace binding i) : StrongRowConstructionData trace binding i
  | remu (d : RowData_remu trace binding i) : StrongRowConstructionData trace binding i
  | remuw (d : RowData_remuw trace binding i) : StrongRowConstructionData trace binding i
  | beq (d : RowData_beq trace binding i) : StrongRowConstructionData trace binding i
  | bne (d : RowData_bne trace binding i) : StrongRowConstructionData trace binding i
  | blt (d : RowData_blt trace binding i) : StrongRowConstructionData trace binding i
  | bge (d : RowData_bge trace binding i) : StrongRowConstructionData trace binding i
  | bltu (d : RowData_bltu trace binding i) : StrongRowConstructionData trace binding i
  | bgeu (d : RowData_bgeu trace binding i) : StrongRowConstructionData trace binding i
  | lui (d : RowData_lui trace binding i) : StrongRowConstructionData trace binding i
  | auipc (d : RowData_auipc trace binding i) : StrongRowConstructionData trace binding i
  | jal (d : RowData_jal trace binding i) : StrongRowConstructionData trace binding i
  | jalr (d : RowData_jalr trace binding i) : StrongRowConstructionData trace binding i
  | sb (d : RowData_sb trace binding i) : StrongRowConstructionData trace binding i
  | sh (d : RowData_sh trace binding i) : StrongRowConstructionData trace binding i
  | sw (d : RowData_sw trace binding i) : StrongRowConstructionData trace binding i
  | sd (d : RowData_sd trace binding i) : StrongRowConstructionData trace binding i
  | ld (d : RowData_ld trace binding i) : StrongRowConstructionData trace binding i
  | lbu (d : RowData_lbu trace binding i) : StrongRowConstructionData trace binding i
  | lhu (d : RowData_lhu trace binding i) : StrongRowConstructionData trace binding i
  | lwu (d : RowData_lwu trace binding i) : StrongRowConstructionData trace binding i
  | lb (d : RowData_lb trace binding i) : StrongRowConstructionData trace binding i
  | lh (d : RowData_lh trace binding i) : StrongRowConstructionData trace binding i
  | lw (d : RowData_lw trace binding i) : StrongRowConstructionData trace binding i
  | fence (d : RowData_fence trace binding i) : StrongRowConstructionData trace binding i

/-- Per-row defect-exclusion obligation supplied to (and threaded into) the
    strengthened trace-level export.  For each OpEnvelope-route arm it is the
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
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) :
    StrongRowConstructionData trace binding i → Prop
  | .sub _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sub .. => True | _ => False)
  | .and _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .and .. => True | _ => False)
  | .or _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .or .. => True | _ => False)
  | .xor _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .xor .. => True | _ => False)
  | .slt _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slt .. => True | _ => False)
  | .sltu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sltu .. => True | _ => False)
  | .andi _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .andi .. => True | _ => False)
  | .ori _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .ori .. => True | _ => False)
  | .xori _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .xori .. => True | _ => False)
  | .slti _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slti .. => True | _ => False)
  | .sltiu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sltiu .. => True | _ => False)
  | .sll _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sll .. => True | _ => False)
  | .srl _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srl .. => True | _ => False)
  | .sra _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sra .. => True | _ => False)
  | .slli _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slli .. => True | _ => False)
  | .srli _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srli .. => True | _ => False)
  | .srai _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srai .. => True | _ => False)
  | .add _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with | .add_via_binary .. => True | .add_via_binaryadd .. => True | _ => False)
  | .addi _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with | .addi_via_binary .. => True | .addi_via_binaryadd .. => True | _ => False)
  | .subw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .subw .. => True | _ => False)
  | .addw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .addw .. => True | _ => False)
  | .addiw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .addiw .. => True | _ => False)
  | .sllw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sllw .. => True | _ => False)
  | .srlw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srlw .. => True | _ => False)
  | .sraw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sraw .. => True | _ => False)
  | .slliw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slliw .. => True | _ => False)
  | .srliw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srliw .. => True | _ => False)
  | .sraiw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sraiw .. => True | _ => False)
  | .jalr _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .jalr .. => True | _ => False)
  | .beq _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .beq .. => True | _ => False)
  | .bne _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bne .. => True | _ => False)
  | .blt _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .blt .. => True | _ => False)
  | .bge _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bge .. => True | _ => False)
  | .bltu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bltu .. => True | _ => False)
  | .bgeu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bgeu .. => True | _ => False)
  | .mul d => Defects.NoKnownDefect (mulEnvOf trace binding i d)
  | .mulh d => Defects.NoKnownDefect (mulhEnvOf trace binding i d)
  | .mulhsu d => Defects.NoKnownDefect (mulhsuEnvOf trace binding i d)
  -- Signed DIV/REM/DIVW/REMW: the GENUINE `NoKnownDefect` of the SPECIFIC env,
  -- NOT the (false) selector-∀ shape.  Satisfiable for an honest signed row
  -- (`|r| ≠ |op2|`); see `RowData_div` / `stepStrong_div`.
  | .div d => Defects.NoKnownDefect (divEnvOf trace binding i d)
  | .rem d => Defects.NoKnownDefect (remEnvOf trace binding i d)
  | .divw d => Defects.NoKnownDefect (divwEnvOf trace binding i d)
  | .remw d => Defects.NoKnownDefect (remwEnvOf trace binding i d)
  | .mulw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .mulw .. => True | _ => False)
  | .mulhu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .mulhu .. => True | _ => False)
  | .divu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .divu .. => True | _ => False)
  | .divuw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .divuw .. => True | _ => False)
  | .remu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .remu .. => True | _ => False)
  | .remuw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .remuw .. => True | _ => False)
  | .lui _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .lui .. => True | _ => False)
  | .auipc _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .auipc .. => True | _ => False)
  | .jal _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .jal .. => True | _ => False)
  | .sb _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sb .. => True | _ => False)
  | .sh _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sh .. => True | _ => False)
  | .sw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sw .. => True | _ => False)
  | .sd _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sd .. => True | _ => False)
  | .ld _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .ld .. => True | _ => False)
  | .lbu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .lbu .. => True | _ => False)
  | .lhu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .lhu .. => True | _ => False)
  | .lwu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .lwu .. => True | _ => False)
  | .lb _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with | .lb_via_static_match .. => True | _ => False)
  | .lh _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with | .lh_via_static_match .. => True | _ => False)
  | .lw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with | .lw_via_static_match .. => True | _ => False)
  -- FENCE: the GENUINE `NoKnownDefect` of the SPECIFIC honest env, NOT the
  -- (false) selector-∀ shape.  Satisfiable for an honest FENCE row.
  | .fence d => Defects.NoKnownDefect (fenceEnvOf trace binding i d)

/-- The strengthened per-step conclusion: the channel-balance
    (`state_effect_via_channels`) form — the OLD global theorem's per-arm
    conclusion — keyed on the row archetype. -/
def StepComplianceStrong
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) :
    StrongRowConstructionData trace binding i → Prop
  | .sub d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SUB))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .and d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.AND))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .or d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.OR))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .xor d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.XOR))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slt d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLT))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sltu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLTU))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .andi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ANDI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .ori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ORI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .xori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.XORI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slti d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sltiu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTIU))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sll d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLL)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srl d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRL)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sra d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRA)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SLLI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRLI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srai d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRAI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .add d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.ADD))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .addi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ADDI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .subw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SUBW))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .addw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.ADDW))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .addiw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (d.imm, d.r1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sllw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SLLW)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srlw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRLW)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sraw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRAW)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slliw d =>
      execute_instruction
        (instruction.SHIFTIWOP (d.slliw_input.shamt, d.r1, d.rd, sopw.SLLIW)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srliw d =>
      execute_instruction
        (instruction.SHIFTIWOP (d.srliw_input.shamt, d.r1, d.rd, sopw.SRLIW)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sraiw d =>
      execute_instruction
        (instruction.SHIFTIWOP (d.sraiw_input.shamt, d.r1, d.rd, sopw.SRAIW)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .mul d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.Low
             signed_rs1 := d.srs1
             signed_rs2 := d.srs2 }))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .mulh d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .mulhsu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .div d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, false))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .rem d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, false))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .divw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, false))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .remw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, false))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.bus.exec_row, [d.bus.e0, d.bus.e1, d.bus.e2]⟩ (binding.stateAt i)
  | .mulw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (d.r2, d.r1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .mulhu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .divu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .divuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .remu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .remuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .beq d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BEQ)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bne d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BNE)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .blt d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLT)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bge d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGE)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bltu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLTU)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bgeu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGEU)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .lui d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.LUI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .auipc d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.AUIPC)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .jal d =>
      execute_instruction (instruction.JAL (d.imm, d.rd)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .jalr d =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (d.imm, d.rs1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .sb d =>
      execute_instruction (instruction.STORE
          (d.sb_input.imm, regidx.Regidx d.sb_input.r2, regidx.Regidx d.sb_input.r1, 1))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sh d =>
      execute_instruction (instruction.STORE
          (d.sh_input.imm, regidx.Regidx d.sh_input.r2, regidx.Regidx d.sh_input.r1, 2))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sw d =>
      execute_instruction (instruction.STORE
          (d.sw_input.imm, regidx.Regidx d.sw_input.r2, regidx.Regidx d.sw_input.r1, 4))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sd d =>
      execute_instruction (instruction.STORE
          (d.sd_input.imm, regidx.Regidx d.sd_input.r2, regidx.Regidx d.sd_input.r1, 8))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .ld d =>
      execute_instruction (instruction.LOAD
          (d.ld_input.imm, regidx.Regidx d.ld_input.r1, regidx.Regidx d.ld_input.rd, false, 8))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lbu d =>
      execute_instruction (instruction.LOAD
          (d.lbu_input.imm, regidx.Regidx d.lbu_input.r1, regidx.Regidx d.lbu_input.rd, true, 1))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lhu d =>
      execute_instruction (instruction.LOAD
          (d.lhu_input.imm, regidx.Regidx d.lhu_input.r1, regidx.Regidx d.lhu_input.rd, true, 2))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lwu d =>
      execute_instruction (instruction.LOAD
          (d.lwu_input.imm, regidx.Regidx d.lwu_input.r1, regidx.Regidx d.lwu_input.rd, true, 4))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lb d =>
      execute_instruction (instruction.LOAD
          (d.lb_input.imm, regidx.Regidx d.lb_input.r1, regidx.Regidx d.lb_input.rd, false, 1))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lh d =>
      execute_instruction (instruction.LOAD
          (d.lh_input.imm, regidx.Regidx d.lh_input.r1, regidx.Regidx d.lh_input.rd, false, 2))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lw d =>
      execute_instruction (instruction.LOAD
          (d.lw_input.imm, regidx.Regidx d.lw_input.r1, regidx.Regidx d.lw_input.rd, false, 4))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .fence d =>
      execute_instruction (instruction.FENCE (d.fm, d.fenceP, d.fenceS, d.rs, d.rd)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)

/-- Per-row dispatch to the matching strengthened step theorem.

    The `h_known` parameter carries the per-row defect-exclusion obligation
    (`StepNoKnownDefect`).  For the 22 OpEnvelope-route arms it is the
    `EnvNoKnownDefectFor` fact for that arm's constructor; the dispatcher hands it
    straight to the corresponding `stepStrong_<op>`, which feeds it to
    `zisk_riscv_compliant_program_bus`.  For the direct-lift arms (which never call
    the old theorem) the obligation is `True` and is ignored. -/
theorem stepComplianceStrong_of_rowData
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (d : StrongRowConstructionData trace binding i)
    (h_known : StepNoKnownDefect trace binding i d) :
    StepComplianceStrong trace binding i d := by
  cases d with
  | sub d => exact stepStrong_sub trace binding i d h_known
  | and d => exact stepStrong_and trace binding i d h_known
  | or d => exact stepStrong_or trace binding i d h_known
  | xor d => exact stepStrong_xor trace binding i d h_known
  | slt d => exact stepStrong_slt trace binding i d h_known
  | sltu d => exact stepStrong_sltu trace binding i d h_known
  | andi d => exact stepStrong_andi trace binding i d h_known
  | ori d => exact stepStrong_ori trace binding i d h_known
  | xori d => exact stepStrong_xori trace binding i d h_known
  | slti d => exact stepStrong_slti trace binding i d h_known
  | sltiu d => exact stepStrong_sltiu trace binding i d h_known
  | sll d => exact stepStrong_sll trace binding i d h_known
  | srl d => exact stepStrong_srl trace binding i d h_known
  | sra d => exact stepStrong_sra trace binding i d h_known
  | slli d => exact stepStrong_slli trace binding i d h_known
  | srli d => exact stepStrong_srli trace binding i d h_known
  | srai d => exact stepStrong_srai trace binding i d h_known
  | add d => exact stepStrong_add trace binding i d h_known
  | addi d => exact stepStrong_addi trace binding i d h_known
  | subw d => exact stepStrong_subw trace binding i d h_known
  | addw d => exact stepStrong_addw trace binding i d h_known
  | addiw d => exact stepStrong_addiw trace binding i d h_known
  | sllw d => exact stepStrong_sllw trace binding i d h_known
  | srlw d => exact stepStrong_srlw trace binding i d h_known
  | sraw d => exact stepStrong_sraw trace binding i d h_known
  | slliw d => exact stepStrong_slliw trace binding i d h_known
  | srliw d => exact stepStrong_srliw trace binding i d h_known
  | sraiw d => exact stepStrong_sraiw trace binding i d h_known
  | mul d => exact stepStrong_mul trace binding i d h_known
  | mulh d => exact stepStrong_mulh trace binding i d h_known
  | mulhsu d => exact stepStrong_mulhsu trace binding i d h_known
  | div d => exact stepStrong_div trace binding i d h_known
  | rem d => exact stepStrong_rem trace binding i d h_known
  | divw d => exact stepStrong_divw trace binding i d h_known
  | remw d => exact stepStrong_remw trace binding i d h_known
  | mulw d => exact stepStrong_mulw trace binding i d h_known
  | mulhu d => exact stepStrong_mulhu trace binding i d h_known
  | divu d => exact stepStrong_divu trace binding i d h_known
  | divuw d => exact stepStrong_divuw trace binding i d h_known
  | remu d => exact stepStrong_remu trace binding i d h_known
  | remuw d => exact stepStrong_remuw trace binding i d h_known
  | beq d => exact stepStrong_beq trace binding i d h_known
  | bne d => exact stepStrong_bne trace binding i d h_known
  | blt d => exact stepStrong_blt trace binding i d h_known
  | bge d => exact stepStrong_bge trace binding i d h_known
  | bltu d => exact stepStrong_bltu trace binding i d h_known
  | bgeu d => exact stepStrong_bgeu trace binding i d h_known
  | lui d => exact stepStrong_lui trace binding i d h_known
  | auipc d => exact stepStrong_auipc trace binding i d h_known
  | jal d => exact stepStrong_jal trace binding i d h_known
  | jalr d => exact stepStrong_jalr trace binding i d h_known
  | sb d => exact stepStrong_sb trace binding i d h_known
  | sh d => exact stepStrong_sh trace binding i d h_known
  | sw d => exact stepStrong_sw trace binding i d h_known
  | sd d => exact stepStrong_sd trace binding i d h_known
  | ld d => exact stepStrong_ld trace binding i d h_known
  | lbu d => exact stepStrong_lbu trace binding i d h_known
  | lhu d => exact stepStrong_lhu trace binding i d h_known
  | lwu d => exact stepStrong_lwu trace binding i d h_known
  | lb d => exact stepStrong_lb trace binding i d h_known
  | lh d => exact stepStrong_lh trace binding i d h_known
  | lw d => exact stepStrong_lw trace binding i d h_known
  | fence d => exact stepStrong_fence trace binding i d h_known

end ZiskFv.Compliance
