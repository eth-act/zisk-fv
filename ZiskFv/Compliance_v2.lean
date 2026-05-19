import ZiskFv.Compliance_v2_Branch
import ZiskFv.Compliance_v2_NoMemOrSimple
import ZiskFv.Compliance_v2_RTYPE
import ZiskFv.Compliance_v2_ITYPE
import ZiskFv.Compliance_v2_Shift
import ZiskFv.Compliance_v2_ADD_RTYPEW
import ZiskFv.Compliance_v2_LDSD
import ZiskFv.Compliance_v2_DIVU
import ZiskFv.Compliance_v2_Misc
import ZiskFv.Compliance_v2_Remaining

/-!
# Compliance_v2 — unified channel-balance global theorem

This file aggregates all the partial Phase 5 dispatchers
(`Compliance_v2_<Family>.lean`) into one top-level v2 global theorem.

The aggregation strategy: `OpEnvelope.exec_eq_v2` is the conjunction
of the per-family v2 conclusions. For any OpEnvelope arm, *exactly
one* partial `exec_eq_v2_<family>` produces the real v2 statement;
the others return `True`. The conjunction of all is therefore
exactly "this arm's v2 statement holds".

The unified theorem `zisk_riscv_compliant_program_bus_v2` proves
this conjunction by invoking each partial dispatcher in turn.

## Coverage (32 OpEnvelope arms)

| Family file                      | Arms covered                                      |
|----------------------------------|---------------------------------------------------|
| `Compliance_v2_Branch.lean`      | BEQ, BNE, BLT, BGE, BLTU, BGEU (6)                |
| `Compliance_v2_NoMemOrSimple`    | LUI, AUIPC, FENCE (3)                             |
| `Compliance_v2_RTYPE.lean`       | SUB, AND, OR, XOR, SLT, SLTU (6)                  |
| `Compliance_v2_ITYPE.lean`       | ANDI, ORI, XORI, SLTI, SLTIU (5)                  |
| `Compliance_v2_Shift.lean`       | SLL, SRL, SRA, SLLI, SRLI, SRAI (6)               |
| `Compliance_v2_ADD_RTYPEW.lean`  | ADD, ADDW, SUBW (3)                               |
| `Compliance_v2_LDSD.lean`        | LD, SD (2)                                        |
| `Compliance_v2_DIVU.lean`        | DIVU (1)                                          |
| **Total**                        | **32**                                            |

Remaining arms (not yet covered): ADDI, ADDIW, SLLW/SRLW/SRAW,
SLLIW/SRLIW/SRAIW, JAL, JALR, 6 more loads (LB/LH/LW/LBU/LHU/LWU),
3 more stores (SB/SH/SW), 12 more Arith (MUL/MULH/MULHU/MULHSU/MULW,
DIV/REM/REMU, DIVW/DIVUW/REMW/REMUW). Each is a mechanical
extension following the same pattern.

## Trust note

No new axioms — the closure is exactly the union of the v1 wrappers'
closures plus the trivial `state_effect_via_channels_eq_bus_effect_2`
bridge. V2 trust gate enforces this.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {C : Type → Type → Type} [Circuit FGL FGL C]
variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main C FGL FGL} {r_main : ℕ}

/-- Unified per-arm v2 conclusion: conjunction of the eight family-
    specific exec_eq_v2_<family> Props. Exactly one family fires
    non-trivially for any given arm; the others are `True`. -/
def OpEnvelope.exec_eq_v2 (env : OpEnvelope (C := C) state m r_main) : Prop :=
  env.exec_eq_v2_branch
    ∧ env.exec_eq_v2_nomem
    ∧ env.exec_eq_v2_rtype_binary
    ∧ env.exec_eq_v2_itype_binary
    ∧ env.exec_eq_v2_shift
    ∧ env.exec_eq_v2_add_rtypew
    ∧ env.exec_eq_v2_ldsd
    ∧ env.exec_eq_v2_divu
    ∧ env.exec_eq_v2_misc
    ∧ env.exec_eq_v2_remaining

/-- **Channel-balance global theorem (partial).**

    For any `OpEnvelope` arm covered by the 32 partial dispatchers,
    the channel-balance form of the conclusion holds. The trust
    footprint equals the union of the corresponding v1 wrappers'
    closures plus the trivial bridge — zero new axioms.

    Once all OpEnvelope arms have v2 probes, this theorem subsumes
    `zisk_riscv_compliant_program_bus` and the v1 layer can be
    retired (Phase 6 cutover). -/
theorem zisk_riscv_compliant_program_bus_v2
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq_v2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_v2_branch env
  · exact zisk_riscv_compliant_program_bus_v2_nomem env
  · exact zisk_riscv_compliant_program_bus_v2_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_v2_itype_binary env
  · exact zisk_riscv_compliant_program_bus_v2_shift env
  · exact zisk_riscv_compliant_program_bus_v2_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_v2_ldsd env
  · exact zisk_riscv_compliant_program_bus_v2_divu env
  · exact zisk_riscv_compliant_program_bus_v2_misc env
  · exact zisk_riscv_compliant_program_bus_v2_remaining env

end ZiskFv.Compliance
