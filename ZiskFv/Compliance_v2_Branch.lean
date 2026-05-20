import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Beq
import ZiskFv.Equivalence.Bge
import ZiskFv.Equivalence.Bgeu
import ZiskFv.Equivalence.Blt
import ZiskFv.Equivalence.Bltu
import ZiskFv.Equivalence.Bne

/-!
# Phase 5 partial — Compliance_v2 dispatcher (Branch arms only)

Demonstrates the Phase 5 architectural shape: a per-arm
`OpEnvelope.exec_eq_v2_branch` Prop expressing the v2 (channel-balance)
conclusion, plus a `zisk_riscv_compliant_program_bus_v2_branch`
dispatcher that uses the v2 probes.

This is a **partial** demo covering only the 6 branch OpEnvelope arms
(BEQ, BNE, BLT, BGE, BLTU, BGEU). The pattern extends mechanically to
all 35 arms once the corresponding v2 probes exist.

## Trust note

No new axioms. The dispatcher's closure is the union of the v2 probes'
closures, which equals the union of the v1 wrappers' closures + the
trivial `state_effect_via_channels_eq_bus_effect_2` bridge.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Vm
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- The per-arm v2 conclusion Prop for Branch arms only.
    Falls through to `True` for non-branch arms (the partial demo). -/
def OpEnvelope.exec_eq_v2_branch
    : OpEnvelope state m r_main → Prop
  | .beq _ ops _ =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BEQ)) state
        = state_effect_via_channels ⟨ops.exec_row, []⟩ state
  | .bne _ ops _ =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BNE)) state
        = state_effect_via_channels ⟨ops.exec_row, []⟩ state
  | .blt _ ops _ =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLT)) state
        = state_effect_via_channels ⟨ops.exec_row, []⟩ state
  | .bge _ ops _ =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGE)) state
        = state_effect_via_channels ⟨ops.exec_row, []⟩ state
  | .bltu _ ops _ =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLTU)) state
        = state_effect_via_channels ⟨ops.exec_row, []⟩ state
  | .bgeu _ ops _ =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGEU)) state
        = state_effect_via_channels ⟨ops.exec_row, []⟩ state
  | _ => True

/-- Partial v2 dispatcher: for any of the 6 branch arms, the channel-
    balance form of the conclusion holds. For other arms,
    `exec_eq_v2_branch` is `True` and trivially holds. -/
theorem zisk_riscv_compliant_program_bus_v2_branch
    (env : OpEnvelope state m r_main) :
    env.exec_eq_v2_branch := by
  cases env with
  | beq beq_input ops promises =>
    simp only [OpEnvelope.exec_eq_v2_branch]
    exact ZiskFv.Equivalence.Beq.equiv_BEQ state beq_input ops promises
  | bne bne_input ops promises =>
    simp only [OpEnvelope.exec_eq_v2_branch]
    exact ZiskFv.Equivalence.Bne.equiv_BNE state bne_input ops promises
  | blt blt_input ops promises =>
    simp only [OpEnvelope.exec_eq_v2_branch]
    exact ZiskFv.Equivalence.Blt.equiv_BLT state blt_input ops promises
  | bge bge_input ops promises =>
    simp only [OpEnvelope.exec_eq_v2_branch]
    exact ZiskFv.Equivalence.Bge.equiv_BGE state bge_input ops promises
  | bltu bltu_input ops promises =>
    simp only [OpEnvelope.exec_eq_v2_branch]
    exact ZiskFv.Equivalence.Bltu.equiv_BLTU state bltu_input ops promises
  | bgeu bgeu_input ops promises =>
    simp only [OpEnvelope.exec_eq_v2_branch]
    exact ZiskFv.Equivalence.Bgeu.equiv_BGEU state bgeu_input ops promises
  -- All non-branch arms: `exec_eq_v2_branch = True`.
  | _ => trivial

end ZiskFv.Compliance
