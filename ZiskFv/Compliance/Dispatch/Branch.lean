import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Beq
import ZiskFv.Equivalence.Bge
import ZiskFv.Equivalence.Bgeu
import ZiskFv.Equivalence.Blt
import ZiskFv.Equivalence.Bltu
import ZiskFv.Equivalence.Bne

/-!
# Compliance dispatcher (Branch arms)

One of the ten per-family dispatchers aggregated by `Compliance.lean`.
Defines a per-arm `OpEnvelope.exec_eq_branch` Prop expressing the
channel-balance conclusion, plus `zisk_riscv_compliant_program_bus_branch`,
which discharges each of the 6 branch arms (BEQ, BNE, BLT, BGE, BLTU,
BGEU) by invoking the corresponding canonical `Equivalence.<Op>.equiv_<OP>`
theorem; non-branch arms fall through to `True`.

## Trust note

No new axioms. The dispatcher's closure is the union of the 6 branch
canonical theorems' closures.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- The per-arm channel-balance conclusion Prop for Branch arms.
    Falls through to `True` for non-branch arms. -/
def OpEnvelope.exec_eq_branch
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
    `exec_eq_branch` is `True` and trivially holds. -/
theorem zisk_riscv_compliant_program_bus_branch
    (env : OpEnvelope state m r_main) :
    env.exec_eq_branch := by
  cases env with
  | beq beq_input ops promises =>
    simp only [OpEnvelope.exec_eq_branch]
    exact ZiskFv.Equivalence.Beq.equiv_BEQ state beq_input ops promises
  | bne bne_input ops promises =>
    simp only [OpEnvelope.exec_eq_branch]
    exact ZiskFv.Equivalence.Bne.equiv_BNE state bne_input ops promises
  | blt blt_input ops promises =>
    simp only [OpEnvelope.exec_eq_branch]
    exact ZiskFv.Equivalence.Blt.equiv_BLT state blt_input ops promises
  | bge bge_input ops promises =>
    simp only [OpEnvelope.exec_eq_branch]
    exact ZiskFv.Equivalence.Bge.equiv_BGE state bge_input ops promises
  | bltu bltu_input ops promises =>
    simp only [OpEnvelope.exec_eq_branch]
    exact ZiskFv.Equivalence.Bltu.equiv_BLTU state bltu_input ops promises
  | bgeu bgeu_input ops promises =>
    simp only [OpEnvelope.exec_eq_branch]
    exact ZiskFv.Equivalence.Bgeu.equiv_BGEU state bgeu_input ops promises
  -- All non-branch arms: `exec_eq_branch = True`.
  | _ => trivial

end ZiskFv.Compliance
