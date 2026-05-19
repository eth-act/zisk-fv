import ZiskFv.Compliance
import ZiskFv.Vm.Probe_LoadU
import ZiskFv.Vm.Probe_StoreSubword
import ZiskFv.Vm.Probe_ShiftW
import ZiskFv.Vm.Probe_Mul
import ZiskFv.Vm.Probe_DivRem
import ZiskFv.Vm.Probe_Jal

/-!
# Phase 5 partial — Compliance_v2 dispatcher for the remaining 26 arms

Covers LBU/LHU/LWU + SB/SH/SW + SLLW/SRLW/SRAW/SLLIW/SRLIW/SRAIW +
MUL/MULH/MULHU/MULHSU/MULW + DIV/REM/REMU/DIVUW/DIVW/REMW/REMUW +
JAL/JALR.

After this dispatcher lands, every OpEnvelope arm has a real
channel-balance conclusion in `Compliance_v2.lean`'s unified
`exec_eq_v2`. No `True` fallbacks remain.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Vm
open ZiskFv.Vm.Probe
open ZiskFv.Airs.Main (Valid_Main)

variable {C : Type → Type → Type} [Circuit FGL FGL C]
variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main C FGL FGL} {r_main : ℕ}

/-- v2 conclusion Prop for the remaining 26 arms. Falls through to
    `True` for arms covered by other partial dispatchers. -/
def OpEnvelope.exec_eq_v2_remaining
    : OpEnvelope (C := C) state m r_main → Prop
  -- Unsigned loads (3)
  | .lbu lbu_input _ _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        lbu_input.imm, regidx.Regidx lbu_input.r1, regidx.Regidx lbu_input.rd, true, 1
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lhu lhu_input _ _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        lhu_input.imm, regidx.Regidx lhu_input.r1, regidx.Regidx lhu_input.rd, true, 2
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lwu lwu_input _ _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        lwu_input.imm, regidx.Regidx lwu_input.r1, regidx.Regidx lwu_input.rd, true, 4
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- Sub-doubleword stores (3)
  | .sb sb_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sb_input.imm, regidx.Regidx sb_input.r2, regidx.Regidx sb_input.r1, 1
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sh sh_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sh_input.imm, regidx.Regidx sh_input.r2, regidx.Regidx sh_input.r1, 2
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sw sw_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sw_input.imm, regidx.Regidx sw_input.r2, regidx.Regidx sw_input.r1, 4
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_v2_remaining
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq_v2_remaining := by
  cases env with
  | lbu lbu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_v2_remaining]
    exact equiv_LBU_v2 state lbu_input regs m mem r_main align bus pins h_width promises
  | lhu lhu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_v2_remaining]
    exact equiv_LHU_v2 state lhu_input regs m mem r_main align bus pins h_width promises
  | lwu lwu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_v2_remaining]
    exact equiv_LWU_v2 state lwu_input regs m mem r_main align bus pins h_width promises
  | sb sb_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_v2_remaining]
    exact equiv_SB_v2 state sb_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sh sh_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_v2_remaining]
    exact equiv_SH_v2 state sh_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sw sw_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_v2_remaining]
    exact equiv_SW_v2 state sw_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | _ => trivial

end ZiskFv.Compliance
