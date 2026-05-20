import ZiskFv.Compliance_v1
import ZiskFv.Vm.Probe_Shift
import ZiskFv.Vm.Probe_ShiftRight

/-!
# Phase 5 partial — Compliance_v2 dispatcher (Shift arms)

Extends to the 6 shift arms (SLL, SRL, SRA, SLLI, SRLI, SRAI) which
pair with the BinaryExtension AIR.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Vm
open ZiskFv.Vm.Probe
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

def OpEnvelope.exec_eq_v2_shift
    : OpEnvelope state m r_main → Prop
  | .sll _ r1 r2 rd _ bus _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srl _ r1 r2 rd _ bus _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sra _ r1 r2 rd _ bus _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slli _ r1 rd shamt _ bus _ _ _ =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srli _ r1 rd shamt _ bus _ _ _ =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srai _ r1 rd shamt _ bus _ _ _ =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_v2_shift
    (env : OpEnvelope state m r_main) :
    env.exec_eq_v2_shift := by
  cases env with
  | sll sll_input r1 r2 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq_v2_shift]
    exact equiv_SLL_v2 state sll_input r1 r2 rd m v r_main bus promises pins h_lane_rd
  | srl srl_input r1 r2 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq_v2_shift]
    exact equiv_SRL_v2 state srl_input r1 r2 rd m v r_main bus promises pins h_lane_rd
  | sra sra_input r1 r2 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq_v2_shift]
    exact equiv_SRA_v2 state sra_input r1 r2 rd m v r_main bus promises pins h_lane_rd
  | slli slli_input r1 rd shamt v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq_v2_shift]
    exact equiv_SLLI_v2 state slli_input r1 rd shamt m v r_main bus promises pins h_lane_rd
  | srli srli_input r1 rd shamt v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq_v2_shift]
    exact equiv_SRLI_v2 state srli_input r1 rd shamt m v r_main bus promises pins h_lane_rd
  | srai srai_input r1 rd shamt v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq_v2_shift]
    exact equiv_SRAI_v2 state srai_input r1 rd shamt m v r_main bus promises pins h_lane_rd
  | _ => trivial

end ZiskFv.Compliance
