import ZiskFv.Compliance_v1
import ZiskFv.Vm.Probe_ITYPE
import ZiskFv.Vm.Probe_Compare

/-!
# Phase 5 partial — Compliance_v2 dispatcher (ITYPE+Binary arms)

Extends to ITYPE+Binary: ANDI, ORI, XORI, SLTI, SLTIU.

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

def OpEnvelope.exec_eq_v2_itype_binary
    : OpEnvelope state m r_main → Prop
  | .andi _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .ori _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .xori _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slti _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sltiu _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_v2_itype_binary
    (env : OpEnvelope state m r_main) :
    env.exec_eq_v2_itype_binary := by
  cases env with
  | andi andi_input r1 rd imm v bus pins h_andi_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_itype_binary]
    exact equiv_ANDI_v2 state andi_input r1 rd imm m v r_main bus pins
      h_andi_subset h_lane_rd promises
  | ori ori_input r1 rd imm v bus pins h_ori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_itype_binary]
    exact equiv_ORI_v2 state ori_input r1 rd imm m v r_main bus pins
      h_ori_subset h_lane_rd promises
  | xori xori_input r1 rd imm v bus pins h_xori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_itype_binary]
    exact equiv_XORI_v2 state xori_input r1 rd imm m v r_main bus pins
      h_xori_subset h_lane_rd promises
  | slti slti_input r1 rd imm v bus pins h_slti_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_itype_binary]
    exact equiv_SLTI_v2 state slti_input r1 rd imm m v r_main bus pins
      h_slti_subset h_lane_rd promises
  | sltiu sltiu_input r1 rd imm v bus pins h_sltiu_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_itype_binary]
    exact equiv_SLTIU_v2 state sltiu_input r1 rd imm m v r_main bus pins
      h_sltiu_subset h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
