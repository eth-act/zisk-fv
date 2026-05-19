import ZiskFv.Compliance
import ZiskFv.Vm.Probe_ADD
import ZiskFv.Vm.Probe_RTYPEW

/-!
# Phase 5 partial — Compliance_v2 dispatcher (ADD + RTYPEW arms)

ADD (RTYPE+BinaryAdd) plus ADDW, SUBW (RTYPEW+Binary).

ADDI omitted — has additional `h_main_subset` + `h_addi_subset`
hypotheses making the arm signature longer. Mechanical follow-up.

ADDIW omitted — similar.

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

def OpEnvelope.exec_eq_v2_add_rtypew
    : OpEnvelope (C := C) state m r_main → Prop
  | .add _ r1 r2 rd _ bus _ _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .addw _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .subw _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_v2_add_rtypew
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq_v2_add_rtypew := by
  cases env with
  | add add_input r1 r2 rd badd bus pins h_main_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_add_rtypew]
    exact equiv_ADD_v2 state add_input r1 r2 rd m badd r_main bus pins
      h_main_subset h_lane_rd promises
  | addw addw_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_add_rtypew]
    exact equiv_ADDW_v2 state addw_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | subw subw_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_add_rtypew]
    exact equiv_SUBW_v2 state subw_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
