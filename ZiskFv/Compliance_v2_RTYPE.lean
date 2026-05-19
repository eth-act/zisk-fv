import ZiskFv.Compliance
import ZiskFv.Vm.Probe_RTYPE
import ZiskFv.Vm.Probe_Compare

/-!
# Phase 5 partial — Compliance_v2 dispatcher (RTYPE+Binary arms)

Extends the dispatcher pattern to the RTYPE+Binary family: SUB, AND,
OR, XOR, SLT, SLTU. Same shape (Valid_Binary + BusRows with 3 mem
entries), same one-line proof body via the v2 probes.

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

/-- The per-arm v2 conclusion Prop for RTYPE+Binary arms.
    Falls through to `True` for non-RTYPE-Binary arms. -/
def OpEnvelope.exec_eq_v2_rtype_binary
    : OpEnvelope (C := C) state m r_main → Prop
  | .sub _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .and _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.AND))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .or _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.OR))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .xor _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slt _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sltu _ r1 r2 rd _ bus _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

/-- Partial v2 dispatcher for RTYPE+Binary arms. -/
theorem zisk_riscv_compliant_program_bus_v2_rtype_binary
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq_v2_rtype_binary := by
  cases env with
  | sub sub_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_rtype_binary]
    exact equiv_SUB_v2 state sub_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | and and_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_rtype_binary]
    exact equiv_AND_v2 state and_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | or or_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_rtype_binary]
    exact equiv_OR_v2 state or_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | xor xor_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_rtype_binary]
    exact equiv_XOR_v2 state xor_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | slt slt_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_rtype_binary]
    exact equiv_SLT_v2 state slt_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | sltu sltu_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_v2_rtype_binary]
    exact equiv_SLTU_v2 state sltu_input r1 r2 rd m v r_main bus pins h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
