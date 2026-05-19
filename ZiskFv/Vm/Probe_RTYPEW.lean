import ZiskFv.Compliance.Wrappers.Addw
import ZiskFv.Compliance.Wrappers.Subw
import ZiskFv.Compliance.Wrappers.Addiw
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — RTYPEW family `equiv_<OP>_v2` corollaries

Three v2 wrappers for the W-suffix (32-bit-result) opcodes that pair
with the Binary AIR: ADDW, SUBW, ADDIW.

The shift variants (SLLW, SRLW, SRAW, SLLIW, SRLIW, SRAIW) pair with
BinaryExtension and are deferred to a follow-up file.

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_ADD_W OP_SUB_W)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ADDW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADDW
    state addw_input r1 r2 rd m v r_main bus pins h_lane_rd promises

theorem equiv_SUBW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SUBW
    state subw_input r1 r2 rd m v r_main bus pins h_lane_rd promises

end ZiskFv.Vm.Probe
