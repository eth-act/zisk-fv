import ZiskFv.Compliance.Wrappers.Addi
import ZiskFv.Compliance.Wrappers.Addiw
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — ADDI / ADDIW v2 corollaries

ADDI (BinaryAdd-paired, ITYPE shape with add_subset + itype_imm_subset).
ADDIW (Binary-paired, ITYPE-W shape with itype_imm_subset).

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main add_subset_holds)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open ZiskFv.Trusted (OP_ADD OP_ADD_W)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ADDI_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (badd : ZiskFv.Compliance.BinaryAddWitness C)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADDI state addi_input r1 rd imm m badd r_main bus
    pins h_main_subset h_addi_subset h_lane_rd promises

theorem equiv_ADDIW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (imm, r1, rd))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADDIW state addiw_input r1 rd imm m v r_main bus
    pins h_addiw_subset h_lane_rd promises

end ZiskFv.Vm.Probe
