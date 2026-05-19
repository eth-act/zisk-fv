import ZiskFv.Compliance.Wrappers.Andi
import ZiskFv.Compliance.Wrappers.Ori
import ZiskFv.Compliance.Wrappers.Xori
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — ITYPE family `equiv_<OP>_v2` corollaries (Binary path)

Three more v2 wrappers covering the ITYPE-shape opcodes that pair
with the Binary AIR: ANDI, ORI, XORI.

ADDI is omitted here because it pairs with BinaryAdd (different
witness bundle, `badd` + `h_main_subset` instead of `v`). It can be
added in a follow-up but follows the same one-line pattern.

Together with `Probe_ADD.lean` (1) and `Probe_RTYPE.lean` (4), this
file brings the total to **8 v2 wrappers** in the stack — a third of
the way to the 35 OpEnvelope arms.

## Trust note

No axioms added. Pure corollaries.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_AND OP_OR OP_XOR)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ANDI_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (andi_input : PureSpec.AndiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_andi_subset : itype_imm_subset_holds_main m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ANDI
    state andi_input r1 rd imm m v r_main bus pins h_andi_subset h_lane_rd promises

theorem equiv_ORI_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ORI
    state ori_input r1 rd imm m v r_main bus pins h_ori_subset h_lane_rd promises

theorem equiv_XORI_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_XORI
    state xori_input r1 rd imm m v r_main bus pins h_xori_subset h_lane_rd promises

end ZiskFv.Vm.Probe
