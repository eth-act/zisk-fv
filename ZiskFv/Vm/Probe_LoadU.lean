import ZiskFv.Compliance.Wrappers.Lbu
import ZiskFv.Compliance.Wrappers.Lhu
import ZiskFv.Compliance.Wrappers.Lwu
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — unsigned-load family equiv_<OP>_v2 corollaries

LBU, LHU, LWU — unsigned-load opcodes that pair with Mem + MemAlign*
and use ModeRegsFull. Shape: 3-mem-row bus.

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Vm.Probe


theorem equiv_LBU_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm, regidx.Regidx lbu_input.r1, regidx.Regidx lbu_input.rd, true, 1
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LBU state lbu_input regs main mem r_main align bus pins h_width promises

theorem equiv_LHU_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm, regidx.Regidx lhu_input.r1, regidx.Regidx lhu_input.rd, true, 2
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LHU state lhu_input regs main mem r_main align bus pins h_width promises

theorem equiv_LWU_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (4 : FGL))
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lwu_state_assumptions lwu_input state)
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm, regidx.Regidx lwu_input.r1, regidx.Regidx lwu_input.rd, true, 4
    )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LWU state lwu_input regs main mem r_main align bus pins h_width promises

end ZiskFv.Vm.Probe
