import Mathlib

import ZiskFv.EquivCore.Lui
import ZiskFv.EquivCore.Promises.UType
import ZiskFv.EquivCore.Promises.UTypeHelpers
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.RowProvenance

/-!
# `equiv_LUI` Compliance wrapper

The wrapper takes the structural `UTypePromises` bundle plus explicit Main-row
mode/control pins. The canonical equivalence proof still consumes the remaining
dynamic immediate-lane bridge.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype


/-- Compliance wrapper for `equiv_LUI`. -/
lemma equiv_LUI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_store_pc : m.store_pc r_main = 0)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_circuit :=
    ZiskFv.EquivCore.Promises.lui_h_circuit_of_main_constraints
      m r_main next_pc pins.main_active pins.main_op
      h_m32 h_set_pc h_store_pc h_lui_subset
  exact ZiskFv.EquivCore.Lui.equiv_LUI state lui_input imm rd
    m r_main next_pc exec_row e_rd store_pc_mem (lui_input.PC + 4#64)
    promises h_imm_lo_nat h_imm_hi_nat h_circuit

/-- Row-provenance wrapper for `equiv_LUI`. The mode pins come from a
    selected production-extracted row shape; the dynamic immediate-lane facts
    remain explicit caller obligations. -/
lemma equiv_LUI_of_row_provenance
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (row_mode : ZiskFv.Compliance.MainRowProvenance.LuiRowMode provenance)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_circuit :=
    ZiskFv.EquivCore.Promises.lui_h_circuit_of_row_provenance
      m r_main next_pc provenance row_mode h_lui_subset
  exact ZiskFv.EquivCore.Lui.equiv_LUI state lui_input imm rd
    m r_main next_pc exec_row e_rd store_pc_mem (lui_input.PC + 4#64)
    promises h_imm_lo_nat h_imm_hi_nat h_circuit

end ZiskFv.Compliance
