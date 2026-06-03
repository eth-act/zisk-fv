import Mathlib

import ZiskFv.EquivCore.Lui
import ZiskFv.EquivCore.Promises.UType
import ZiskFv.EquivCore.Promises.UTypeHelpers
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.AeneasRowProvenance

/-!
# `equiv_LUI` Compliance wrapper — Aeneas-provenance route

The wrapper takes the structural `UTypePromises` bundle plus
`MainAeneasRowProvenance` for the selected Aeneas-lowered LUI row. Static
mode/control pins are derived from that provenance, while the canonical
equivalence proof still consumes the remaining dynamic immediate-lane bridge.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype


/-- Aeneas-provenance wrapper for `equiv_LUI`. Static/control pins come from
    a selected row produced by the Aeneas-extracted LUI lowerer. -/
lemma equiv_LUI_of_aeneas_provenance
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (provenance : ZiskFv.Compliance.MainAeneasRowProvenance m r_main inst)
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
    ZiskFv.EquivCore.Promises.lui_h_circuit_of_aeneas_provenance
      m r_main next_pc provenance h_lui_subset
  exact ZiskFv.EquivCore.Lui.equiv_LUI state lui_input imm rd
    m r_main next_pc exec_row e_rd store_pc_mem (lui_input.PC + 4#64)
    promises h_imm_lo_nat h_imm_hi_nat h_circuit

/-- Canonical compliance-wrapper name for LUI. This is intentionally an alias
    of the Aeneas-provenance route for this milestone. -/
lemma equiv_LUI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (provenance : ZiskFv.Compliance.MainAeneasRowProvenance m r_main inst)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  equiv_LUI_of_aeneas_provenance
    state lui_input imm rd m r_main next_pc exec_row e_rd store_pc_mem
    provenance h_lui_subset h_imm_lo_nat h_imm_hi_nat promises

end ZiskFv.Compliance
