import Mathlib

import ZiskFv.Equivalence.Lui
import ZiskFv.Equivalence.Promises.UType
import ZiskFv.Equivalence.Promises.UTypeHelpers
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LUI` Compliance wrapper — ControlFlow non-branch shape exemplar

The wrapper takes the structural `UTypePromises` bundle along with the
upstream activation/opcode pins and the per-row LUI subset constraint,
and internally calls `lui_h_circuit_of_main_constraints` (which
transitively consumes `transpile_LUI`) to derive `h_circuit`. This keeps
`transpile_LUI` transitively reachable from the global compliance
theorem.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_LUI`.** Derives `h_circuit` from
    `lui_h_circuit_of_main_constraints` (consuming `transpile_LUI`)
    and delegates to canonical `equiv_LUI`. -/
theorem equiv_LUI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins on Main + per-row subset constraint
    -- (consumed by the UTypeHelpers helper that fires `transpile_LUI`).
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    -- Structural `UTypePromises` bundle.
    (promises : ZiskFv.Equivalence.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.Equivalence.Promises.lui_h_circuit_of_main_constraints
      m r_main next_pc pins.main_active pins.main_op h_lui_subset
  ZiskFv.Equivalence.Lui.equiv_LUI state lui_input imm rd
    m r_main next_pc exec_row e_rd (lui_input.PC + 4#64)
    promises h_circuit

end ZiskFv.Compliance
