import Mathlib

import ZiskFv.EquivCore.Auipc
import ZiskFv.EquivCore.Promises.UType
import ZiskFv.EquivCore.Promises.UTypeHelpers
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_AUIPC` Compliance wrapper — ControlFlow non-branch

The wrapper takes the structural `UTypePromises` bundle along with the
upstream activation/opcode pins and the per-row AUIPC subset
constraint, and internally calls `auipc_h_circuit_of_main_constraints`
(which transitively consumes `transpile_AUIPC`) to derive `h_circuit`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype


/-- **Compliance wrapper for `equiv_AUIPC`.** Derives `h_circuit` from
    `auipc_h_circuit_of_main_constraints` (consuming `transpile_AUIPC`)
    and delegates to canonical `equiv_AUIPC`. -/
theorem equiv_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    -- Activation / opcode pins on Main + per-row subset constraint.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    -- Structural `UTypePromises` bundle.
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.EquivCore.Promises.auipc_h_circuit_of_main_constraints
      m r_main next_pc pins.main_active pins.main_op h_auipc_subset
  ZiskFv.EquivCore.Auipc.equiv_AUIPC state auipc_input imm rd
    exec_row e_rd nextPC_val m r_main next_pc
    promises h_circuit h_no_wrap h_pc_offset_lt_2_32

end ZiskFv.Compliance
