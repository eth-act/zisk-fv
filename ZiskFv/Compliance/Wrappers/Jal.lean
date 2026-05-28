import Mathlib

import ZiskFv.EquivCore.Jal
import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.EquivCore.Promises.JumpHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_JAL` Compliance wrapper — ControlFlow non-branch

The wrapper takes the structural `JumpPromises` bundle along with the
upstream activation/opcode pins on Main and the per-row JAL subset
constraint, and internally calls `jal_h_circuit_of_main_constraints`
(which transitively consumes `transpile_JAL`) to derive `h_circuit`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main


/-- **Compliance wrapper for `equiv_JAL`.** Derives `h_circuit` from
    `jal_h_circuit_of_main_constraints` (consuming `transpile_JAL`)
    and delegates to canonical `equiv_JAL`. -/
theorem equiv_JAL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    -- Activation / opcode pins on Main + per-row subset constraint.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    -- Structural `JumpPromises` bundle.
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.EquivCore.Promises.jal_h_circuit_of_main_constraints
      m r_main next_pc pins.main_active pins.main_op h_jal_subset
  ZiskFv.EquivCore.Jal.equiv_JAL state jal_input imm rd misa_val
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_input_imm h_not_throws
    h_circuit h_pc_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
