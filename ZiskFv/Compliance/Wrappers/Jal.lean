import Mathlib

import ZiskFv.EquivCore.Jal
import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.EquivCore.Promises.JumpHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.RowProvenance

/-!
# `equiv_JAL` Compliance wrapper — ControlFlow non-branch

The wrapper takes the structural `JumpPromises` bundle along with the
upstream activation/opcode/mode pins on Main and the per-row JAL subset
constraint, then delegates to canonical `equiv_JAL`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

/-- Compliance wrapper for the JAL `rd = x0` no-memory shape. -/
lemma equiv_JAL_x0_no_memory
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (nextPC_val : BitVec 64)
    (promises : ZiskFv.EquivCore.Promises.JumpNoMemPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [] state).2 :=
  ZiskFv.EquivCore.Jal.equiv_JAL_x0_no_memory
    state jal_input imm rd misa_val exec_row nextPC_val
    promises h_input_imm h_not_throws

/-- **Compatibility wrapper for `equiv_JAL`.** Derives `h_circuit` from
    explicit Main-row pins and delegates to canonical `equiv_JAL`. -/
lemma equiv_JAL
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
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_store_pc : m.store_pc r_main = 1)
    (h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_pc_bridge : (m.pc r_main).val = jal_input.PC.toNat)
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
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_circuit :=
    ZiskFv.EquivCore.Promises.jal_h_circuit_of_main_constraints
      m r_main next_pc pins.main_active pins.main_op
      h_m32 h_set_pc h_store_pc h_jal_subset
  exact ZiskFv.EquivCore.Jal.equiv_JAL state jal_input imm rd misa_val
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_input_imm h_not_throws
    h_circuit h_jmp2 h_pc_bridge h_pc_bound h_pc_offset_lt_2_32

/-- Row-provenance wrapper for the JAL rd-write route. The mode pins come from
    a selected production-extracted row shape. -/
lemma equiv_JAL_of_row_provenance
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
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (row_mode : ZiskFv.Compliance.MainRowProvenance.JalRowMode provenance)
    (h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_pc_bridge : (m.pc r_main).val = jal_input.PC.toNat)
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
    ZiskFv.EquivCore.Promises.jal_h_circuit_of_row_provenance
      m r_main next_pc provenance row_mode h_jal_subset
  ZiskFv.EquivCore.Jal.equiv_JAL state jal_input imm rd misa_val
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_input_imm h_not_throws
    h_circuit h_jmp2 h_pc_bridge h_pc_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
