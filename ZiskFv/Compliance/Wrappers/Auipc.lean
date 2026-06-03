import Mathlib

import ZiskFv.EquivCore.Auipc
import ZiskFv.EquivCore.Promises.UType
import ZiskFv.EquivCore.Promises.UTypeHelpers
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.RowProvenance

/-!
# AUIPC Compliance wrappers

This file keeps the legacy pin-based wrapper and the newer row-provenance
wrapper. The global compliance route uses the row-provenance wrapper for
`rd != x0` and a separate no-memory wrapper for `rd = x0`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

/-- Compliance wrapper for the AUIPC `rd = x0` no-memory shape. This route
    does not consume Main AUIPC mode pins, dynamic AUIPC transpiler bridges, or
    store-value witnesses because Sail and the production/static transpiler
    both perform no x-register write. -/
lemma equiv_AUIPC_x0_no_memory
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (promises : ZiskFv.EquivCore.Promises.UTypeNoMemPromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [] state).2 :=
  ZiskFv.EquivCore.Auipc.equiv_AUIPC_x0_no_memory
    state auipc_input imm rd exec_row promises

/-- **Compatibility wrapper for `equiv_AUIPC`.** Derives `h_circuit` from
    explicit Main-row pins and delegates to canonical
    `equiv_AUIPC`. -/
lemma equiv_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    -- Activation / opcode pins on Main + per-row subset constraint.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 ZiskFv.Trusted.OP_FLAG)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_store_pc : m.store_pc r_main = 1)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_pc_bridge : (m.pc r_main).val = auipc_input.PC.toNat)
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
      m r_main next_pc pins.main_active pins.main_op
      h_m32 h_set_pc h_store_pc h_auipc_subset
  ZiskFv.EquivCore.Auipc.equiv_AUIPC state auipc_input imm rd
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_circuit h_offset_bridge h_pc_bridge h_no_wrap h_pc_offset_lt_2_32

/-- Row-provenance wrapper for `equiv_AUIPC`. The mode pins come from a
    selected production-extracted row shape. The PC/offset dynamic facts are
    supplied explicitly by the caller. -/
lemma equiv_AUIPC_of_row_provenance
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (row_mode : ZiskFv.Compliance.MainRowProvenance.AuipcRowMode provenance)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_pc_bridge : (m.pc r_main).val = auipc_input.PC.toNat)
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
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_circuit :=
    ZiskFv.EquivCore.Promises.auipc_h_circuit_of_row_provenance
      m r_main next_pc provenance row_mode h_auipc_subset
  exact ZiskFv.EquivCore.Auipc.equiv_AUIPC state auipc_input imm rd
    exec_row e_rd m r_main next_pc store_pc_mem nextPC_val
    promises h_circuit h_offset_bridge h_pc_bridge h_no_wrap h_pc_offset_lt_2_32

end ZiskFv.Compliance
