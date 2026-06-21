import Mathlib

import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Main.OpcodeClassification
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.MemTrace
import ZiskFv.ZiskCircuit.MemTimeline.Construction
import ZiskFv.ZiskCircuit.MemTimeline.Spike
import ZiskFv.Compliance.Wrappers.Lui
import ZiskFv.Compliance.Wrappers.Auipc
import ZiskFv.Compliance.Wrappers.Jal
import ZiskFv.Compliance.Wrappers.Jalr
import ZiskFv.Compliance.Wrappers.Fence
import ZiskFv.Compliance.Wrappers.Beq
import ZiskFv.Compliance.Wrappers.Bne
import ZiskFv.Compliance.Wrappers.Blt
import ZiskFv.Compliance.Wrappers.Bge
import ZiskFv.Compliance.Wrappers.Bltu
import ZiskFv.Compliance.Wrappers.Bgeu
import ZiskFv.Compliance.Wrappers.Add
import ZiskFv.Compliance.Wrappers.Addi
import ZiskFv.Compliance.Wrappers.Addw
import ZiskFv.Compliance.Wrappers.Subw
import ZiskFv.Compliance.Wrappers.Addiw
import ZiskFv.Compliance.Wrappers.Sub
import ZiskFv.Compliance.Wrappers.And
import ZiskFv.Compliance.Wrappers.Andi
import ZiskFv.Compliance.Wrappers.Or
import ZiskFv.Compliance.Wrappers.Ori
import ZiskFv.Compliance.Wrappers.Xor
import ZiskFv.Compliance.Wrappers.Xori
import ZiskFv.AirsClean.Binary.Constraints
import ZiskFv.Compliance.Wrappers.Slt
import ZiskFv.Compliance.Wrappers.Sltu
import ZiskFv.Compliance.Wrappers.Slti
import ZiskFv.Compliance.Wrappers.Sltiu
import ZiskFv.Compliance.Wrappers.Sll
import ZiskFv.Compliance.Wrappers.Srl
import ZiskFv.Compliance.Wrappers.Sra
import ZiskFv.Compliance.Wrappers.Slli
import ZiskFv.Compliance.Wrappers.Srli
import ZiskFv.Compliance.Wrappers.Srai
import ZiskFv.Compliance.Wrappers.Shift
import ZiskFv.Compliance.Wrappers.ShiftLI
import ZiskFv.Compliance.Wrappers.ShiftR
import ZiskFv.Compliance.Wrappers.ShiftRLI
import ZiskFv.Compliance.Wrappers.ShiftRA
import ZiskFv.Compliance.Wrappers.ShiftRAI
import ZiskFv.Compliance.Wrappers.Mul
import ZiskFv.Compliance.Wrappers.MulH
import ZiskFv.Compliance.Wrappers.MulHU
import ZiskFv.Compliance.Wrappers.MulHSU
import ZiskFv.Compliance.Wrappers.MulW
import ZiskFv.Compliance.Wrappers.Div
import ZiskFv.Compliance.Wrappers.Divu
import ZiskFv.Compliance.Wrappers.Divw
import ZiskFv.Compliance.Wrappers.Divuw
import ZiskFv.Compliance.Wrappers.Rem
import ZiskFv.Compliance.Wrappers.Remu
import ZiskFv.Compliance.Wrappers.Remw
import ZiskFv.Compliance.Wrappers.Remuw
import ZiskFv.Compliance.Wrappers.Ld
import ZiskFv.Compliance.Wrappers.Lbu
import ZiskFv.Compliance.Wrappers.Lhu
import ZiskFv.Compliance.Wrappers.Lwu
import ZiskFv.Compliance.Wrappers.Lb
import ZiskFv.Compliance.Wrappers.Lh
import ZiskFv.Compliance.Wrappers.Lw
import ZiskFv.Compliance.Wrappers.Sb
import ZiskFv.Compliance.Wrappers.Sh
import ZiskFv.Compliance.Wrappers.Sw
import ZiskFv.Compliance.Wrappers.Sd
import ZiskFv.ZiskCircuit.MemTrace
import ZiskFv.AirsClean.FullEnsemble.Balance

/-!
# OpEnvelope.lean — the per-opcode input bundle for RV64IM

This file defines `OpEnvelope`, the sum type whose constructors
bundle, per Zisk opcode, the inputs and hypotheses the corresponding
`equiv_<OP>` wrapper requires. It is consumed by the per-family dispatchers in
`Compliance/Dispatch/` and, through them, by the global
theorem `zisk_riscv_compliant_program_bus` in `Compliance.lean`.

(Before Phase E2 this file was `Compliance_v1.lean`; the pre-cutover
v1 global theorem and the unused `mainOpKind` decode helpers it also
carried were dead code and have been removed.)

## Opcode bucketing by AIR shape

| Shape                  | Opcodes                                                |
|------------------------|--------------------------------------------------------|
| ControlFlow non-branch | LUI, AUIPC, JAL, JALR, FENCE                           |
| ControlFlow branch     | BEQ, BNE, BLT, BGE, BLTU, BGEU                         |
| BinaryAdd              | ADD, ADDI                                              |
| BinaryAddW             | ADDW, SUBW, ADDIW                                      |
| Binary                 | SUB, AND, OR, XOR, SLT, SLTU, SLTI, SLTIU,             |
|                        | ANDI, ORI, XORI, SLLI, SRLI, SRAI                      |
| BinaryExtension Shift  | SLL, SRL, SRA, SLLW, SRLW, SRAW, SLLIW, SRLIW, SRAIW   |
| ArithMul               | MUL, MULH, MULHSU, MULHU, MULW                         |
| ArithDiv               | DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW, REMUW         |
| Mem Load               | LD, LBU, LHU, LWU, LB, LH, LW                          |
| Mem Store              | SB, SH, SW, SD                                         |

## Why a sum type for `OpEnvelope`

The 63 wrapper signatures do not unify: they take different
`PureSpec.<OP>Input` records, different provider-AIR validators
(LUI: none; ADD: BinaryAdd; LBU/LHU/LWU: Mem + MemAlignByte +
MemAlignReadByte + MemAlign; etc.), and different bus shapes
(branches end with `bus_effect exec_row [] state`; UType/JAL/JALR
with `[e_rd]`; most arithmetic/mem with `[e0, e1, e2]`). Their
LHS conclusion forms also differ: `execute_instruction (instruction
…) state` vs. `(do; writeReg Register.nextPC; execute …) state`
whenever a Sail wrapper unfolds to a `writeReg` prefix.

A sum type is the honest encoding; an existential over a unified
record would be vacuous because most fields would be `True` / junk
values per arm.

## Trust footprint

Zero new axioms in this file. The trust footprint is exactly the
union of the 63 `equiv_<OP>` wrappers' closures against
the project's trust ledger.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.Binary
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.Mem
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Compliance


/-! ## The `OpEnvelope` sum type

Bundles, per Zisk op-kind, the inputs the corresponding
`equiv_<OP>` wrapper requires beyond `(state, m, r_main)`.
Each arm's signature is verbatim from its wrapper.
-/

set_option maxHeartbeats 1000000 in
/-- Per-op input bundle.

    Each constructor's parameter list is exactly the corresponding
    `equiv_<OP>` wrapper's parameter list, minus the shared
    `(state, m, r_main)`. -/
inductive OpEnvelope
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (m : Valid_Main FGL FGL) (r_main : ℕ) where
  -- ============================ BEQ (branch, no mem) ====================
  | beq
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BNE (branch, no mem) ====================
  | bne
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BLT (branch, no mem) ====================
  | blt
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BGE (branch, no mem) ====================
  | bge
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BLTU (branch, no mem) ===================
  | bltu
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BGEU (branch, no mem) ===================
  | bgeu
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ FENCE (no mem) ==========================
  | fence
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) : OpEnvelope state m r_main
  -- ============================ LUI (1 mem entry) =======================
  | lui
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
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
        imm rd exec_row e_rd (lui_input.PC + 4#64)) : OpEnvelope state m r_main
  -- ============================ AUIPC (1 mem entry) =====================
  | auipc
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
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
        < 4294967296) : OpEnvelope state m r_main
  -- ============================ AUIPC x0 (no mem) ======================
  | auipc_x0
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (promises : ZiskFv.EquivCore.Promises.UTypeNoMemPromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row) : OpEnvelope state m r_main
  -- ============================ JAL (1 mem entry) =======================
  | jal
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
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
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) : OpEnvelope state m r_main
  -- ============================ JAL x0 (no mem) ========================
  | jal_x0
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (nextPC_val : BitVec 64)
    (promises : ZiskFv.EquivCore.Promises.JumpNoMemPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
      : OpEnvelope state m r_main
  -- ============================ JALR (1 mem entry, do-block) ============
  | jalr
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_flag : m.flag r_main = 0)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 1)
    (h_store_pc : m.store_pc r_main = 1)
    (h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m r_main
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m r_main
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r_main
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jalr_input.PC jalr_input.rd misa_val
        (PureSpec.execute_JALR_pure jalr_input).success
        (PureSpec.execute_JALR_pure jalr_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_link_bridge :
      (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) : OpEnvelope state m r_main
  -- ============================ ADD via Binary arm (sole provider after T4-purge) =
  | add_via_binary
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : add_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : add_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADD via BinaryAdd arm ====================
  | add_via_binaryadd
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryAdd.component)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_binaryadd : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage
          (ZiskFv.AirsClean.BinaryAdd.component.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_subset : ZiskFv.Airs.Main.add_subset_holds m r_main)
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_b_lo_t : m.b_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r2)))
    (h_b_hi_t : m.b_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r2)))
    (h_m32 : m.m32 r_main = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDI via Binary arm (sole provider after T4-purge) =
  | addi_via_binary
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_input_r1_row : addi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 addi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDI via BinaryAdd arm ===================
  | addi_via_binaryadd
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryAdd.component)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_binaryadd : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage
          (ZiskFv.AirsClean.BinaryAdd.component.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_subset : ZiskFv.Airs.Main.add_subset_holds m r_main)
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDW (Binary, do-block) =================
  | addw
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_input_r2_extract :
      (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SUBW (Binary, do-block) =================
  | subw
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB_W)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
      (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage
            (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
              (providerTable.environment providerRow))) 1))
      (h_input_r1_extract :
        (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
          = ZiskFv.EquivCore.Addw.binaryRowA32
            (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
              (providerTable.environment providerRow)) % 2^32)
      (h_input_r2_extract :
        (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
          = ZiskFv.EquivCore.Addw.binaryRowB32
            (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
              (providerTable.environment providerRow)) % 2^32)
      (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDIW (Binary, do-block, I-type) ========
  | addiw
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SUB (Binary, R-type) ====================
  | sub
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
      (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage
            (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
              (providerTable.environment providerRow))) 1))
      (h_input_r1_row : sub_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)))
      (h_input_r2_row : sub_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)))
      (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ AND (Binary, R-type) ====================
  | and
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : and_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : and_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ OR (Binary, R-type) =====================
  | or
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : or_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : or_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ XOR (Binary, R-type) ====================
  | xor
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : xor_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : xor_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
        (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLT (Binary, R-type) ====================
  | slt
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : slt_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : slt_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state slt_input.r1_val slt_input.r2_val slt_input.rd slt_input.PC
        (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLTU (Binary, R-type) ===================
  | sltu
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sltu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : sltu_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sltu_input.r1_val sltu_input.r2_val sltu_input.rd sltu_input.PC
        (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ANDI (Binary, I-type) ===================
  | andi
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : andi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 andi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_andi_subset : itype_imm_subset_holds_main m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ORI (Binary, I-type) ====================
  | ori
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : ori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 ori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ XORI (Binary, I-type) ===================
  | xori
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : xori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 xori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLTI (Binary, I-type) ===================
  | slti
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_m32 : m.m32 r_main = 0)
    (h_input_r1_row : slti_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLTIU (Binary, I-type) ==================
  | sltiu
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_m32 : m.m32 r_main = 0)
    (h_input_r1_row : sltiu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_sltiu_subset : itype_imm_subset_holds_main m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLL (BinaryExtension, R-type) ===========
  | sll
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sll_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sll_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRL ====================================
  | srl
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : srl_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srl_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRA ====================================
  | sra
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sra_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sra_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SLLI ====================================
  | slli
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : slli_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : slli_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRLI ====================================
  | srli
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : srli_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srli_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRAI ====================================
  | srai
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : srai_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srai_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SLLW ====================================
  | sllw
    (sllw_input : PureSpec.SllwInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : sllw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb sllw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : sllw_input.r2_val.toNat % 32 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRLW ====================================
  | srlw
    (srlw_input : PureSpec.SrlwInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb srlw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : srlw_input.r2_val.toNat % 32 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRAW ====================================
  | sraw
    (sraw_input : PureSpec.SrawInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sraw_input.r2_val state)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : sraw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb sraw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : sraw_input.r2_val.toNat % 32 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SLLIW ===================================
  | slliw
    (slliw_input : PureSpec.SlliwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb slliw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : slliw_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRLIW ===================================
  | srliw
    (srliw_input : PureSpec.SrliwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb srliw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : srliw_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRAIW ===================================
  | sraiw
    (sraiw_input : PureSpec.SraiwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb sraiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : sraiw_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SB (store, Main-only) ===================
  | sb
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 1)
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)) :
      OpEnvelope state m r_main
  -- ============================ SH (store, Main-only) ===================
  | sh
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 2)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)) :
      OpEnvelope state m r_main
  -- ============================ SW (store, Main-only) ===================
  | sw
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 4)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)) :
      OpEnvelope state m r_main
  -- ============================ SD (store, Main-only) ===================
  | sd
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
      OpEnvelope state m r_main
  -- ============================ LD (load doubleword) ====================
  | ld
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        ld_input.rd = 0)
    (h_addr2_idx :
      ld_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ LBU =====================================
  | lbu
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_width : m.ind_width r_main = (1 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lbu_input.r1_val.toNat + (BitVec.signExtend 64 lbu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lbu_input.rd = 0)
    (h_addr2_idx :
      lbu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ LHU =====================================
  | lhu
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_width : m.ind_width r_main = (2 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lhu_input.r1_val.toNat + (BitVec.signExtend 64 lhu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lhu_input.rd = 0)
    (h_addr2_idx :
      lhu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ LWU =====================================
  | lwu
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_width : m.ind_width r_main = (4 : FGL))
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lwu_state_assumptions lwu_input state)
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lwu_input.r1_val.toNat + (BitVec.signExtend 64 lwu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lwu_input.rd = 0)
    (h_addr2_idx :
      lwu_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ LB via static BinaryExtension lookup ====
  -- T4 alternate provider arm: takes the BinaryExtension row witness
  -- + matches_entry directly + static lookup soundness, bypassing
  -- op_bus_perm_sound_BinaryExtension and bin_ext_table_consumer_wf.
  | lb_via_static_match
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lb_input.r1_val.toNat + (BitVec.signExtend 64 lb_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lb_input.rd = 0)
    (h_addr2_idx :
      lb_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ LH via static BinaryExtension lookup ====
  | lh_via_static_match
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lh_input.r1_val.toNat + (BitVec.signExtend 64 lh_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lh_input.rd = 0)
    (h_addr2_idx :
      lh_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ LW via static BinaryExtension lookup ====
  | lw_via_static_match
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lw_state_assumptions lw_input state)
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (r_mem : ℕ)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        lw_input.r1_val.toNat + (BitVec.signExtend 64 lw_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        lw_input.rd = 0)
    (h_addr2_idx :
      lw_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) : OpEnvelope state m r_main
  -- ============================ MUL =====================================
  | mul
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main
  -- ============================ MULH ====================================
  | mulh
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    -- SIGN-RANGE RESIDUAL: `na = MSB(op1)`, `nb = MSB(op2)`.  Carried, not
    -- derived (the real circuit pins it via `arith.pil:286/289/303`; the FV
    -- extraction collapses the indexed lookup to the full `rangeTable16`).
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0) :
    OpEnvelope state m r_main
  -- ============================ MULHU ===================================
  | mulhu
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    -- FAITHFUL signed-carry witness (`< 983041 ∨ ·`): balance-constructible,
    -- replaces the vacuous tight `< 2^17` UnsignedCarryRangeWitness.
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main
  -- ============================ MULHSU ==================================
  | mulhsu
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULSUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhsu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhsu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    -- SIGN-RANGE RESIDUAL on op1 only (op2 unsigned, table pins `nb = 0`).
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0) :
    OpEnvelope state m r_main
  -- ============================ MULW ====================================
  | mulw
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    OpEnvelope state m r_main
  -- ============================ DIV =====================================
  | div
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a)
            + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    -- WEAK signed remainder bound `|r| ≤ |op2|` (extraction-fidelity residual:
    -- the most the LT_ABS_NP/PN byte chain can soundly witness; the STRICT bound
    -- is recovered by the narrowed `|r| = |op2|` defect exclusion).
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    OpEnvelope state m r_main
  -- ============================ DIVU ====================================
  | divu
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : divu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : divu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main
  -- ============================ DIVW ====================================
  | divw
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    -- WEAK signed-W remainder bound `|r₃₂| ≤ |op2₃₂|` (extraction-fidelity
    -- residual; the STRICT bound is recovered from the narrowed `|r₃₂| = |op2₃₂|`
    -- defect exclusion at the canonical layer).
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    OpEnvelope state m r_main
  -- ============================ DIVUW ===================================
  | divuw
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    OpEnvelope state m r_main
  -- ============================ REM =====================================
  | rem
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REM)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ (toIntZ (v.a_0 r_a)
            + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      rem_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      rem_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ rem_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * rem_input.r1_val.toInt) :
    OpEnvelope state m r_main
  -- ============================ REMU ====================================
  | remu
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main
  -- ============================ REMW ====================================
  | remw
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REM_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    -- WEAK signed-W remainder bound `|r₃₂| ≤ |op2₃₂|` (extraction-fidelity residual).
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt) :
    OpEnvelope state m r_main
  -- ============================ REMUW ===================================
  | remuw
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    OpEnvelope state m r_main

/-- Single global residual memory-timeline boundary. Load arms require
    timeline evidence for `state` and `bus.e1`; non-load arms impose no
    obligation.

    Generated full-witness sidecar artifacts can construct this object via
    `FullWitnessGeneratedTimelineEvidence`, but the public compliance theorem
    consumes only the residual timeline API so Clean full-ensemble
    completeness does not enter the global soundness closure. -/
@[reducible]
def OpEnvelope.memoryTimelineEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : Valid_Main FGL FGL}
    {r_main : ℕ} :
    OpEnvelope state m r_main → Prop
  | .ld _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | .lbu _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | .lhu _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | .lwu _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus .. =>
      Nonempty
        (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)
  | _ => True

/-- **RETIRED** (kept for the audit diff against `LoadMemoryTimelineCoherenceEvidence`).

    Construction-shaped residual that pinned the **whole** load Sail `state` to a
    closed-form replay of the chronological prefix
    (`MemoryPrefixStateAlignment initialState state priorRows`, i.e.
    `state = stateAfterMemoryBusRows initialState priorRows`). This freezes every
    field of `state` — regs, choiceState, mem, tags, cycleCount, sailOutput.

    As of the #76 Fold-B reduction it is **no longer in the live closure of**
    `zisk_riscv_compliant_program_bus`: the `OpEnvelope` load arm and all load
    `RowData_<op>` now carry the strictly weaker, memory-map-only
    `LoadMemoryTimelineCoherenceEvidence`. This def remains only so a reviewer can
    diff the two residual shapes side by side; nothing references it. -/
@[reducible]
def LoadMemoryTimelineConstructionEvidence
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∃ (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (_facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL)),
      rows = priorRows ++ entry :: laterRows
        ∧ ZiskFv.ZiskCircuit.MemTimeline.MemoryPrefixStateAlignment
            initialState state priorRows

/-- The construction-shaped load residual produces the legacy timeline evidence
    needed by existing load equivalence cores. -/
theorem loadMemoryTimelineEvidence_of_constructionEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2)
    (h_construction : LoadMemoryTimelineConstructionEvidence state e1) :
    Nonempty (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state e1) := by
  rcases h_construction with
    ⟨initialState, rows, facts, priorRows, laterRows, h_traceSplit, h_alignment⟩
  exact
    ⟨ZiskFv.ZiskCircuit.MemTimeline.memoryTimelineEvidence_of_load_structural_promises
      facts promises priorRows laterRows h_traceSplit h_alignment⟩

/-- **Memory-only trace-coherence residual** for one load read entry (the #76
    Fold-B reduction of `LoadMemoryTimelineConstructionEvidence`).

    Where `LoadMemoryTimelineConstructionEvidence` pins the load Sail `state` to a
    closed-form whole-`SailState` replay of the prefix
    (`MemoryPrefixStateAlignment`, i.e. `state = stateAfterMemoryBusRows …`,
    freezing regs / PC / cycleCount / tags / sailOutput), this residual asks only
    for the **memory map** to chain through the prefix: an opaque cursor-indexed
    state assignment `stateAt` whose empty-prefix value is the segment initial
    state, that places the load at `stateAt priorRows`, and that satisfies the
    `RowTraceCoherence` chain (per-row `.mem` agreement; regs / PC free).

    The byte-local agreement the load consumer actually needs is then *derived*
    via the store-driven Fold-B (`stateBytesAtPrefix_of_rowTraceCoherence`); see
    `loadMemoryTimelineEvidence_of_coherenceEvidence`. This is strictly weaker
    than the whole-state identity — the non-degeneracy witness
    `ZiskFv.ZiskCircuit.MemTimeline.Spike.witness_nondegenerate` exhibits a model
    whose load state's regs **and** cycleCount differ from the initial state. -/
@[reducible]
def LoadMemoryTimelineCoherenceEvidence
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∃ (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (_facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (stateAt : List (Interaction.MemoryBusEntry FGL) →
      ZiskFv.ZiskCircuit.MemTrace.SailState)
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL)),
      rows = priorRows ++ entry :: laterRows
        ∧ stateAt [] = initialState
        ∧ stateAt priorRows = state
        ∧ ZiskFv.ZiskCircuit.MemTimeline.Spike.RowTraceCoherence stateAt [] priorRows

/-- The memory-only trace-coherence residual produces the legacy timeline
    evidence needed by existing load equivalence cores — the byte-local
    `stateBytesAtPrefix` field is *derived* via the store-driven Fold-B
    (`stateBytesAtPrefix_of_rowTraceCoherence`), not read off a whole-state
    identity. -/
theorem loadMemoryTimelineEvidence_of_coherenceEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    {opcode_assumptions : Prop}
    {pure_nextPC : BitVec 64}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (promises :
      ZiskFv.EquivCore.Promises.LoadStructuralPromises state mstatus pmaRegion
        misa mseccfg opcode_assumptions pure_nextPC exec_row e0 e1 e2)
    (h_coherence : LoadMemoryTimelineCoherenceEvidence state e1) :
    Nonempty (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state e1) := by
  obtain ⟨initialState, rows, facts, stateAt, priorRows, laterRows,
    h_traceSplit, h_seed, h_loadState, h_coherence⟩ := h_coherence
  refine ⟨{
    acceptedReplay :=
      ZiskFv.ZiskCircuit.MemTimeline.acceptedMemoryReplayEvidenceOfGeneratedReplayFacts
        facts
    priorRows := priorRows
    laterRows := laterRows
    traceSplit := by
      simpa [ZiskFv.ZiskCircuit.MemTimeline.acceptedMemoryReplayEvidenceOfGeneratedReplayFacts]
        using h_traceSplit
    selectedRead :=
      ZiskFv.ZiskCircuit.MemTimeline.selectedRead_of_load_structural_promises promises
    stateBytesAtPrefix := ?_ }⟩
  -- Derive the byte-local agreement from the Fold-B at the load state
  -- `stateAt priorRows = state`, using the seed and the trace-coherence chain.
  have h_bytes :=
    ZiskFv.ZiskCircuit.MemTimeline.Spike.stateBytesAtPrefix_of_rowTraceCoherence
      (entry := e1) facts stateAt priorRows h_seed h_coherence
  rw [h_loadState] at h_bytes
  simpa [ZiskFv.ZiskCircuit.MemTimeline.acceptedMemoryReplayEvidenceOfGeneratedReplayFacts]
    using h_bytes

/-- Single global construction boundary for memory-timeline evidence. Load arms
    require construction data for `state` and `bus.e1`; non-load arms impose no
    obligation. -/
@[reducible]
def OpEnvelope.memoryTimelineConstructionEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : Valid_Main FGL FGL}
    {r_main : ℕ} :
    OpEnvelope state m r_main → Prop
  | .ld _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | .lbu _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | .lhu _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | .lwu _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus .. =>
      LoadMemoryTimelineCoherenceEvidence state bus.e1
  | _ => True

/-- The construction boundary is the only public residual; this adapter is
    internal glue for dispatchers that still consume the older timeline API. -/
theorem OpEnvelope.memoryTimelineEvidence_of_constructionEvidence
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : Valid_Main FGL FGL}
    {r_main : ℕ}
    (env : OpEnvelope state m r_main)
    (h_construction : env.memoryTimelineConstructionEvidence) :
    env.memoryTimelineEvidence := by
  cases env with
  | ld ld_input regs mem bus pins promises r_mem h_mainEval h_providerEval
      h_msg h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | lbu lbu_input regs mem bus align pins h_width promises r_mem
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | lhu lhu_input regs mem bus align pins h_width promises r_mem
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | lwu lwu_input regs mem bus align pins h_width promises r_mem
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | lb_via_static_match lb_input regs mem v r_binary offset env h_static h_match
      bus pins promises r_mem h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | lh_via_static_match lh_input regs mem v r_binary offset env h_static h_match
      bus pins promises r_mem h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | lw_via_static_match lw_input regs mem v r_binary offset env h_static h_match
      bus pins promises r_mem h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
      exact loadMemoryTimelineEvidence_of_coherenceEvidence
        promises h_construction
  | _ => trivial

end ZiskFv.Compliance
