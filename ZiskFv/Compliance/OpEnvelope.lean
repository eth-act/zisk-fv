import Mathlib

import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Main.OpcodeClassification
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
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
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a) :
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
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulUnsignedCarryRangeWitness v r_a)
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
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a) :
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
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a)) :
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
      ZiskFv.Compliance.ArithDivUnsignedCarryRangeWitness v r_a)
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
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
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
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32)) :
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
      ZiskFv.Compliance.ArithDivUnsignedCarryRangeWitness v r_a)
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
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (rem_input.r1_val.toInt = -(2:ℤ)^63 ∧ rem_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a)) :
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
      ZiskFv.Compliance.ArithDivUnsignedCarryRangeWitness v r_a)
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
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - (v.np r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32)) :
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
      ZiskFv.Compliance.ArithDivUnsignedCarryRangeWitness v r_a)
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

/-- Marker for row-local specs carried by `OpEnvelope` constructors. -/
def OpEnvelope.rowSpecBurden
    (_env : OpEnvelope state m r_main) : Prop :=
  True

/-- Marker for provider table specs, provider-row membership, and static
    lookup evidence carried by `OpEnvelope` constructors. -/
def OpEnvelope.tableProviderBurden
    (_env : OpEnvelope state m r_main) : Prop :=
  True

/-- Marker for memory agreement, byte facts, and Mem/Main memory-bus witness
    facts carried by load/store `OpEnvelope` constructors. -/
def OpEnvelope.memoryBurden
    (env : OpEnvelope state m r_main) : Prop :=
  match env with
  | .ld _ _ _ _ _ promises .. => promises.memoryBurden
  | .lbu _ _ _ _ _ _ _ promises .. => promises.memoryBurden
  | .lhu _ _ _ _ _ _ _ promises .. => promises.memoryBurden
  | .lwu _ _ _ _ _ _ _ promises .. => promises.memoryBurden
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ _ _ promises .. =>
      promises.memoryBurden
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ _ _ promises .. =>
      promises.memoryBurden
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ _ _ promises .. =>
      promises.memoryBurden
  | _ => True

/-- Accepted Mem-trace evidence for load arms at the `OpEnvelope` boundary.

    This is the global-facing memory obligation: for a load envelope it is the
    accepted raw-row construction data, selected-event split, read tag, and
    Sail/replay cursor agreement for the selected memory-bus event. Non-load
    arms have no load-memory replay obligation. -/
def OpEnvelope.acceptedMemoryTraceBurden
    (env : OpEnvelope state m r_main) : Prop :=
  match env with
  | .ld _ _ _ _ _ promises .. => promises.memoryBurden
  | .lbu _ _ _ _ _ _ _ promises .. => promises.memoryBurden
  | .lhu _ _ _ _ _ _ _ promises .. => promises.memoryBurden
  | .lwu _ _ _ _ _ _ _ promises .. => promises.memoryBurden
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ _ _ promises .. =>
      promises.memoryBurden
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ _ _ promises .. =>
      promises.memoryBurden
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ _ _ promises .. =>
      promises.memoryBurden
  | _ => True

/-- The selected load event from an `OpEnvelope` occurs in a shared accepted
    Mem trace. Non-load arms do not select a Mem read event. -/
def OpEnvelope.selectedLoadEventInTrace
    (env : OpEnvelope state m r_main)
    (trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | .lbu _ _ _ bus _ _ _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | .lhu _ _ _ bus _ _ _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | .lwu _ _ _ bus _ _ _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ priorEvents laterEvents,
        trace = priorEvents ++
          ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1 :: laterEvents
  | _ => True

/-- Structured selected-load cursor inside an accepted execution memory trace. -/
structure SelectedLoadExecutionCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (stateAt : List ZiskFv.ZiskCircuit.MemTrace.MemEvent →
      ZiskFv.ZiskCircuit.MemTrace.SailState)
    (trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent)
    (event : ZiskFv.ZiskCircuit.MemTrace.MemEvent) : Type where
  priorEvents : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  laterEvents : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  trace_split : trace = priorEvents ++ event :: laterEvents
  state_eq : state = stateAt priorEvents

/-- The selected load event from an `OpEnvelope` occurs in an accepted
    execution memory trace at the cursor for the current Sail state. -/
def OpEnvelope.SelectedLoadEventInExecutionTraceAtState
    (env : OpEnvelope state m r_main)
    (stateAt : List ZiskFv.ZiskCircuit.MemTrace.MemEvent →
      ZiskFv.ZiskCircuit.MemTrace.SailState)
    (trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lbu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lhu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lwu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadExecutionCursor state stateAt trace
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | _ => Unit

/-- Global-facing accepted Mem trace context for an `OpEnvelope`.

    This is stronger than passing the per-load `LoadMemoryBurden` directly:
    one accepted trace for the current Sail state is supplied, and each load
    arm must identify its selected `bus.e1` event inside that trace. The
    remaining future step is proving this context from the full accepted AIR
    trace construction rather than taking it as a public premise. -/
def OpEnvelope.acceptedMemoryTraceContext
    (env : OpEnvelope state m r_main) : Prop :=
  ∃ trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent,
  ∃ _ctx : ZiskFv.ZiskCircuit.MemTrace.AcceptedMemTraceForState state trace,
    env.selectedLoadEventInTrace trace

/-- Accepted full-memory-trace evidence for the Sail state at an instruction
    cursor.

    This object contains only the replay-sound Mem trace. The separate
    envelope-at-cursor object below supplies the selected load split and the
    Sail/replay memory agreement at that cursor, which is the exact invariant
    future full-trace construction code must derive from execution-state
    replay. -/
structure AcceptedFullMemoryTrace
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    Type where
  trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  accepted : ZiskFv.ZiskCircuit.MemTrace.AcceptedMemTrace trace

/-- The selected load event of this envelope is covered by the accepted
    full-memory trace. Non-load envelopes discharge this predicate as
    `True`. -/
def OpEnvelope.acceptedFullMemoryTraceCovers
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullMemoryTrace state) : Prop :=
  env.selectedLoadEventInTrace fullTrace.trace

/-- Accepted full-memory-trace evidence at one selected load cursor. -/
structure AcceptedLoadMemoryTraceAtCursor
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (event : ZiskFv.ZiskCircuit.MemTrace.MemEvent) : Type where
  fullTrace : AcceptedFullMemoryTrace state
  priorEvents : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  laterEvents : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  trace_split : fullTrace.trace = priorEvents ++ event :: laterEvents
  read : event.op = (1 : FGL)
  stateReplayAgreement :
    ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement state
      (ZiskFv.ZiskCircuit.MemTrace.replayEvents
        fullTrace.accepted.initialMemory priorEvents)

/-- Public accepted full-memory-trace burden, scoped to load envelopes only.

    This is the global construction hook for Mem replay: non-load opcodes do
    not need memory replay evidence, while load opcodes require one accepted
    full-memory trace, the selected-event split inside that trace, and
    Sail/replay agreement at the selected cursor. -/
def OpEnvelope.acceptedFullMemoryTraceBurden
    (env : OpEnvelope state m r_main) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | .lbu _ _ _ bus _ _ _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | .lhu _ _ _ bus _ _ _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | .lwu _ _ _ bus _ _ _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      Nonempty
        (AcceptedLoadMemoryTraceAtCursor state
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1))
  | _ => True

/-- Structured full-trace construction target for this envelope.

    This is intentionally a `Type`, not a bare `Prop`: future accepted
    full-trace construction code should produce a concrete accepted
    full-memory trace, the selected-load split, and the Sail/replay cursor
    agreement. Non-load envelopes carry `Unit`, because no memory replay
    evidence is needed for them. -/
def OpEnvelope.AcceptedFullMemoryTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | _ => Unit

/-- Turn the structured full-trace construction target into the public
    load-scoped memory burden consumed by the compliance theorem. -/
theorem OpEnvelope.acceptedFullMemoryTraceBurden_of_atEnvelope
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedFullMemoryTraceAtEnvelope) :
    env.acceptedFullMemoryTraceBurden := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullMemoryTraceAtEnvelope,
      OpEnvelope.acceptedFullMemoryTraceBurden] at construction ⊢
  all_goals
    try exact trivial
    exact ⟨construction⟩

/-- Derive the dispatcher-facing load-memory burden from accepted full-trace
    evidence at the selected envelope cursor. -/
theorem OpEnvelope.memoryBurden_of_acceptedFullMemoryTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedFullMemoryTraceAtEnvelope) :
    env.memoryBurden := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullMemoryTraceAtEnvelope,
      OpEnvelope.memoryBurden,
      ZiskFv.EquivCore.Promises.LoadPromises.memoryBurden] at construction ⊢
  all_goals
    try exact trivial
    exact
      ⟨construction.fullTrace.trace, construction.fullTrace.accepted,
        construction.priorEvents, construction.laterEvents,
        construction.trace_split, construction.read,
        construction.stateReplayAgreement⟩

/-- Build one selected load cursor from an accepted execution memory trace. -/
def acceptedLoadMemoryTraceAtCursor_of_executionTrace
    (stateAt : List ZiskFv.ZiskCircuit.MemTrace.MemEvent →
      ZiskFv.ZiskCircuit.MemTrace.SailState)
    (trace priorEvents laterEvents :
      List ZiskFv.ZiskCircuit.MemTrace.MemEvent)
    (event : ZiskFv.ZiskCircuit.MemTrace.MemEvent)
    (execTrace :
      ZiskFv.ZiskCircuit.MemTrace.AcceptedExecutionMemoryTrace stateAt trace)
    (h_split : trace = priorEvents ++ event :: laterEvents)
    (h_state : state = stateAt priorEvents)
    (h_read : event.op = (1 : FGL)) :
    AcceptedLoadMemoryTraceAtCursor state event := by
  subst state
  exact
    { fullTrace :=
        { trace := trace
          accepted := execTrace.accepted }
      priorEvents := priorEvents
      laterEvents := laterEvents
      trace_split := h_split
      read := h_read
      stateReplayAgreement :=
        ZiskFv.ZiskCircuit.MemTrace.replayAgreement_at_prefix_of_execution_trace
          stateAt trace priorEvents (event :: laterEvents) execTrace h_split }

/-- Construct the envelope-local full-memory trace obligation from an accepted
    execution memory trace and a selected-load cursor proof. -/
def OpEnvelope.acceptedFullMemoryTraceAtEnvelope_of_executionTrace
    (env : OpEnvelope state m r_main)
    (stateAt : List ZiskFv.ZiskCircuit.MemTrace.MemEvent →
      ZiskFv.ZiskCircuit.MemTrace.SailState)
    (trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent)
    (execTrace :
      ZiskFv.ZiskCircuit.MemTrace.AcceptedExecutionMemoryTrace stateAt trace)
    (h_selected :
      env.SelectedLoadEventInExecutionTraceAtState stateAt trace) :
    env.AcceptedFullMemoryTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullMemoryTraceAtEnvelope,
      OpEnvelope.SelectedLoadEventInExecutionTraceAtState] at h_selected ⊢
  all_goals
    first
    | exact ()
    | exact acceptedLoadMemoryTraceAtCursor_of_executionTrace
        stateAt trace h_selected.priorEvents h_selected.laterEvents _
        execTrace h_selected.trace_split h_selected.state_eq rfl

/-- Accepted execution-memory trace data for one selected load cursor. -/
structure AcceptedLoadExecutionMemoryTraceAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (event : ZiskFv.ZiskCircuit.MemTrace.MemEvent) : Type where
  stateAt : List ZiskFv.ZiskCircuit.MemTrace.MemEvent →
    ZiskFv.ZiskCircuit.MemTrace.SailState
  trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  execTrace :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedExecutionMemoryTrace stateAt trace
  selected : SelectedLoadExecutionCursor state stateAt trace event

/-- Public accepted execution-memory trace burden, scoped to load envelopes
only. Non-load envelopes carry `Unit`; load envelopes carry an accepted Mem
trace, replay steps over a Sail state-at-cursor function, and the selected
load cursor in that execution trace. -/
def OpEnvelope.AcceptedExecutionMemoryTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadExecutionMemoryTraceAtCursor state
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry bus.e1)
  | _ => Unit

/-- Derive the existing selected full-memory trace construction from the
stronger accepted execution-memory trace evidence exposed at the public
compliance theorem boundary. -/
def OpEnvelope.acceptedFullMemoryTraceAtEnvelope_of_executionTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedExecutionMemoryTraceAtEnvelope) :
    env.AcceptedFullMemoryTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedExecutionMemoryTraceAtEnvelope,
      OpEnvelope.AcceptedFullMemoryTraceAtEnvelope] at construction ⊢
  all_goals
    first
    | exact ()
    | exact acceptedLoadMemoryTraceAtCursor_of_executionTrace
        construction.stateAt construction.trace
        construction.selected.priorEvents construction.selected.laterEvents _
        construction.execTrace construction.selected.trace_split
        construction.selected.state_eq rfl

/-- Accepted chronological memory-bus trace data for one selected load cursor.

    This bus-level construction is closer to the AIR trace shape than
    `AcceptedExecutionMemoryTrace`: it records concrete read/write memory-bus
    events and the selected load cursor. The selected Sail/replay cursor
    agreement is derived by replaying the prior bus events from initial memory
    agreement. -/
structure SelectedLoadMemoryBusReadCursor
    (state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (events : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  priorEvents : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent
  laterEvents : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent
  trace_split :
    events =
      priorEvents ++
        ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry ::
          laterEvents
  state_eq :
    state =
      ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusTrace
        initialState priorEvents

/-- Accepted chronological memory-bus trace plus the selected load cursor for
    one envelope. The selected event is the concrete bus read row emitted by
    the envelope, not an arbitrary Mem event supplied by the caller. -/
structure AcceptedLoadFullMemoryBusTraceAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  events : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent
  busTrace :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryBusExecutionTrace
      initialState events
  selected :
    SelectedLoadMemoryBusReadCursor state initialState events entry

/-- Selected load cursor in the chronological raw memory-bus row list. This is
    closer to the full AIR/Main/Mem trace shape than an already-projected event
    cursor: the split is over the concrete memory-bus rows, and the selected
    row must project to the envelope's read event. -/
structure SelectedLoadMemoryBusReadRowCursor
    (state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  priorRows : List (Interaction.MemoryBusEntry FGL)
  laterRows : List (Interaction.MemoryBusEntry FGL)
  trace_split : rows = priorRows ++ entry :: laterRows
  selected_read :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
      some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry)
  state_eq :
    state =
      ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
        initialState priorRows

/-- Build a selected load row cursor from the ordinary row split, read tags,
    and Sail cursor equality. Future AIR/Main/Mem integration should prove
    these tags from the selected Main load row rather than supplying the raw
    projected-read equality directly. -/
def SelectedLoadMemoryBusReadRowCursor.of_split_read_tags
    {state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_as : entry.as = (2 : FGL))
    (h_mult : entry.multiplicity = (-1 : FGL))
    (h_state :
      state =
        ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
          initialState priorRows) :
    SelectedLoadMemoryBusReadRowCursor state initialState rows entry :=
  { priorRows := priorRows
    laterRows := laterRows
    trace_split := h_split
    selected_read :=
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow_read
        entry h_as h_mult
    state_eq := h_state }

/-- Selected load cursor in the chronological raw memory-bus row list before
    proving that the selected row is a memory read. The read tags are already
    present in load envelopes via their Main-side `bMem` match, so this
    prefix object is the shape that full-trace integration should supply. -/
structure SelectedLoadMemoryBusRowPrefixCursor
    (state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  priorRows : List (Interaction.MemoryBusEntry FGL)
  laterRows : List (Interaction.MemoryBusEntry FGL)
  trace_split : rows = priorRows ++ entry :: laterRows
  state_eq :
    state =
      ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
        initialState priorRows

/-- The selected cursor identifies the only chronological occurrence of the
    selected row. This is the extra fact needed to promote a cursor-shaped
    state proof to the split-indexed state predicate used at the public source
    boundary. -/
def SelectedLoadMemoryBusRowPrefixCursor.prefixUnique
    {state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (cursor :
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry) :
    Prop :=
  ∀ priorRows laterRows,
    rows = priorRows ++ entry :: laterRows →
      priorRows = cursor.priorRows

/-- In a duplicate-free list, a split at a selected element has a unique
    prefix. -/
theorem List.prefix_eq_of_nodup_splits
    {α : Type} [DecidableEq α]
    {rows priorRows laterRows cursorPriorRows cursorLaterRows : List α}
    {entry : α}
    (h_nodup : rows.Nodup)
    (h_cursor :
      rows = cursorPriorRows ++ entry :: cursorLaterRows)
    (h_split :
      rows = priorRows ++ entry :: laterRows) :
    priorRows = cursorPriorRows := by
  subst rows
  induction cursorPriorRows generalizing priorRows with
  | nil =>
      cases priorRows with
      | nil =>
          rfl
      | cons head tail =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq]
            at h_split
          obtain ⟨h_head, h_tail⟩ := h_split
          subst head
          have h_nodup_cons : (entry :: cursorLaterRows).Nodup := by
            simpa using h_nodup
          have h_not_mem : entry ∉ cursorLaterRows := by
            exact (List.nodup_cons.mp h_nodup_cons).1
          have h_mem : entry ∈ cursorLaterRows := by
            rw [h_tail]
            simp
          exact False.elim (h_not_mem h_mem)
  | cons head cursorTail ih =>
      cases priorRows with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq]
            at h_split
          obtain ⟨h_head, h_tail⟩ := h_split
          subst head
          have h_nodup_cons :
              (entry :: (cursorTail ++ entry :: cursorLaterRows)).Nodup := by
            exact h_nodup
          have h_not_mem :
              entry ∉ (cursorTail ++ entry :: cursorLaterRows) := by
            exact (List.nodup_cons.mp h_nodup_cons).1
          have h_mem :
              entry ∈ (cursorTail ++ entry :: cursorLaterRows) := by
            simp
          exact False.elim (h_not_mem h_mem)
      | cons priorHead priorTail =>
          simp only [List.cons_append, List.cons.injEq] at h_split
          obtain ⟨h_head, h_tail⟩ := h_split
          subst priorHead
          have h_tail_nodup :
              (cursorTail ++ entry :: cursorLaterRows).Nodup := by
            have h_cons :
                (head :: (cursorTail ++ entry :: cursorLaterRows)).Nodup := by
              simpa using h_nodup
            exact (List.nodup_cons.mp h_cons).2
          have h_prior_tail : priorTail = cursorTail :=
            ih h_tail_nodup h_tail
          rw [h_prior_tail]

/-- A duplicate-free accepted row list discharges selected-prefix occurrence
    uniqueness for a cursor. -/
theorem SelectedLoadMemoryBusRowPrefixCursor.prefixUnique_of_nodup
    {state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (cursor :
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry)
    (h_nodup : rows.Nodup) :
    cursor.prefixUnique := by
  intro priorRows laterRows h_split
  exact
    List.prefix_eq_of_nodup_splits h_nodup cursor.trace_split h_split

/-- A selected cursor plus occurrence uniqueness gives the stronger
    split-indexed prefix-state equality. -/
theorem SelectedLoadMemoryBusRowPrefixCursor.state_eq_of_prefixUnique
    {state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (cursor :
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry)
    (h_unique : cursor.prefixUnique) :
    ∀ priorRows laterRows,
      rows = priorRows ++ entry :: laterRows →
        state =
          ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
            initialState priorRows := by
  intro priorRows laterRows h_split
  have h_prior : priorRows = cursor.priorRows :=
    h_unique priorRows laterRows h_split
  rw [h_prior]
  exact cursor.state_eq

/-- Build a selected raw-row prefix cursor from row coverage plus a proof that
    any selected split's prefix replays to the current Sail state. This factors
    selected-prefix construction into the two obligations FullEnsemble/AIR
    integration can prove independently: the selected row occurs in the
    accepted chronological row list, and the instruction state is the replayed
    prefix state for that occurrence. -/
noncomputable def SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
    {state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_mem : entry ∈ rows)
    (h_state :
      ∀ priorRows laterRows,
        rows = priorRows ++ entry :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              initialState priorRows) :
    SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry := by
  let h_exists := List.mem_iff_append.mp h_mem
  let priorRows := Classical.choose h_exists
  let laterExists := Classical.choose_spec h_exists
  let laterRows := Classical.choose laterExists
  have h_split : rows = priorRows ++ entry :: laterRows :=
    Classical.choose_spec laterExists
  exact
    { priorRows := priorRows
      laterRows := laterRows
      trace_split := h_split
      state_eq := h_state priorRows laterRows h_split }

/-- Turn a prefix cursor plus an envelope-derived Main memory-read match into
    the selected read cursor used by memory replay. -/
def SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
    {state initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    {msg : ZiskFv.Channels.MemoryBus.MemBusMessage FGL}
    (prefixCursor :
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry msg (-1) 2)) :
    SelectedLoadMemoryBusReadRowCursor state initialState rows entry := by
  obtain ⟨h_mult, h_as, _h_ptr, _h_v0, _h_v1, _h_ts⟩ := h_match
  exact
    SelectedLoadMemoryBusReadRowCursor.of_split_read_tags
      prefixCursor.priorRows prefixCursor.laterRows
      prefixCursor.trace_split h_as h_mult prefixCursor.state_eq

/-- Accepted chronological raw memory-bus rows plus the selected load row
    cursor for one envelope. The remaining AIR theorem should construct this
    object from full Main/Mem accepted trace data: chronological rows, Mem
    continuity/read-value soundness, initial memory agreement, and selected
    envelope row coverage. -/
structure AcceptedLoadFullMemoryBusRowsTraceAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  rows : List (Interaction.MemoryBusEntry FGL)
  rowsTrace :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryBusRowsTrace
      initialState rows
  selected :
    SelectedLoadMemoryBusReadRowCursor state initialState rows entry

/-- Granular construction data for accepted raw memory-bus rows plus the
    selected load row cursor. This exposes the remaining Mem continuity and
    selected-cursor obligations before they are packed into
    `AcceptedLoadFullMemoryBusRowsTraceAtCursor`. -/
structure AcceptedLoadFullMemoryBusRowsTraceConstructionAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  rows : List (Interaction.MemoryBusEntry FGL)
  rowsConstruction :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryBusRowsTraceConstruction
      initialState rows
  selected :
    SelectedLoadMemoryBusReadRowCursor state initialState rows entry

/-- Accepted global Mem row-trace facts plus the selected load row cursor.

This is the AIR-shaped predecessor of
`AcceptedLoadFullMemoryBusRowsTraceConstructionAtCursor`: the global Mem
trace spec names chronological rows, read/write replay soundness, write
updates, segment carry, and dual-memory emission before lowering to the replay
construction object used by load proofs. -/
structure AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  rows : List (Interaction.MemoryBusEntry FGL)
  fullTrace :
    ZiskFv.AirsClean.Mem.AcceptedFullMemoryBusRowsTrace initialState rows
  selected :
    SelectedLoadMemoryBusReadRowCursor state initialState rows entry

/-- Build accepted global Mem row-trace evidence at a selected load cursor from
    a global trace, row split, read tags, and the Sail cursor equality. -/
def AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor.of_split_read_tags
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (fullTrace :
      ZiskFv.AirsClean.Mem.AcceptedFullMemoryBusRowsTrace initialState rows)
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_as : entry.as = (2 : FGL))
    (h_mult : entry.multiplicity = (-1 : FGL))
    (h_state :
      state =
        ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
          initialState priorRows) :
    AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state entry :=
  { initialState := initialState
    rows := rows
    fullTrace := fullTrace
    selected :=
      SelectedLoadMemoryBusReadRowCursor.of_split_read_tags
        priorRows laterRows h_split h_as h_mult h_state }

/-- The global prefix-indexed Mem trace spec gives read replay agreement at
    the selected load row's chronological prefix. -/
theorem AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor.selectedPrefixReadAgreement
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (construction :
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state entry) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        construction.fullTrace.initialMemory construction.selected.priorRows)
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry entry) := by
  obtain ⟨h_as, h_mult⟩ :=
    ZiskFv.ZiskCircuit.MemTrace.read_tags_of_memoryBusTraceEventOfRow_read
      entry construction.selected.selected_read
  exact
    construction.fullTrace.prefixReadSound
      construction.selected.priorRows entry construction.selected.laterRows
      construction.selected.trace_split h_as h_mult

/-- The selected row cursor's Sail state agrees with replaying the raw
    memory-bus prefix before that row. -/
theorem AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor.selectedPrefixStateAgreement
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (construction :
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state entry) :
    ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement
      state
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        construction.fullTrace.initialMemory construction.selected.priorRows) := by
  rcases construction with
    ⟨initialState, rows, fullTrace,
      ⟨priorRows, laterRows, trace_split, selected_read, state_eq⟩⟩
  change
    ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement
      state
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        fullTrace.initialMemory priorRows)
  rw [state_eq]
  exact
    ZiskFv.ZiskCircuit.MemTrace.replayAgreement_after_memoryBusRows
      initialState priorRows fullTrace.initialMemory fullTrace.initialAgreement

/-- The global Mem row-trace spec and selected cursor imply the concrete
    memory byte agreement consumed by local load correctness. -/
theorem AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor.selectedMemoryTraceAgreement
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (construction :
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state entry) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement
      state (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry entry) :=
  ZiskFv.ZiskCircuit.MemTrace.memoryTraceAgreement_of_replayAgreement
    state
    (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
      construction.fullTrace.initialMemory construction.selected.priorRows)
    (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry entry)
    construction.selectedPrefixStateAgreement
    construction.selectedPrefixReadAgreement

/-- Lower accepted global Mem trace facts to the existing granular replay
    construction object for one selected load cursor. -/
def acceptedLoadFullMemoryBusRowsTraceConstructionAtCursor_of_globalTrace
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL)
    (construction :
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state entry) :
    AcceptedLoadFullMemoryBusRowsTraceConstructionAtCursor state entry :=
  { initialState := construction.initialState
    rows := construction.rows
    rowsConstruction :=
      ZiskFv.AirsClean.Mem.AcceptedFullMemoryBusRowsTrace.toRowsTraceConstruction
        construction.fullTrace
    selected := construction.selected }

/-- Pack granular row-trace construction data into the accepted row trace
    object consumed by the existing memory replay bridge. -/
def acceptedLoadFullMemoryBusRowsTraceAtCursor_of_construction
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL)
    (construction :
      AcceptedLoadFullMemoryBusRowsTraceConstructionAtCursor state entry) :
    AcceptedLoadFullMemoryBusRowsTraceAtCursor state entry :=
  { initialState := construction.initialState
    rows := construction.rows
    rowsTrace :=
      ZiskFv.ZiskCircuit.MemTrace.acceptedMemoryBusRowsTrace_of_construction
        construction.initialState construction.rows construction.rowsConstruction
    selected := construction.selected }

/-- Project accepted raw memory-bus row evidence to accepted memory-bus event
    evidence by filtering the chronological rows to memory read/write events. -/
def acceptedLoadFullMemoryBusTraceAtCursor_of_rowsTrace
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL)
    (construction :
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state entry) :
    AcceptedLoadFullMemoryBusTraceAtCursor state entry := by
  rcases construction with
    ⟨initialState, rows, rowsTrace,
      ⟨priorRows, laterRows, trace_split, selected_read, state_eq⟩⟩
  refine
    { initialState := initialState
      events :=
        ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsOfRows
          rows
      busTrace :=
        ZiskFv.ZiskCircuit.MemTrace.acceptedMemoryBusExecutionTrace_of_rowsTrace
          initialState rows rowsTrace
      selected :=
        { priorEvents :=
            ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsOfRows
              priorRows
          laterEvents :=
            ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsOfRows
              laterRows
          trace_split := ?_
          state_eq := state_eq } }
  rw [trace_split,
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsOfRows_append]
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsOfRows,
    selected_read]

/-- Lower replay construction for one selected load cursor. This object is
    derived from `AcceptedLoadFullMemoryBusTraceAtCursor`; it remains separate
    because downstream load-memory agreement already consumes this shape. -/
structure AcceptedLoadMemoryBusExecutionTraceAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  events : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent
  busTrace :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryBusExecutionTrace
      initialState events
  priorEvents : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent
  laterEvents : List ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent
  trace_split :
    events =
      priorEvents ++
        ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry ::
          laterEvents
  state_eq :
    state =
      ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusTrace
        initialState priorEvents

/-- Collapse full memory-bus trace data and its selected read cursor into the
    lower replay construction consumed by load-memory agreement. -/
def acceptedLoadMemoryBusExecutionTraceAtCursor_of_fullTrace
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL)
    (construction :
      AcceptedLoadFullMemoryBusTraceAtCursor state entry) :
    AcceptedLoadMemoryBusExecutionTraceAtCursor state entry :=
  { initialState := construction.initialState
    events := construction.events
    busTrace := construction.busTrace
    priorEvents := construction.selected.priorEvents
    laterEvents := construction.selected.laterEvents
    trace_split := construction.selected.trace_split
    state_eq := construction.selected.state_eq }

/-- Build the existing selected full-memory cursor from chronological
    memory-bus execution trace data. -/
def acceptedLoadMemoryTraceAtCursor_of_memoryBusExecutionTrace
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL)
    (construction :
      AcceptedLoadMemoryBusExecutionTraceAtCursor state entry) :
    AcceptedLoadMemoryTraceAtCursor state
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry entry) := by
  rcases construction with
    ⟨initialState, events, busTrace, priorEvents, laterEvents,
      trace_split, state_eq⟩
  subst state
  have h_mem_split :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace
        events =
        ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace
          priorEvents
        ++ ZiskFv.ZiskCircuit.MemTrace.eventOfEntry entry ::
          ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace
            laterEvents := by
    rw [trace_split,
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace,
      List.map_append]
    simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace,
      ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.toMemEvent]
  exact
    { fullTrace :=
        { trace :=
            ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace
              events
          accepted := busTrace.accepted }
      priorEvents :=
        ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace
          priorEvents
      laterEvents :=
        ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace
            laterEvents
      trace_split := h_mem_split
      read := rfl
      stateReplayAgreement := by
        simpa [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventsToMemTrace] using
          ZiskFv.ZiskCircuit.MemTrace.replayAgreement_after_memoryBusTrace
            initialState priorEvents
            busTrace.accepted.initialMemory
            busTrace.initialAgreement }

/-- Public chronological memory-bus execution trace burden, scoped to load
    envelopes only. Non-load envelopes carry `Unit`; load envelopes carry an
    accepted memory-bus event list and the selected load cursor in that list. -/
def OpEnvelope.AcceptedMemoryBusExecutionTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadMemoryBusExecutionTraceAtCursor state bus.e1
  | _ => Unit

/-- Public accepted full memory-bus trace burden, scoped to load envelopes.
    Non-load envelopes carry `Unit`; load envelopes carry a chronological
    accepted memory-bus trace plus a cursor selecting the envelope's concrete
    read row in that trace. -/
def OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusTraceAtCursor state bus.e1
  | _ => Unit

/-- Public accepted raw memory-bus row trace burden, scoped to load envelopes.
    This is the AIR-shaped predecessor of `AcceptedFullMemoryBusTraceAtEnvelope`:
    load envelopes carry chronological raw memory-bus rows plus a selected
    cursor for the envelope's concrete read row. -/
def OpEnvelope.AcceptedFullMemoryBusRowsTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsTraceAtCursor state bus.e1
  | _ => Unit

/-- Public granular raw-row construction burden, scoped to load envelopes.
    This is the visible predecessor of `AcceptedFullMemoryBusRowsTraceAtEnvelope`:
    load envelopes carry the global Mem row-trace facts plus the selected
    read-row cursor; the lower replay construction is derived internally. -/
def OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor state bus.e1
  | _ => Unit

/-- Selected load row-prefix cursor burden scoped to load envelopes. This is
    the part of the memory construction that still needs instruction-cursor
    integration: identify the envelope's concrete read row in the chronological
    public Mem row list and prove the Sail state is the replayed prefix state.
    The read tags themselves are recovered from the load envelope. -/
def OpEnvelope.SelectedLoadMemoryBusRowsPrefixAtEnvelope
    (env : OpEnvelope state m r_main)
    (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state initialState rows bus.e1
  | _ => Unit

/-- Generated Mem full-trace construction plus the selected load prefix
    cursor for one concrete load row. This is the load-scoped shape expected
    from accepted AIR/Main/Mem full-trace integration. -/
structure GeneratedMemFullTraceConstructionWithPrefixAtCursor
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  rows : List (Interaction.MemoryBusEntry FGL)
  generatedTrace :
    ZiskFv.AirsClean.Mem.GeneratedMemFullTraceConstruction
      initialState rows
  selectedPrefix :
    SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry

/-- Public generated Mem full-trace burden, scoped to load envelopes.
    Non-load envelopes carry `Unit`; load envelopes carry the generated Mem
    full-trace construction and the selected prefix cursor for the envelope's
    concrete memory read row. -/
def OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      GeneratedMemFullTraceConstructionWithPrefixAtCursor state bus.e1
  | _ => Unit

/-- Accepted AIR/Main/Mem full-trace construction plus the selected load
    prefix cursor for one concrete load row. This is the remaining global
    construction target: prove it from the accepted full execution trace, then
    the generated Mem replay burden follows internally. -/
structure AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor
    (main : Valid_Main FGL FGL)
    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (entry : Interaction.MemoryBusEntry FGL) : Type where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  rows : List (Interaction.MemoryBusEntry FGL)
  acceptedTrace :
    ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTraceConstruction
      main initialState rows
  selectedPrefix :
    SelectedLoadMemoryBusRowPrefixCursor state initialState rows entry

/-- Public accepted AIR/Main/Mem full-trace burden, scoped to load envelopes.
    Non-load envelopes carry `Unit`; load envelopes carry the accepted
    full-trace construction and the selected prefix cursor for the envelope's
    concrete memory read row. -/
def OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      AcceptedAirMainMemFullTraceConstructionWithPrefixAtCursor m state bus.e1
  | _ => Unit

/-- Shared accepted AIR/Main/Mem trace data scoped to load envelopes.
    Non-load envelopes carry `Unit`; load envelopes carry the shared
    program-level trace object, without the selected cursor. -/
def OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type :=
  match env with
  | .ld .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | .lbu .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | .lhu .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | .lwu .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | .lb_via_static_match .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | .lh_via_static_match .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | .lw_via_static_match .. =>
      ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  | _ => Unit

/-- Recover the shared accepted AIR/Main/Mem trace object from the
    load-scoped accepted trace construction plus selected prefix cursor. -/
def OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_construction
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope) :
    env.AcceptedAirMainMemFullTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope] at construction ⊢
  case ld =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  case lbu =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  case lhu =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  case lwu =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  case lb_via_static_match =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  case lh_via_static_match =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  case lw_via_static_match =>
    exact
      { initialState := construction.initialState
        rows := construction.rows
        construction := construction.acceptedTrace }
  all_goals exact ()

/-- Selected-prefix coverage for the accepted AIR/Main/Mem trace at one
    envelope. This is separated from the shared trace object so the future
    full-execution theorem has two explicit jobs: construct the chronological
    Mem trace, and locate each load row's cursor in it. -/
def OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope) : Type :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | .lbu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | .lhu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | .lwu _ _ _ bus _ _ _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      SelectedLoadMemoryBusRowPrefixCursor state
        acceptedTrace.initialState acceptedTrace.rows bus.e1
  | _ => Unit

/-- Selected load-row membership in the accepted chronological Mem row list.
    This is one of the two proof obligations needed to construct
    `SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope`; it should eventually
    follow from the selected Main/Mem row match plus the embedding of projected
    Mem replay rows into the accepted chronological trace. -/
def OpEnvelope.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | .lbu _ _ _ bus _ _ _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | .lhu _ _ _ bus _ _ _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | .lwu _ _ _ bus _ _ _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      bus.e1 ∈ acceptedTrace.rows
  | _ => True

/-- FullEnsemble-shaped selected-row coverage for the accepted chronological
    Mem trace. For load envelopes, the selected Main memory read must first
    be a projected read-replay row of some concrete Mem table, and those
    projected rows must be embedded in the accepted chronological row list.

    This is the visible bridge point for future accepted-execution
    integration: FullEnsemble/Mem extraction should prove the table-local
    selected projection and the global embedding, after which ordinary row
    membership follows below. -/
def OpEnvelope.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | .lbu _ _ _ bus _ _ _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | .lhu _ _ _ bus _ _ _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | .lwu _ _ _ bus _ _ _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ table : Air.Flat.Table FGL,
        ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
          table acceptedTrace.rows
          ∧ bus.e1 ∈
            ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable table
  | _ => True

/-- Split-indexed Sail state equality for the selected load row. This is the
    second proof obligation needed to construct the selected-prefix cursor:
    whenever the accepted chronological row list is split at the envelope's
    concrete load row, the current Sail state is the replayed memory state
    after that prefix. -/
def OpEnvelope.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | .lbu _ _ _ bus _ _ _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | .lhu _ _ _ bus _ _ _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | .lwu _ _ _ bus _ _ _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∀ priorRows laterRows,
        acceptedTrace.rows = priorRows ++ bus.e1 :: laterRows →
          state =
            ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows
              acceptedTrace.initialState priorRows
  | _ => True

/-- Occurrence uniqueness for the selected prefix cursor in the accepted
    chronological Mem trace. For load envelopes, every split of the accepted
    rows at the selected load row has the same prefix as the selected cursor;
    non-load envelopes carry no memory occurrence. -/
def OpEnvelope.SelectedPrefixUniqueAtAcceptedAirMainMemTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope)
    (selectedPrefix :
      env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace) : Prop :=
  match env with
  | .ld .. =>
      selectedPrefix.prefixUnique
  | .lbu .. =>
      selectedPrefix.prefixUnique
  | .lhu .. =>
      selectedPrefix.prefixUnique
  | .lwu .. =>
      selectedPrefix.prefixUnique
  | .lb_via_static_match .. =>
      selectedPrefix.prefixUnique
  | .lh_via_static_match .. =>
      selectedPrefix.prefixUnique
  | .lw_via_static_match .. =>
      selectedPrefix.prefixUnique
  | _ => True

/-- Promote cursor-shaped selected-prefix evidence to the split-indexed
    prefix-state predicate when the selected row occurrence is unique. -/
theorem OpEnvelope.selectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope_of_prefixUnique
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope)
    (selectedPrefix :
      env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace)
    (h_unique :
      env.SelectedPrefixUniqueAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace selectedPrefix) :
    env.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
      acceptedTrace := by
  cases env <;>
    simp [OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.SelectedPrefixUniqueAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope]
      at acceptedTrace selectedPrefix h_unique ⊢
  all_goals
    exact
      SelectedLoadMemoryBusRowPrefixCursor.state_eq_of_prefixUnique
        selectedPrefix h_unique

/-- The FullEnsemble-shaped selected read-replay coverage implies ordinary
    selected-row membership in the accepted chronological Mem trace. -/
theorem OpEnvelope.selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_memReadReplayRow
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope)
    (h_selected :
      env.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace) :
    env.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope
      acceptedTrace := by
  cases env <;>
    simp [OpEnvelope.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope]
      at h_selected ⊢
  all_goals
    rcases h_selected with ⟨table, h_embedded, h_row⟩
    exact h_embedded _
      (by
        simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
          ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
          ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
          using h_row)

/-- Accepted AIR/Main/Mem evidence at one envelope, factored at the current
    full-execution bridge point.

    For non-load envelopes this object is trivial. For load envelopes it
    carries the shared accepted AIR/Main/Mem trace, a FullEnsemble-shaped
    selected read-row coverage proof, and the split-indexed Sail prefix-state
    equality. The ordinary selected-row membership and selected prefix cursor
    are derived from these fields by the global compliance theorem. -/
structure OpEnvelope.AcceptedAirMainMemTraceEvidenceAtEnvelope
    (env : OpEnvelope state m r_main) : Type where
  acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope
  selectedReadRow :
    env.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope
      acceptedTrace
  selectedPrefixState :
    env.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
      acceptedTrace

/-- Shared accepted AIR/Main/Mem trace data plus the concrete Mem table whose
    projected replay rows are embedded in that accepted trace.

    This is a program-level bridge shape for load envelopes: full-execution
    integration should construct it once from the accepted Main/Mem trace, then
    selected load envelopes only need to prove that their selected row occurs
    in this table projection and that their Sail state is the replayed prefix
    state at that row. Non-load envelopes carry `Unit`. -/
structure AcceptedAirMainMemFullTraceWithMemTable
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) : Type 2 where
  acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  table : Air.Flat.Table FGL
  embedded :
    ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
      table acceptedTrace.rows
  replayEmbedded :
    ZiskFv.AirsClean.FullEnsemble.MemReplayRowsEmbeddedInTrace
      table acceptedTrace.rows

/-- Accepted AIR/Main/Mem trace data tied to a concrete Mem table in a full
    RV64IM Clean ensemble witness.

    This is the next upstream shape for full-execution integration. It still
    records the global embedding obligation explicitly, but the selected table
    is no longer arbitrary: it is a `Mem.componentWithDualMemBus` table from
    an actual `fullRv64imEnsemble` witness. -/
structure AcceptedAirMainMemFullTraceWithFullEnsembleMemTable
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) : Type 2 where
  length : ℕ
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
        length program).ensemble
  acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m
  table : Air.Flat.Table FGL
  table_mem : table ∈ witness.allTables
  table_component :
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
  embedded :
    ZiskFv.AirsClean.FullEnsemble.MemReadReplayRowsEmbeddedInTrace
      table acceptedTrace.rows
  replayEmbedded :
    ZiskFv.AirsClean.FullEnsemble.MemReplayRowsEmbeddedInTrace
      table acceptedTrace.rows

/-- Construct the full-ensemble Mem-table bridge from an actual full RV64IM
    witness plus embedding theorems for whichever mutable Mem table occurs in
    that witness. The table itself is selected by
    `exists_mem_table_of_fullRv64im_witness`; selected-row occurrence and
    prefix-state alignment remain separate obligations. -/
noncomputable def AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows) :
    AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m := by
  let existsTable :=
    ZiskFv.AirsClean.FullEnsemble.exists_mem_table_of_fullRv64im_witness
      witness
  let table := Classical.choose existsTable
  have h_table : table ∈ witness.allTables :=
    (Classical.choose_spec existsTable).1
  have h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus :=
    (Classical.choose_spec existsTable).2
  exact
    { length := length
      program := program
      witness := witness
      acceptedTrace := acceptedTrace
      table := table
      table_mem := h_table
      table_component := h_component
      embedded := embedded table h_table h_component
      replayEmbedded := replayEmbedded table h_table h_component }

/-- Forget full-ensemble provenance and keep the trace/table bridge consumed
    by the current replay theorem. -/
def AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    (construction :
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m) :
    AcceptedAirMainMemFullTraceWithMemTable m :=
  { acceptedTrace := construction.acceptedTrace
    table := construction.table
    embedded := construction.embedded
    replayEmbedded := construction.replayEmbedded }

/-- Load-scoped shared accepted trace plus Mem-table embedding. -/
def OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | .lbu .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | .lhu .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | .lwu .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | .lb_via_static_match .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | .lh_via_static_match .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | .lw_via_static_match .. =>
      AcceptedAirMainMemFullTraceWithMemTable m
  | _ => ULift.{2, 0} Unit

/-- Load-scoped shared accepted trace plus full-ensemble Mem-table bridge.
    Non-load envelopes carry `ULift Unit`; load envelopes carry the program
    trace, full-ensemble witness, concrete Mem table, and embedding needed to
    build the current trace/table object. -/
def OpEnvelope.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | .lbu .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | .lhu .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | .lwu .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | .lb_via_static_match .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | .lh_via_static_match .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | .lw_via_static_match .. =>
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable m
  | _ => ULift.{2, 0} Unit

/-- Lower the full-ensemble Mem-table bridge to the existing trace/table
    bridge object at one envelope. -/
def OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope) :
    env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope]
      at construction ⊢
  case ld =>
    exact construction.toTraceWithMemTable
  case lbu =>
    exact construction.toTraceWithMemTable
  case lhu =>
    exact construction.toTraceWithMemTable
  case lwu =>
    exact construction.toTraceWithMemTable
  case lb_via_static_match =>
    exact construction.toTraceWithMemTable
  case lh_via_static_match =>
    exact construction.toTraceWithMemTable
  case lw_via_static_match =>
    exact construction.toTraceWithMemTable
  all_goals exact ULift.up ()

/-- Envelope-scoped constructor for the full-ensemble Mem-table bridge.

    Load envelopes receive the witness-selected mutable dual-Mem table; non-load
    envelopes carry `ULift Unit`. This is the first full-execution extraction
    step that no longer asks callers to choose a concrete Mem table. -/
noncomputable def OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows) :
    env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope]
  case ld =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  case lbu =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  case lhu =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  case lwu =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  case lb_via_static_match =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  case lh_via_static_match =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  case lw_via_static_match =>
    exact
      AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
        program witness acceptedTrace embedded replayEmbedded
  all_goals exact ULift.up ()

/-- The accepted trace contained in the shared trace/table bridge object. -/
def OpEnvelope.acceptedTraceOfFullTraceWithMemTable
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope) :
    env.AcceptedAirMainMemFullTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope] at traceWithTable ⊢
  case ld => exact traceWithTable.acceptedTrace
  case lbu => exact traceWithTable.acceptedTrace
  case lhu => exact traceWithTable.acceptedTrace
  case lwu => exact traceWithTable.acceptedTrace
  case lb_via_static_match => exact traceWithTable.acceptedTrace
  case lh_via_static_match => exact traceWithTable.acceptedTrace
  case lw_via_static_match => exact traceWithTable.acceptedTrace
  all_goals exact ()

/-- Selected load-row coverage in the concrete FullEnsemble Mem table
    projection carried by the shared trace/table bridge object. -/
def OpEnvelope.SelectedMemReadReplayRowInTraceTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | .lbu _ _ _ bus _ _ _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | .lhu _ _ _ bus _ _ _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | .lwu _ _ _ bus _ _ _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      bus.e1 ∈
        ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable
          traceWithTable.table
  | _ => True

/-- Provider-row selected coverage in the concrete FullEnsemble Mem table.
    This is the table-local predecessor of
    `SelectedMemReadReplayRowInTraceTableAtEnvelope`: the selected load row is
    matched by either the primary or dual read projection of a concrete Mem
    provider row. -/
def OpEnvelope.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope) : Prop :=
  match env with
  | .ld _ _ _ bus _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | .lbu _ _ _ bus _ _ _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | .lhu _ _ _ bus _ _ _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | .lwu _ _ _ bus _ _ _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | .lb_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | .lh_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | .lw_via_static_match _ _ _ _ _ _ _ _ _ bus _ _ .. =>
      ∃ providerRow ∈ traceWithTable.table.table,
        ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
        ∨ ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
          (ZiskFv.AirsClean.FullEnsemble.memDualReadReplayEntryOfRow
            (eval (traceWithTable.table.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
  | _ => True

/-- A matched concrete primary/dual Mem provider row implies selected
    membership in the table's read-replay projection. -/
theorem OpEnvelope.selectedMemReadReplayRowInTraceTableAtEnvelope_of_providerRow
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope)
    (h_provider :
      env.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope
        traceWithTable) :
    env.SelectedMemReadReplayRowInTraceTableAtEnvelope traceWithTable := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope,
      OpEnvelope.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope,
      OpEnvelope.SelectedMemReadReplayRowInTraceTableAtEnvelope]
      at traceWithTable h_provider ⊢
  all_goals
    rcases h_provider with ⟨providerRow, h_providerRow, h_primary | h_dual⟩
    · simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
        ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
        ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
        using
          ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_table_row_match
            h_providerRow h_primary
    · simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
        ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
        ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
        using
          ZiskFv.AirsClean.FullEnsemble.mem_dual_read_replay_entry_mem_of_table_row_match
            h_providerRow h_dual

/-- Split-indexed Sail prefix-state equality at the accepted trace contained
    in the shared trace/table bridge object. -/
def OpEnvelope.SelectedPrefixStateAtTraceTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope) : Prop :=
  env.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
    (env.acceptedTraceOfFullTraceWithMemTable traceWithTable)

/-- Provider-row coverage for the full-ensemble Mem table bridge. -/
def OpEnvelope.SelectedMemProviderReadReplayRowInFullEnsembleMemTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope) :
    Prop :=
  env.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope
    (env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
      construction)

/-- Concrete selected Mem provider-row occurrence in the FullEnsemble Mem
    table, expressed in the smaller shape available from load envelope arms.

    The load constructors already carry the selected Clean Mem provider row
    and the Main/Mem message equality.  The remaining table-local obligation
    is that this same evaluated Mem row occurs in the concrete Mem table of
    the full-ensemble bridge.  From that row occurrence, the full selected
    provider replay-row coverage is derived below. -/
def OpEnvelope.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope) :
    Prop :=
  match env with
  | .ld (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | .lbu (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | .lhu (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | .lwu (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | .lb_via_static_match (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | .lh_via_static_match (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | .lw_via_static_match (memRowVar := memRowVar) (memEnv := memEnv) .. =>
      ∃ providerRow ∈
          (AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.table,
        eval
          ((AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable
            construction).table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar
  | _ => True

/-- The envelope's selected Clean Mem provider row gives the full selected
    primary read-replay coverage once it is identified with a row of the
    FullEnsemble Mem table. -/
theorem OpEnvelope.selectedMemProviderReadReplayRowInFullEnsembleMemTableAtEnvelope_of_envelopeMemRow
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope)
    (h_row :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        construction) :
    env.SelectedMemProviderReadReplayRowInFullEnsembleMemTableAtEnvelope
      construction := by
  cases env <;>
    simp [OpEnvelope.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope,
      OpEnvelope.SelectedMemProviderReadReplayRowInFullEnsembleMemTableAtEnvelope,
      OpEnvelope.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope,
      OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble]
      at construction h_row ⊢
  case ld ld_input regs mem bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match
  case lbu lbu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match
  case lhu lhu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match
  case lwu lwu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match
  case lb_via_static_match lb_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match
  case lh_via_static_match lh_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match
  case lw_via_static_match lw_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    refine ⟨providerRow, h_providerRow, Or.inl ?_⟩
    rw [h_row_eval]
    change ZiskFv.Airs.MemoryBus.matches_memory_entry _
      (ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayEntryOfRow
        (eval _ _))
    exact
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
        h_mainEval h_providerEval h_msg h_main_b_match

/-- The selected envelope Mem-row occurrence plus replay-row embedding gives
    ordinary accepted-row membership directly. Unlike the older read-row
    bridge, this uses the polarity-preserving replay embedding and the
    load-arm proof `wr = 0`, so write rows are not required to appear in the
    accepted trace as reads. -/
theorem OpEnvelope.selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_envelopeMemRowReplay
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope)
    (h_row :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        construction) :
    env.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope
      (env.acceptedTraceOfFullTraceWithMemTable
        (env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
          construction)) := by
  cases env <;>
    simp [OpEnvelope.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope,
      OpEnvelope.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope,
      OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
      OpEnvelope.acceptedTraceOfFullTraceWithMemTable]
      at construction h_row ⊢
  case ld ld_input regs mem bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match
  case lbu lbu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match
  case lhu lhu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match
  case lwu lwu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match
  case lb_via_static_match lb_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match
  case lh_via_static_match lh_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match
  case lw_via_static_match lw_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    rcases h_row with ⟨providerRow, h_providerRow, h_row_eval⟩
    have h_providerRow' : providerRow ∈ construction.table.table := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_providerRow
    have h_row_eval' :
        eval (construction.table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
          eval memEnv memRowVar := by
      simpa [AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.toTraceWithMemTable]
        using h_row_eval
    refine
      ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
        construction.replayEmbedded h_providerRow' ?_ ?_
    · rw [h_row_eval']
      rw [h_mem_row]
      exact h_mem_wr
    · rw [h_row_eval']
      exact
        ZiskFv.AirsClean.FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
          h_mainEval h_providerEval h_msg h_main_b_match

/-- Selected raw-row prefix cursor for the accepted trace contained in the
    full-ensemble Mem table bridge.  This is the cursor-shaped state proof
    expected from full-execution replay; unlike the older split-indexed state
    predicate, it identifies the selected occurrence rather than requiring a
    state proof for every possible split at an equal row. -/
def OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope) :
    Type :=
  env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
    (env.acceptedTraceOfFullTraceWithMemTable
      (env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
        construction))

/-- Split-indexed Sail prefix-state equality for the accepted trace contained
    in the FullEnsemble Mem-table bridge.  This is the remaining per-envelope
    state-cursor fact once selected row membership has been derived from the
    concrete Mem-table row occurrence. -/
def OpEnvelope.SelectedPrefixStateAtFullEnsembleMemTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope) :
    Prop :=
  env.SelectedPrefixStateAtTraceTableAtEnvelope
    (env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
      construction)

/-- Occurrence uniqueness for the selected prefix cursor in the accepted
    trace contained in the FullEnsemble Mem-table bridge. -/
def OpEnvelope.SelectedPrefixUniqueAtFullEnsembleMemTableAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope)
    (selectedPrefix :
      env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
        construction) : Prop :=
  env.SelectedPrefixUniqueAtAcceptedAirMainMemTraceAtEnvelope
    (env.acceptedTraceOfFullTraceWithMemTable
      (env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
        construction))
    selectedPrefix

/-- Promote a FullEnsemble-table selected prefix cursor to the source-shaped
    split-indexed prefix-state predicate, provided the selected occurrence is
    unique in the accepted chronological row list. -/
theorem OpEnvelope.selectedPrefixStateAtFullEnsembleMemTableAtEnvelope_of_prefixUnique
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope)
    (selectedPrefix :
      env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
        construction)
    (h_unique :
      env.SelectedPrefixUniqueAtFullEnsembleMemTableAtEnvelope
        construction selectedPrefix) :
    env.SelectedPrefixStateAtFullEnsembleMemTableAtEnvelope
      construction := by
  exact
    env.selectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope_of_prefixUnique
      (env.acceptedTraceOfFullTraceWithMemTable
        (env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
          construction))
      selectedPrefix
      h_unique

/-- Cursor-shaped full-execution Mem extraction target for one envelope.

    Full execution replay naturally produces a selected raw-row prefix cursor,
    not a universal split-indexed equality over every possible split at an
    equal row. This object is therefore the next upstream theorem target:
    prove the full trace/table bridge, the selected envelope Mem-row
    occurrence, and the selected prefix cursor from accepted full execution
    data, then let the public compliance theorem consume that cursor directly. -/
structure OpEnvelope.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 where
  fullTraceTable :
    env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
      fullTraceTable
  selectedPrefix :
    env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
      fullTraceTable

/-- Build the current public accepted-memory evidence object from the next
    upstream full-execution bridge shape: a shared accepted trace, a concrete
    FullEnsemble Mem-table embedding into that trace, selected row coverage in
    the table projection, and selected prefix-state equality. -/
def OpEnvelope.acceptedAirMainMemTraceEvidenceAtEnvelope_of_traceTable
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope)
    (h_selected :
      env.SelectedMemReadReplayRowInTraceTableAtEnvelope traceWithTable)
    (h_state :
      env.SelectedPrefixStateAtTraceTableAtEnvelope traceWithTable) :
    env.AcceptedAirMainMemTraceEvidenceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope,
      OpEnvelope.SelectedMemReadReplayRowInTraceTableAtEnvelope,
      OpEnvelope.SelectedPrefixStateAtTraceTableAtEnvelope,
      OpEnvelope.acceptedTraceOfFullTraceWithMemTable]
      at traceWithTable h_selected h_state ⊢
  case ld =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  case lbu =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  case lhu =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  case lwu =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  case lb_via_static_match =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  case lh_via_static_match =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  case lw_via_static_match =>
    exact
      { acceptedTrace := traceWithTable.acceptedTrace
        selectedReadRow :=
          ⟨traceWithTable.table, traceWithTable.embedded,
            by
              simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
                ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
                using h_selected⟩
        selectedPrefixState := h_state }
  all_goals
    exact
      { acceptedTrace := ()
        selectedReadRow := trivial
        selectedPrefixState := trivial }

/-- Project selected read-row coverage from a trace/table bridge to the
    accepted trace carried by that same bridge. -/
theorem OpEnvelope.selectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope_of_traceTable
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope)
    (h_selected :
      env.SelectedMemReadReplayRowInTraceTableAtEnvelope traceWithTable) :
    env.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope
      (env.acceptedTraceOfFullTraceWithMemTable traceWithTable) := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope,
      OpEnvelope.SelectedMemReadReplayRowInTraceTableAtEnvelope,
      OpEnvelope.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.acceptedTraceOfFullTraceWithMemTable]
      at traceWithTable h_selected ⊢
  all_goals
    exact
      ⟨traceWithTable.table, traceWithTable.embedded,
        by
          simpa [ZiskFv.AirsClean.FullEnsemble.memReadReplayRowsOfTable,
            ZiskFv.AirsClean.FullEnsemble.memPrimaryReadReplayRowsOfTable,
            ZiskFv.AirsClean.FullEnsemble.memDualReadReplayRowsOfTable]
            using h_selected⟩

/-- Build the current public accepted-memory evidence object from concrete
    provider-row coverage in the shared FullEnsemble Mem table. This composes
    the table-local primary/dual provider-row adapter with the trace/table
    bridge above. -/
def OpEnvelope.acceptedAirMainMemTraceEvidenceAtEnvelope_of_traceTableProvider
    (env : OpEnvelope state m r_main)
    (traceWithTable :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope)
    (h_provider :
      env.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope
        traceWithTable)
    (h_state :
      env.SelectedPrefixStateAtTraceTableAtEnvelope traceWithTable) :
    env.AcceptedAirMainMemTraceEvidenceAtEnvelope :=
  env.acceptedAirMainMemTraceEvidenceAtEnvelope_of_traceTable traceWithTable
    (env.selectedMemReadReplayRowInTraceTableAtEnvelope_of_providerRow
      traceWithTable h_provider)
    h_state

/-- Build the selected-prefix cursor from the two explicit selected-row
    obligations at the accepted AIR/Main/Mem boundary: row membership in the
    accepted chronological trace and split-indexed Sail prefix-state equality. -/
noncomputable def OpEnvelope.selectedPrefixAtAcceptedAirMainMemTraceAtEnvelope_of_rowMembership
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope)
    (h_mem :
      env.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace)
    (h_state :
      env.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace) :
    env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope acceptedTrace := by
  cases env <;>
    simp [OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope]
      at acceptedTrace h_mem h_state ⊢
  case ld =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  case lbu =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  case lhu =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  case lwu =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  case lb_via_static_match =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  case lh_via_static_match =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  case lw_via_static_match =>
    exact SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split
      h_mem h_state
  all_goals exact ()

/-- Build the cursor-shaped extraction target from FullEnsemble-aligned facts:
    the concrete Mem-table bridge, the selected envelope Mem-row occurrence in
    that table, and the split-indexed Sail prefix-state equality for the same
    accepted trace carried by the bridge. Selected row membership is derived
    internally from the table occurrence and embedding. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
    (env : OpEnvelope state m r_main)
    (fullTraceTable :
      env.AcceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        fullTraceTable)
    (selectedPrefixState :
      env.SelectedPrefixStateAtFullEnsembleMemTableAtEnvelope
        fullTraceTable) :
    env.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope := by
  let traceWithTable :=
    env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
      fullTraceTable
  let acceptedTrace :=
    env.acceptedTraceOfFullTraceWithMemTable traceWithTable
  have selectedPrefixStateAtAccepted :
      env.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace := by
    change
      env.SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope
        (env.acceptedTraceOfFullTraceWithMemTable traceWithTable)
    exact selectedPrefixState
  have selectedMembership :
      env.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope
        acceptedTrace :=
    env.selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_envelopeMemRowReplay
      fullTraceTable selectedEnvelopeRow
  exact
    { fullTraceTable := fullTraceTable
      selectedEnvelopeRow := selectedEnvelopeRow
      selectedPrefix :=
        env.selectedPrefixAtAcceptedAirMainMemTraceAtEnvelope_of_rowMembership
          acceptedTrace selectedMembership selectedPrefixStateAtAccepted }

/-- Construct the cursor-shaped full-execution memory extraction target from
    witness-selected full-ensemble Mem data and a selected prefix cursor.

    This is the direct shape expected from accepted full-execution replay: a
    witness-selected Mem table bridge, selected row occurrence in that table,
    and a cursor identifying the selected chronological prefix. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_witnessCursor
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness acceptedTrace embedded replayEmbedded))
    (selectedPrefix :
      env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness acceptedTrace embedded replayEmbedded)) :
    env.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope :=
  { fullTraceTable :=
      env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        program witness acceptedTrace embedded replayEmbedded
    selectedEnvelopeRow := selectedEnvelopeRow
    selectedPrefix := selectedPrefix }

/-- Construct the cursor-shaped full-execution memory extraction target from
    witness-selected full-ensemble Mem data.

    This composes the witness-selected mutable Mem table constructor with the
    table-local selected-row and prefix-state bridge. The remaining upstream
    obligations are therefore exactly the named mutable-Mem embedding, the
    selected envelope Mem-row occurrence in the selected table, and the
    selected prefix-state equality. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_witnessPrefixState
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness acceptedTrace embedded replayEmbedded))
    (selectedPrefixState :
      env.SelectedPrefixStateAtFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness acceptedTrace embedded replayEmbedded)) :
    env.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope :=
  env.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
    (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
      program witness acceptedTrace embedded replayEmbedded)
    selectedEnvelopeRow
    selectedPrefixState

/-- Load-scoped mutable-Mem embedding obligation at the accepted trace
    construction boundary. Non-load envelopes carry `True`; load envelopes
    require the witness-selected mutable Mem table's read-replay rows to embed
    in the chronological rows from the accepted construction. -/
def OpEnvelope.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (_program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length _program).ensemble)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope) :
    Prop :=
  match env with
  | .ld .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lbu .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lhu .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lwu .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lb_via_static_match .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lh_via_static_match .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lw_via_static_match .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness construction.rows
  | _ => True

/-- Load-scoped all-event mutable-Mem embedding obligation at the accepted
    trace construction boundary. Non-load envelopes carry `True`; load
    envelopes require the witness-selected mutable Mem table's read/write
    replay rows to embed in the chronological rows from the accepted
    construction. -/
def OpEnvelope.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (_program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length _program).ensemble)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope) :
    Prop :=
  match env with
  | .ld .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lbu .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lhu .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lwu .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lb_via_static_match .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lh_via_static_match .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | .lw_via_static_match .. =>
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness construction.rows
  | _ => True

/-- Load-scoped selected envelope Mem-row occurrence at the accepted trace
    construction boundary. The concrete Mem table is selected from the
    full-ensemble witness, and the shared accepted trace is recovered from the
    construction. -/
def OpEnvelope.SelectedEnvelopeMemRowAtAcceptedTraceConstructionWithWitness
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope)
    (embedded :
      env.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (replayEmbedded :
      env.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction) :
    Prop :=
  match env with
  | .ld .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | .lbu .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | .lhu .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | .lwu .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | .lb_via_static_match .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | .lh_via_static_match .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | .lw_via_static_match .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          program witness
          { initialState := construction.initialState
            rows := construction.rows
            construction := construction.acceptedTrace }
          embedded replayEmbedded)
  | _ => True

/-- Shared full-execution memory trace construction for one Main trace.

    This is the program-level memory object expected from accepted full
    execution: a full RV64IM witness, the accepted AIR/Main/Mem memory trace,
    the proof that the witness-selected mutable Mem table embeds its projected
    read-replay rows for selected-load coverage, and the stronger proof that
    its real read/write replay rows are embedded for chronological memory
    replay. It deliberately does not select a particular load envelope row. -/
structure AcceptedFullExecutionMemoryTrace
    (main : Valid_Main FGL FGL) : Type 2 where
  length : ℕ
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
        length program).ensemble
  acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace main
  embedded :
    ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
      witness acceptedTrace.rows
  replayEmbedded :
    ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
      witness acceptedTrace.rows

/-- Package accepted AIR/Main/Mem trace data, a full RV64IM witness, and the
    witness-level mutable-Mem embeddings into the shared full-execution memory
    trace object. This is only record packaging; the semantic fields of
    `acceptedTrace` and the embedding proofs remain explicit inputs. -/
def AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
    {main : Valid_Main FGL FGL}
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace main)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows) :
    AcceptedFullExecutionMemoryTrace main :=
  { length := length
    program := program
    witness := witness
    acceptedTrace := acceptedTrace
    embedded := embedded
    replayEmbedded := replayEmbedded }

/-- Shared accepted-execution Mem row extraction target.

    This names the program-level theorem result still missing from accepted
    full-execution integration: construct the chronological accepted
    AIR/Main/Mem trace and prove that the full RV64IM witness's mutable-Mem
    table projections embed in that trace for both selected reads and full
    read/write replay. Per-envelope selected-load coverage remains separate. -/
structure AcceptedFullExecutionMemoryRowExtraction
    (main : Valid_Main FGL FGL) : Type 2 where
  length : ℕ
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
        length program).ensemble
  acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace main
  embedded :
    ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
      witness acceptedTrace.rows
  replayEmbedded :
    ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
      witness acceptedTrace.rows

/-- Lower the named row-extraction target to the shared full-execution memory
    trace package already consumed by the load replay bridge. -/
def AcceptedFullExecutionMemoryRowExtraction.toFullTrace
    {main : Valid_Main FGL FGL}
    (extraction : AcceptedFullExecutionMemoryRowExtraction main) :
    AcceptedFullExecutionMemoryTrace main :=
  AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
    extraction.program extraction.witness extraction.acceptedTrace
    extraction.embedded extraction.replayEmbedded

/-- Load-scoped view of the shared full-execution memory trace. -/
def OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m) :
    env.AcceptedAirMainMemFullTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope]
  all_goals
    try exact ()
  all_goals
    exact fullTrace.acceptedTrace

/-- Selected envelope row occurrence for the witness-selected Mem table in a
    shared full-execution memory trace. Non-load envelopes carry no row
    obligation. -/
def OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m) : Prop :=
  match env with
  | .ld .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | .lbu .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | .lhu .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | .lwu .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | .lb_via_static_match .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | .lh_via_static_match .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | .lw_via_static_match .. =>
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
  | _ => True

/-- Per-envelope coverage facts for a shared full-execution memory trace.

    The selected prefix identifies the concrete chronological read occurrence
    for this envelope. The selected row occurrence ties the envelope's Clean
    Mem provider row to the witness-selected mutable Mem table. -/
structure OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m) : Type 1 where
  selectedPrefix :
    env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
      (env.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace
        fullTrace)
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace fullTrace

/-- Unpacked per-envelope selection facts for accepted AIR/Main/Mem trace data.

    This is the shape accepted full-execution integration is expected to
    produce for each load envelope once the shared trace and witness-level
    Mem-table embedding are known: the selected prefix cursor in the accepted
    chronological Mem trace, plus the selected envelope Mem-row occurrence in
    the witness-selected mutable Mem table. -/
structure OpEnvelope.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows) : Type 1 where
  selectedPrefix :
    env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
      (env.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace
        (AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
          program witness acceptedTrace embedded replayEmbedded))
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        program witness acceptedTrace embedded replayEmbedded)

/-- Per-envelope selected-load extraction indexed by the named shared row
    extraction package.

    This is just the extraction-shaped view of
    `AcceptedFullExecutionMemoryTraceSelectionAtEnvelope`: accepted full
    execution should construct the shared row extraction once, then prove this
    selected-prefix/selected-row package for each load envelope. -/
def OpEnvelope.AcceptedFullExecutionMemoryRowSelectionAtEnvelope
    (env : OpEnvelope state m r_main)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m) : Type 1 :=
  env.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
    extraction.program extraction.witness extraction.acceptedTrace
    extraction.embedded extraction.replayEmbedded

/-- Cursor-shaped per-envelope selected-load extraction indexed by the named
    shared row extraction package.

    This is the shape expected from accepted full-execution replay: after the
    shared chronological Mem trace and witness-selected mutable-Mem embeddings
    have been constructed once, each selected load envelope must identify its
    concrete Mem provider row in that witness-selected table and the selected
    chronological prefix cursor for the corresponding memory-bus read. The
    accepted trace's `rowsNodup` invariant derives occurrence uniqueness later,
    so callers do not pass it here. -/
structure OpEnvelope.AcceptedFullExecutionMemoryRowCursorSelectionAtEnvelope
    (env : OpEnvelope state m r_main)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m) : Type 1 where
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        extraction.program extraction.witness extraction.acceptedTrace
        extraction.embedded extraction.replayEmbedded)
  selectedPrefix :
    env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        extraction.program extraction.witness extraction.acceptedTrace
        extraction.embedded extraction.replayEmbedded)

/-- Repack unpacked selected-prefix/selected-row evidence into the shared
    full-execution coverage object consumed by the current compliance proof. -/
def OpEnvelope.acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_selection
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded) :
    env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
      (AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
        program witness acceptedTrace embedded replayEmbedded) :=
  { selectedPrefix := selection.selectedPrefix
    selectedEnvelopeRow := by
      cases env <;>
        simp [OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
          OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness]
          at selection ⊢
      all_goals
        exact selection.selectedEnvelopeRow }

/-- Repack extraction-indexed selected-load evidence into the ordinary
    per-envelope coverage object for `extraction.toFullTrace`. -/
def OpEnvelope.acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_rowSelection
    (env : OpEnvelope state m r_main)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowSelectionAtEnvelope extraction) :
    env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
      extraction.toFullTrace :=
  env.acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_selection
    extraction.program extraction.witness extraction.acceptedTrace
    extraction.embedded extraction.replayEmbedded selection

/-- Repack row-extraction-indexed cursor evidence into the existing unpacked
    selection shape. This bridge is definitional: both predicates carry the
    same selected row and selected prefix, but the cursor form makes the
    accepted-full-execution replay obligation clearer. -/
def OpEnvelope.acceptedFullExecutionMemoryRowSelectionAtEnvelope_of_cursorSelection
    (env : OpEnvelope state m r_main)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowCursorSelectionAtEnvelope extraction) :
    env.AcceptedFullExecutionMemoryRowSelectionAtEnvelope extraction := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryRowSelectionAtEnvelope]
      at selection ⊢
  all_goals
    exact
      { selectedPrefix := selection.selectedPrefix
        selectedEnvelopeRow := selection.selectedEnvelopeRow }

/-- Source-shaped per-envelope coverage facts for a shared full-execution
    memory trace.

    This is the boundary expected from accepted full-execution integration:
    selected Mem-row occurrence in the witness-selected table, plus the
    split-indexed Sail prefix-state equality. The selected prefix cursor used
    by the replay bridge is derived internally from these two facts and the
    shared mutable-Mem embedding. -/
structure OpEnvelope.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m) : Type 1 where
  selectedPrefixState :
    env.SelectedPrefixStateAtFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded)
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded)

/-- Cursor-shaped source coverage for a shared full-execution memory trace.

    This is one step closer to accepted full-execution replay than
    `AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope`: it carries the
    selected prefix cursor that replay naturally constructs, plus the explicit
    occurrence-uniqueness proof needed to promote that cursor to the
    split-indexed source predicate. -/
structure OpEnvelope.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m) : Type 1 where
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded)
  selectedPrefix :
    env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded)
  selectedPrefixUnique :
    env.SelectedPrefixUniqueAtFullEnsembleMemTableAtEnvelope
      (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded)
      selectedPrefix

/-- Build source-shaped coverage from cursor-shaped selected-prefix evidence
    plus a proof that the selected row occurrence is unique in the accepted
    chronological trace. This is the honest bridge from the cursor shape
    naturally produced by execution replay to the split-indexed source shape
    currently consumed by the public compliance theorem. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope_of_prefixUnique
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded))
    (selectedPrefix :
      env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded))
    (h_unique :
      env.SelectedPrefixUniqueAtFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
        selectedPrefix) :
    env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace :=
  { selectedPrefixState :=
      env.selectedPrefixStateAtFullEnsembleMemTableAtEnvelope_of_prefixUnique
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
        selectedPrefix h_unique
    selectedEnvelopeRow := selectedEnvelopeRow }

/-- Lower cursor-shaped full-execution coverage to source-shaped coverage. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope_of_cursorCoverage
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (cursorCoverage :
      env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope
        fullTrace) :
    env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace :=
  env.acceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope_of_prefixUnique
    fullTrace cursorCoverage.selectedEnvelopeRow
    cursorCoverage.selectedPrefix cursorCoverage.selectedPrefixUnique

/-- Build cursor-shaped coverage from unpacked accepted AIR/Main/Mem
    selection evidence.

    The accepted trace's duplicate-free row invariant discharges selected
    occurrence uniqueness, so accepted-execution callers that already provide
    the selected prefix cursor and selected Mem-row occurrence do not need to
    pass uniqueness separately. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope_of_selection
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded) :
    env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope
      (AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
        program witness acceptedTrace embedded replayEmbedded) := by
  cases env <;>
    try dsimp only [OpEnvelope.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope,
      OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
      OpEnvelope.SelectedPrefixUniqueAtFullEnsembleMemTableAtEnvelope,
      OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
      OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
      OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
      OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
      at selection ⊢
  all_goals
    exact
      { selectedEnvelopeRow := selection.selectedEnvelopeRow
        selectedPrefix := selection.selectedPrefix
        selectedPrefixUnique := by
          first
          | exact
              selection.selectedPrefix.prefixUnique_of_nodup
                acceptedTrace.construction.rowsNodup
          | trivial }

/-- Build cursor-shaped coverage from source-shaped coverage. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_sourceCoverage
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (sourceCoverage :
      env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace) :
    env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace := by
  cases env
  case ld ld_input regs mem bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .ld ld_input regs mem bus pins promises r_mem h_mainEval h_providerEval
        h_msg h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
        h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
        h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  case lbu lbu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .lbu lbu_input regs mem bus align pins h_width promises r_mem
        h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
        h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
        h_addr2_idx h_mem_sel h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  case lhu lhu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .lhu lhu_input regs mem bus align pins h_width promises r_mem
        h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
        h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
        h_addr2_idx h_mem_sel h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  case lwu lwu_input regs mem bus align pins h_width promises r_mem
      mainRowVar memRowVar mainEnv memEnv mainMult providerMult
      mainInteraction providerInteraction h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .lwu lwu_input regs mem bus align pins h_width promises r_mem
        h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
        h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
        h_addr2_idx h_mem_sel h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  case lb_via_static_match lb_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .lb_via_static_match lb_input regs mem v r_binary offset binEnv
        h_static h_match bus pins promises r_mem h_mainEval h_providerEval
        h_msg h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
        h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
        h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  case lh_via_static_match lh_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .lh_via_static_match lh_input regs mem v r_binary offset binEnv
        h_static h_match bus pins promises r_mem h_mainEval h_providerEval
        h_msg h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
        h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
        h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  case lw_via_static_match lw_input regs mem v r_binary offset binEnv
      h_static h_match bus pins promises r_mem mainRowVar memRowVar
      mainEnv memEnv mainMult providerMult mainInteraction
      providerInteraction h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    let env' : OpEnvelope state m r_main :=
      .lw_via_static_match lw_input regs mem v r_binary offset binEnv
        h_static h_match bus pins promises r_mem h_mainEval h_providerEval
        h_msg h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
        h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
        h_mem_wr
    let fullTraceTable :=
      env'.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
        fullTrace.program fullTrace.witness fullTrace.acceptedTrace
        fullTrace.embedded fullTrace.replayEmbedded
    let extraction :=
      env'.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState
        fullTraceTable sourceCoverage.selectedEnvelopeRow
        sourceCoverage.selectedPrefixState
    exact
      { selectedPrefix := by
          simpa [env', fullTraceTable,
            OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope,
            OpEnvelope.acceptedTraceOfFullTraceWithMemTable,
            OpEnvelope.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble,
            OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_fullExecutionMemoryTrace]
            using extraction.selectedPrefix
        selectedEnvelopeRow := by
          simpa [env',
            OpEnvelope.SelectedEnvelopeMemRowAtAcceptedFullExecutionMemoryTrace,
            OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness,
            fullTraceTable]
            using sourceCoverage.selectedEnvelopeRow }
  all_goals
    exact
      { selectedPrefix := ()
        selectedEnvelopeRow := trivial }

/-- Load-scoped package containing the shared full-execution memory trace plus
    coverage for one envelope. Non-load envelopes carry no memory data.

    This is the honest inverse shape of
    `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope`: the shared trace
    can only be recovered from a load-scoped construction on load arms. -/
def OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | .lbu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | .lhu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | .lwu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | .lb_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | .lh_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | .lw_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace
  | _ => ULift.{2, 0} Unit

/-- Load-scoped shared full-execution memory trace.

    This is the split form of `AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope`:
    load envelopes carry the shared memory trace object, while non-load
    envelopes carry no memory trace obligation. -/
def OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. => AcceptedFullExecutionMemoryTrace m
  | .lbu .. => AcceptedFullExecutionMemoryTrace m
  | .lhu .. => AcceptedFullExecutionMemoryTrace m
  | .lwu .. => AcceptedFullExecutionMemoryTrace m
  | .lb_via_static_match .. => AcceptedFullExecutionMemoryTrace m
  | .lh_via_static_match .. => AcceptedFullExecutionMemoryTrace m
  | .lw_via_static_match .. => AcceptedFullExecutionMemoryTrace m
  | _ => ULift.{2, 0} Unit

/-- Per-envelope selected-row/prefix coverage indexed by the load-scoped
    shared trace object. -/
def OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (fullTraceAtEnvelope :
      env.AcceptedFullExecutionMemoryTraceAtEnvelope) : Type 1 :=
  match env with
  | .ld .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | .lbu .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | .lhu .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | .lwu .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | .lb_via_static_match .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | .lh_via_static_match .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | .lw_via_static_match .. =>
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        fullTraceAtEnvelope
  | _ => ULift.{1, 0} Unit

/-- Project a shared full-execution memory trace into the load-scoped split
    public boundary. Non-load envelopes carry no memory trace data. -/
def OpEnvelope.acceptedFullExecutionMemoryTraceAtEnvelope_of_fullTrace
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m) :
    env.AcceptedFullExecutionMemoryTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope]
  all_goals
    try exact ULift.up ()
  all_goals
    exact fullTrace

/-- Project ordinary coverage for a shared full-execution memory trace into
    the indexed split public boundary. -/
def OpEnvelope.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_fullTraceCoverage
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace) :
    env.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope
      (env.acceptedFullExecutionMemoryTraceAtEnvelope_of_fullTrace
        fullTrace) := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope,
      OpEnvelope.acceptedFullExecutionMemoryTraceAtEnvelope_of_fullTrace]
      at coverage ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact coverage

/-- Pack the split load-scoped trace plus selected coverage back into the
    compatibility package consumed by the existing replay bridge. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_split
    (env : OpEnvelope state m r_main)
    (fullTraceAtEnvelope :
      env.AcceptedFullExecutionMemoryTraceAtEnvelope)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope
        fullTraceAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope]
      at fullTraceAtEnvelope coverage ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact ⟨fullTraceAtEnvelope, coverage⟩

/-- Load-scoped package containing the shared full-execution memory trace plus
    source-shaped coverage for one envelope. Non-load envelopes carry no
    memory data.

    Compared with `AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope`,
    this exposes the two remaining per-load obligations expected from accepted
    full execution instead of asking callers for the already-built selected
    prefix cursor. -/
def OpEnvelope.AcceptedFullExecutionMemoryTraceSourceAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | .lbu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | .lhu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | .lwu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | .lb_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | .lh_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | .lw_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope fullTrace
  | _ => ULift.{2, 0} Unit

/-- Load-scoped package containing the shared full-execution memory trace plus
    cursor-shaped source coverage. Non-load envelopes carry no memory data.

    This is the current upstream theorem target: accepted full execution should
    construct the shared trace, locate the selected Mem row, construct the
    selected chronological prefix cursor, and prove that selected occurrence is
    unique. The split-indexed source predicate is derived below. -/
def OpEnvelope.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | .lbu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | .lhu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | .lwu .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | .lb_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | .lh_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | .lw_via_static_match .. =>
      Σ fullTrace : AcceptedFullExecutionMemoryTrace m,
        env.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope fullTrace
  | _ => ULift.{2, 0} Unit

/-- Load-scoped source evidence from a shared full-execution trace, selected
    table-row occurrence, cursor-shaped selected-prefix evidence, and selected
    occurrence uniqueness. Non-load envelopes carry no memory data. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_prefixUnique
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded))
    (selectedPrefix :
      env.SelectedPrefixAtFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded))
    (h_unique :
      env.SelectedPrefixUniqueAtFullEnsembleMemTableAtEnvelope
        (env.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness
          fullTrace.program fullTrace.witness fullTrace.acceptedTrace
          fullTrace.embedded fullTrace.replayEmbedded)
        selectedPrefix) :
    env.AcceptedFullExecutionMemoryTraceSourceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceSourceAtEnvelope]
      at selectedEnvelopeRow selectedPrefix h_unique ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      ⟨fullTrace,
        OpEnvelope.acceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope_of_prefixUnique
          _ fullTrace selectedEnvelopeRow selectedPrefix h_unique⟩

/-- Lower the cursor-shaped public memory evidence to the source-shaped
    package consumed by the existing replay bridge. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_cursorSource
    (env : OpEnvelope state m r_main)
    (cursorSource :
      env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceSourceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceSourceAtEnvelope]
      at cursorSource ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      ⟨cursorSource.1,
        OpEnvelope.acceptedFullExecutionMemoryTraceSourceCoverageAtEnvelope_of_cursorCoverage
          _ cursorSource.1 cursorSource.2⟩

/-- Build the cursor-shaped public memory evidence from accepted AIR/Main/Mem
    trace data, witness-level mutable-Mem embeddings, and unpacked selected
    prefix/row evidence. Selected occurrence uniqueness is derived internally
    from the accepted trace's duplicate-free row invariant. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_selection
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded) :
    env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope := by
  let env0 := env
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope]
      at selection ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      ⟨AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
          program witness acceptedTrace embedded replayEmbedded,
        OpEnvelope.acceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope_of_selection
          env0 program witness acceptedTrace embedded replayEmbedded selection⟩

/-- Build cursor-shaped public memory evidence from the named shared row
    extraction package plus extraction-indexed selected-load evidence. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowSelection
    (env : OpEnvelope state m r_main)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowSelectionAtEnvelope extraction) :
    env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope :=
  env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_selection
    extraction.program extraction.witness extraction.acceptedTrace
    extraction.embedded extraction.replayEmbedded selection

/-- Build cursor-shaped public memory evidence from the named shared row
    extraction plus cursor-shaped selected-load evidence. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowCursorSelection
    (env : OpEnvelope state m r_main)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowCursorSelectionAtEnvelope extraction) :
    env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope :=
  env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowSelection
    extraction
    (env.acceptedFullExecutionMemoryRowSelectionAtEnvelope_of_cursorSelection
      extraction selection)

/-- Lower source-shaped full-execution memory evidence to the selected-cursor
    coverage package consumed by the existing replay bridge. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_source
    (env : OpEnvelope state m r_main)
    (source : env.AcceptedFullExecutionMemoryTraceSourceAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceSourceAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope]
      at source ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      ⟨source.1,
        OpEnvelope.acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_sourceCoverage
          _ source.1 source.2⟩

/-- Full-execution memory construction data for one load cursor.

    This is the theorem-shaped upstream target: accepted full execution should
    provide the accepted AIR/Main/Mem trace construction, the full RV64IM
    witness, the mutable-Mem read-row embedding for selected-load coverage, the
    all-event mutable-Mem embedding for replay, and selected envelope Mem-row
    occurrence in the witness-selected table. The selected prefix cursor is
    already part of `construction`. -/
structure OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionWithWitness
    (env : OpEnvelope state m r_main) : Type 2 where
  length : ℕ
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
        length program).ensemble
  construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope
  embedded :
    env.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
      program witness construction
  replayEmbedded :
    env.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
      program witness construction
  selectedEnvelopeRow :
    env.SelectedEnvelopeMemRowAtAcceptedTraceConstructionWithWitness
      program witness construction embedded replayEmbedded

/-- Load-scoped full-execution memory construction target.

    This is the public boundary shape one step above
    `AcceptedFullExecutionMemoryCursorExtractionAtEnvelope`: load envelopes
    carry the accepted AIR/Main/Mem trace construction, a full RV64IM witness,
    the mutable-Mem read-row embedding for that witness, and selected
    envelope Mem-row occurrence in the witness-selected table. Non-load
    envelopes carry no memory obligation. -/
def OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main) : Type 2 :=
  match env with
  | .ld .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | .lbu .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | .lhu .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | .lwu .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | .lb_via_static_match .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | .lh_via_static_match .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | .lw_via_static_match .. =>
      env.AcceptedFullExecutionMemoryTraceConstructionWithWitness
  | _ => ULift.{2, 0} Unit

/-- Package the unpacked accepted AIR/Main/Mem construction fields into the
    load-scoped full-execution memory construction object.

    This is an integration helper for callers that have proved the accepted
    trace construction, mutable-Mem embeddings, and selected envelope Mem-row
    occurrence separately. Non-load envelopes carry no memory data. -/
def OpEnvelope.acceptedFullExecutionMemoryTraceConstructionWithWitness_of_fields
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope)
    (embedded :
      env.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (replayEmbedded :
      env.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowAtAcceptedTraceConstructionWithWitness
        program witness construction embedded replayEmbedded) :
    env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope]
      at construction embedded replayEmbedded selectedEnvelopeRow ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      { length := length
        program := program
        witness := witness
        construction := construction
        embedded := embedded
        replayEmbedded := replayEmbedded
        selectedEnvelopeRow := selectedEnvelopeRow }

/-- Occurrence uniqueness for the selected prefix carried by the older
    load-scoped full-execution construction object. Non-load envelopes carry
    no memory occurrence obligation. -/
def OpEnvelope.SelectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) : Prop :=
  match env with
  | .ld .. =>
      construction.construction.selectedPrefix.prefixUnique
  | .lbu .. =>
      construction.construction.selectedPrefix.prefixUnique
  | .lhu .. =>
      construction.construction.selectedPrefix.prefixUnique
  | .lwu .. =>
      construction.construction.selectedPrefix.prefixUnique
  | .lb_via_static_match .. =>
      construction.construction.selectedPrefix.prefixUnique
  | .lh_via_static_match .. =>
      construction.construction.selectedPrefix.prefixUnique
  | .lw_via_static_match .. =>
      construction.construction.selectedPrefix.prefixUnique
  | _ => True

/-- The duplicate-free row invariant in the accepted Mem trace discharges
    selected-prefix occurrence uniqueness for the selected load cursor carried
    by the full-execution construction object. -/
theorem OpEnvelope.selectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_nodup
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) :
    env.SelectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope
      construction := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope,
      OpEnvelope.SelectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope]
      at construction ⊢
  all_goals
    exact
      construction.construction.selectedPrefix.prefixUnique_of_nodup
        construction.construction.acceptedTrace.rowsNodup

/-- Lower the load-scoped full-execution memory construction target to the
    cursor-shaped extraction object consumed by the existing replay chain. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_acceptedTraceConstruction
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) :
    env.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope]
      at construction ⊢
  all_goals
    try
      exact
        { fullTraceTable := ULift.up ()
          selectedEnvelopeRow := trivial
          selectedPrefix := () }
    all_goals
      exact
        { fullTraceTable :=
            AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness
              construction.program construction.witness
              { initialState := construction.construction.initialState
                rows := construction.construction.rows
                construction := construction.construction.acceptedTrace }
              construction.embedded construction.replayEmbedded
          selectedEnvelopeRow := construction.selectedEnvelopeRow
          selectedPrefix := construction.construction.selectedPrefix }

/-- Lower the older full-execution construction object to the current
    cursor-shaped public source package when selected occurrence uniqueness is
    available. This isolates the remaining extra fact needed beyond the older
    construction boundary. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_traceConstructionAndPrefixUnique
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope)
    (h_unique :
      env.SelectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope
        construction) :
    env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope,
      OpEnvelope.SelectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope]
      at construction h_unique ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    refine
      ⟨{ length := construction.length
         program := construction.program
         witness := construction.witness
         acceptedTrace :=
           { initialState := construction.construction.initialState
             rows := construction.construction.rows
             construction := construction.construction.acceptedTrace }
         embedded := construction.embedded
         replayEmbedded := construction.replayEmbedded },
       ?_⟩
    exact
      { selectedEnvelopeRow := construction.selectedEnvelopeRow
        selectedPrefix := construction.construction.selectedPrefix
        selectedPrefixUnique := h_unique }

/-- Lower the older full-execution construction object to the current
    cursor-shaped public source package using the accepted trace's
    duplicate-free row invariant to prove selected occurrence uniqueness. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_traceConstruction
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope :=
  env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_traceConstructionAndPrefixUnique
    construction
    (env.selectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_nodup
      construction)

/-- Combine shared accepted trace data with selected-prefix coverage to
    recover the packed load-scoped construction object used by the existing
    replay bridge. -/
def OpEnvelope.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_traceAndPrefix
    (env : OpEnvelope state m r_main)
    (acceptedTrace : env.AcceptedAirMainMemFullTraceAtEnvelope)
    (selectedPrefix :
      env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope acceptedTrace) :
    env.AcceptedAirMainMemFullTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope,
      OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope,
      OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope]
      at acceptedTrace selectedPrefix ⊢
  case ld =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  case lbu =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  case lhu =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  case lwu =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  case lb_via_static_match =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  case lh_via_static_match =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  case lw_via_static_match =>
    exact
      { initialState := acceptedTrace.initialState
        rows := acceptedTrace.rows
        acceptedTrace := acceptedTrace.construction
        selectedPrefix := selectedPrefix }
  all_goals exact ()

/-- Decompose the older load-scoped full-execution construction object into
    the newer shared trace plus selected envelope coverage package.

    This is a migration helper for upstream callers of the older boundary; it
    does not manufacture memory evidence for non-load envelopes. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_traceConstruction
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope]
      at construction ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    refine
      ⟨{ length := construction.length
         program := construction.program
         witness := construction.witness
         acceptedTrace :=
           { initialState := construction.construction.initialState
             rows := construction.construction.rows
             construction := construction.construction.acceptedTrace }
         embedded := construction.embedded
         replayEmbedded := construction.replayEmbedded },
       ?_⟩
    exact
      { selectedPrefix := construction.construction.selectedPrefix
        selectedEnvelopeRow := construction.selectedEnvelopeRow }

/-- Project the shared full-execution memory trace from the older
    construction object into the split public boundary shape. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceAtEnvelope_of_traceConstruction
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope]
      at construction ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      { length := construction.length
        program := construction.program
        witness := construction.witness
        acceptedTrace :=
          { initialState := construction.construction.initialState
            rows := construction.construction.rows
            construction := construction.construction.acceptedTrace }
        embedded := construction.embedded
        replayEmbedded := construction.replayEmbedded }

/-- Project selected coverage from the older construction object into the
    split public boundary shape, indexed by the projected shared trace above. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_traceConstruction
    (env : OpEnvelope state m r_main)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope
      (env.acceptedFullExecutionMemoryTraceAtEnvelope_of_traceConstruction
        construction) := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope,
      OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope,
      OpEnvelope.acceptedFullExecutionMemoryTraceAtEnvelope_of_traceConstruction]
      at construction ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      { selectedPrefix := construction.construction.selectedPrefix
        selectedEnvelopeRow := construction.selectedEnvelopeRow }

/-- Build the current public load-scoped memory construction object from a
    shared accepted full-execution memory trace plus per-envelope selected
    coverage. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_fullExecutionMemoryTrace
    (env : OpEnvelope state m r_main)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace) :
    env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope]
      at ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      { length := fullTrace.length
        program := fullTrace.program
        witness := fullTrace.witness
        construction :=
          { initialState := fullTrace.acceptedTrace.initialState
            rows := fullTrace.acceptedTrace.rows
            acceptedTrace := fullTrace.acceptedTrace.construction
            selectedPrefix := coverage.selectedPrefix }
        embedded := fullTrace.embedded
        replayEmbedded := fullTrace.replayEmbedded
        selectedEnvelopeRow := coverage.selectedEnvelopeRow }

/-- Build the current public load-scoped memory construction object from the
    explicit accepted AIR/Main/Mem trace, witness embeddings, and unpacked
    per-envelope selection evidence. This keeps the accepted-execution
    integration boundary source-shaped while still routing through the packed
    construction object consumed by replay. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_acceptedAirMainMemSelection
    (env : OpEnvelope state m r_main)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded) :
    env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope :=
  env.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_fullExecutionMemoryTrace
    (AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
      program witness acceptedTrace embedded replayEmbedded)
    (env.acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_selection
      program witness acceptedTrace embedded replayEmbedded selection)

/-- Lower the load-scoped shared-trace-plus-coverage package to the older
    load-scoped construction object consumed by the replay bridge.

    This is the public theorem boundary shape: non-load envelopes carry no
    memory trace data, while load envelopes carry the shared accepted trace and
    selected coverage needed to build the construction internally. -/
noncomputable def OpEnvelope.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_traceWithCoverage
    (env : OpEnvelope state m r_main)
    (traceWithCoverage :
      env.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope) :
    env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope]
      at traceWithCoverage ⊢
  all_goals
    try exact ULift.up ()
  all_goals
    exact
      { length := traceWithCoverage.1.length
        program := traceWithCoverage.1.program
        witness := traceWithCoverage.1.witness
        construction :=
          { initialState := traceWithCoverage.1.acceptedTrace.initialState
            rows := traceWithCoverage.1.acceptedTrace.rows
            acceptedTrace := traceWithCoverage.1.acceptedTrace.construction
            selectedPrefix := traceWithCoverage.2.selectedPrefix }
        embedded := traceWithCoverage.1.embedded
        replayEmbedded := traceWithCoverage.1.replayEmbedded
        selectedEnvelopeRow := traceWithCoverage.2.selectedEnvelopeRow }

/-- Lower accepted AIR/Main/Mem full-trace data to the generated Mem burden
    currently consumed by replay. -/
def OpEnvelope.generatedMemFullTraceConstructionAtEnvelope_of_acceptedAirMainMemTrace
    (env : OpEnvelope state m r_main)
    (acceptedTraceAtEnvelope :
      env.AcceptedAirMainMemFullTraceConstructionAtEnvelope) :
    env.GeneratedMemFullTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope,
      OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope]
      at acceptedTraceAtEnvelope ⊢
  case ld =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  case lbu =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  case lhu =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  case lwu =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  case lb_via_static_match =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  case lh_via_static_match =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  case lw_via_static_match =>
    exact
      { initialState := acceptedTraceAtEnvelope.initialState
        rows := acceptedTraceAtEnvelope.rows
        generatedTrace :=
          acceptedTraceAtEnvelope.acceptedTrace.toGeneratedMemFullTraceConstruction
        selectedPrefix := acceptedTraceAtEnvelope.selectedPrefix }
  all_goals exact ()

/-- Construct the public load-scoped memory-row burden from a shared accepted
    Mem row trace plus an envelope-specific prefix cursor. The selected
    row's `as = 2` and `multiplicity = -1` facts are derived from each load
    arm's existing Main-side memory-read match, so callers no longer need to
    provide raw read tags in the cursor. -/
def OpEnvelope.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_globalTraceAndPrefix
    (env : OpEnvelope state m r_main)
    (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (fullTrace :
      ZiskFv.AirsClean.Mem.AcceptedFullMemoryBusRowsTrace initialState rows)
    (prefixCursor :
      env.SelectedLoadMemoryBusRowsPrefixAtEnvelope initialState rows) :
    env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.SelectedLoadMemoryBusRowsPrefixAtEnvelope,
      OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope]
      at prefixCursor ⊢
  case ld =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  case lbu =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  case lhu =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  case lwu =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  case lb_via_static_match =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  case lh_via_static_match =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  case lw_via_static_match =>
    exact
      { initialState := initialState
        rows := rows
        fullTrace := fullTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              prefixCursor (by assumption) }
  all_goals exact ()

/-- Construct the public load-scoped memory-row burden from generated Mem
    full-trace construction data plus an envelope-specific selected prefix
    cursor. This is the next AIR bridge target: prove the generated
    construction and selected cursor from accepted AIR/Main/Mem full-trace
    data, then this adapter supplies the current compliance theorem's memory
    premise. -/
def OpEnvelope.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedTraceAndPrefix
    (env : OpEnvelope state m r_main)
    (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (rows : List (Interaction.MemoryBusEntry FGL))
    (generatedTrace :
      ZiskFv.AirsClean.Mem.GeneratedMemFullTraceConstruction
        initialState rows)
    (prefixCursor :
      env.SelectedLoadMemoryBusRowsPrefixAtEnvelope initialState rows) :
    env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope :=
  env.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_globalTraceAndPrefix
    initialState rows
    generatedTrace.toAcceptedFullMemoryBusRowsTrace
    prefixCursor

/-- Lower the generated Mem full-trace burden to the current packed memory
    construction burden consumed by replay. -/
def OpEnvelope.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (generatedTraceAtEnvelope :
      env.GeneratedMemFullTraceConstructionAtEnvelope) :
    env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope]
      at generatedTraceAtEnvelope ⊢
  case ld =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  case lbu =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  case lhu =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  case lwu =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  case lb_via_static_match =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  case lh_via_static_match =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  case lw_via_static_match =>
    exact
      { initialState := generatedTraceAtEnvelope.initialState
        rows := generatedTraceAtEnvelope.rows
        fullTrace :=
          generatedTraceAtEnvelope.generatedTrace.toAcceptedFullMemoryBusRowsTrace
        selected :=
            SelectedLoadMemoryBusReadRowCursor.of_prefix_main_read_match
              generatedTraceAtEnvelope.selectedPrefix (by assumption) }
  all_goals exact ()

/-- Derive accepted raw-row trace evidence from the granular construction
    burden for this envelope. -/
def OpEnvelope.acceptedFullMemoryBusRowsTraceAtEnvelope_of_construction
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope) :
    env.AcceptedFullMemoryBusRowsTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope,
      OpEnvelope.AcceptedFullMemoryBusRowsTraceAtEnvelope] at construction ⊢
  all_goals
    first
    | exact ()
    | exact acceptedLoadFullMemoryBusRowsTraceAtCursor_of_construction state _
        (acceptedLoadFullMemoryBusRowsTraceConstructionAtCursor_of_globalTrace
          state _ construction)

/-- Derive accepted memory-bus event trace evidence from accepted raw
    memory-bus rows and the selected read-row cursor for this envelope. -/
def OpEnvelope.acceptedFullMemoryBusTraceAtEnvelope_of_rowsTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedFullMemoryBusRowsTraceAtEnvelope) :
    env.AcceptedFullMemoryBusTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullMemoryBusRowsTraceAtEnvelope,
      OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope] at construction ⊢
  all_goals
    first
    | exact ()
    | exact acceptedLoadFullMemoryBusTraceAtCursor_of_rowsTrace
        state _ construction

/-- Derive lower memory-bus execution replay evidence from accepted full-trace
    data and the selected read cursor for this envelope. -/
def OpEnvelope.acceptedMemoryBusExecutionTraceAtEnvelope_of_fullTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedFullMemoryBusTraceAtEnvelope) :
    env.AcceptedMemoryBusExecutionTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedFullMemoryBusTraceAtEnvelope,
      OpEnvelope.AcceptedMemoryBusExecutionTraceAtEnvelope] at construction ⊢
  all_goals
    first
    | exact ()
    | exact acceptedLoadMemoryBusExecutionTraceAtCursor_of_fullTrace
        state _ construction

/-- Derive selected full-memory trace evidence from chronological memory-bus
    execution trace evidence. -/
def OpEnvelope.acceptedFullMemoryTraceAtEnvelope_of_memoryBusExecutionTraceAtEnvelope
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedMemoryBusExecutionTraceAtEnvelope) :
    env.AcceptedFullMemoryTraceAtEnvelope := by
  cases env <;>
    simp [OpEnvelope.AcceptedMemoryBusExecutionTraceAtEnvelope,
      OpEnvelope.AcceptedFullMemoryTraceAtEnvelope] at construction ⊢
  all_goals
    first
    | exact ()
    | exact acceptedLoadMemoryTraceAtCursor_of_memoryBusExecutionTrace
        state _ construction

/-- Concrete construction payload for the accepted Mem trace used by this
    envelope.

    This is the theorem hook for the missing accepted-trace-to-`OpEnvelope`
    layer: global construction code should build this object from accepted
    full-trace data. The compliance theorem consumes this structured evidence
    and derives the final `acceptedMemoryTraceContext` proposition internally. -/
structure OpEnvelope.AcceptedMemoryTraceConstruction
    (env : OpEnvelope state m r_main) : Type where
  trace : List ZiskFv.ZiskCircuit.MemTrace.MemEvent
  context :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemTraceForState state trace
  selected : env.selectedLoadEventInTrace trace

/-- Turn the concrete accepted-memory construction object into the proposition
    consumed by the load-memory projection theorem. -/
theorem OpEnvelope.acceptedMemoryTraceContext_of_construction
    (env : OpEnvelope state m r_main)
    (construction : env.AcceptedMemoryTraceConstruction) :
    env.acceptedMemoryTraceContext := by
  exact ⟨construction.trace, construction.context, construction.selected⟩

/-- Derive the per-load accepted-memory burden from the shared accepted trace
    context exposed at the global theorem boundary. -/
theorem OpEnvelope.acceptedMemoryTraceBurden_of_context
    (env : OpEnvelope state m r_main)
    (h_context : env.acceptedMemoryTraceContext) :
    env.acceptedMemoryTraceBurden := by
  cases env <;>
    simp [OpEnvelope.acceptedMemoryTraceContext,
      OpEnvelope.selectedLoadEventInTrace,
      OpEnvelope.acceptedMemoryTraceBurden,
      ZiskFv.EquivCore.Promises.LoadPromises.memoryBurden] at h_context ⊢
  all_goals
    try exact trivial
    exact ZiskFv.ZiskCircuit.MemTrace.loadMemoryBurden_of_accepted_trace_split_nonempty
      state _ h_context rfl

/-- Project the dispatcher-facing memory burden from the accepted Mem-trace
    obligation exposed at the global theorem boundary. -/
theorem OpEnvelope.memoryBurden_of_acceptedMemoryTraceBurden
    (env : OpEnvelope state m r_main)
    (h_trace : env.acceptedMemoryTraceBurden) :
    env.memoryBurden := by
  cases env <;> exact h_trace

/-- Marker for route pins, message equality, row equality, and bus-match facts
    carried by `OpEnvelope` constructors. -/
def OpEnvelope.routeBurden
    (_env : OpEnvelope state m r_main) : Prop :=
  True

/-- Public marker for the completeness/witness burden hidden inside an
    `OpEnvelope`.

    The current compliance theorem is not a global accepted-trace
    completeness theorem: an `OpEnvelope` already carries row specs, table
    specs, provider-row membership, and route pins. Requiring this predicate at
    the public theorem boundary makes that caller burden explicit without
    changing the existing wrapper proofs. Load-memory replay evidence is
    exposed separately by
    `AcceptedAirMainMemFullTraceConstructionAtEnvelope`, so the public theorem
    no longer hides that obligation under this structural completeness marker. -/
def OpEnvelope.completenessBurden
    (env : OpEnvelope state m r_main) : Prop :=
  env.rowSpecBurden
    ∧ env.tableProviderBurden
    ∧ env.routeBurden

end ZiskFv.Compliance
