import ZiskFv.Compliance.OpEnvelope

/-!
# Aeneas bridge audit predicate

The main Lake proof does not yet import generated Aeneas Lean and derive every
row-provenance/source-lane field from the extracted production lowerer.  The
corresponding facts are carried by `OpEnvelope` constructors as ordinary proof
fields.  This file keeps the representative bridge predicate and
extracted-shape constructors available for audit and generated-row-shape
integration. The `aeneasBridgeTrust` predicate is deliberately explicit as a
global theorem hypothesis until generated Aeneas Lean is imported by main Lake
and proves these fields instead.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- The Aeneas-backed row-lowering facts currently carried by `OpEnvelope`.

This predicate makes representative bridge facts that replaced the retired
hand-written Lean transpiler visible for local audit. The global theorem assumes
the predicate explicitly until generated Aeneas Lean is imported by the main
proof. The existing wrappers still take their full proof-field parameter lists,
so the caller-burden ledgers remain the mechanical inventory of fields that
generated/full-ensemble proof integration can later remove. -/
def OpEnvelope.aeneasBridgeTrust : OpEnvelope state m r_main → Prop
  | .beq .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_EQ
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset2 r_main = 4
  | .bne .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_EQ
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
  | .blt .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_LT
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset2 r_main = 4
  | .bge .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_LT
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
  | .bltu .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_LTU
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset2 r_main = 4
  | .bgeu .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_LTU
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
  | .fence .. =>
      m.is_external_op r_main = 0
      ∧ m.op r_main = ZiskFv.Trusted.OP_FLAG
  | .lui _ imm _ _ _ _ _ provenance _ _ _ _ _ =>
      Nonempty (MainRowProvenance m r_main)
      ∧ MainRowProvenance.LuiRowMode provenance
      ∧ (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat
      ∧ (m.b_1 r_main).val
          = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296
  | .auipc auipc_input _ _ _ _ _ _ _ provenance _ _ _ _ _ _ _ =>
      Nonempty (MainRowProvenance m r_main)
      ∧ MainRowProvenance.AuipcRowMode provenance
      ∧ (m.jmp_offset2 r_main).val
          = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      ∧ (m.pc r_main).val = auipc_input.PC.toNat
  | .auipc_x0 .. =>
      True
  | .jal jal_input _ _ _ _ _ _ _ _ provenance _ _ _ _ _ _ _ _ _ =>
      Nonempty (MainRowProvenance m r_main)
      ∧ MainRowProvenance.JalRowMode provenance
      ∧ m.jmp_offset2 r_main = 4
      ∧ (m.pc r_main).val = jal_input.PC.toNat
  | .jal_x0 .. =>
      True
  | .jalr jalr_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 1
      ∧ m.store_pc r_main = 1
      ∧ (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat
  | .add_via_binary add_input _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      add_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ add_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .add_via_binaryadd _ r1 r2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      m.a_0 r_main =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
            (regidx_to_fin r1))
      ∧ m.a_1 r_main =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
            (regidx_to_fin r1))
      ∧ m.b_0 r_main =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
            (regidx_to_fin r2))
      ∧ m.b_1 r_main =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
            (regidx_to_fin r2))
      ∧ m.m32 r_main = 0
  | .addi_via_binary addi_input _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      addi_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 addi_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .addi_via_binaryadd _ r1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      m.a_0 r_main =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
            (regidx_to_fin r1))
      ∧ m.a_1 r_main =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
            (regidx_to_fin r1))
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
  | .addw addw_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
      ∧ (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
  | .subw subw_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
      ∧ (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
  | .addiw addiw_input _ _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ =>
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
  | .sub sub_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      sub_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sub_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .and and_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      and_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ and_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .or or_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      or_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ or_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .xor xor_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      xor_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ xor_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slt slt_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      slt_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ slt_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sltu sltu_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      sltu_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sltu_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .andi andi_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      andi_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 andi_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .ori ori_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      ori_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 ori_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .xori xori_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      xori_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 xori_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slti slti_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      m.m32 r_main = 0
      ∧ slti_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sltiu sltiu_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      m.m32 r_main = 0
      ∧ sltiu_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sll sll_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      sll_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sll_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srl srl_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      srl_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srl_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sra sra_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      sra_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sra_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sllw sllw_input _ _ _ providerTable providerRow .. =>
      (Sail.BitVec.extractLsb sllw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sllw_input.r2_val.toNat % 32 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srlw srlw_input _ _ _ providerTable providerRow .. =>
      (Sail.BitVec.extractLsb srlw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srlw_input.r2_val.toNat % 32 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sraw sraw_input _ _ _ providerTable providerRow .. =>
      (Sail.BitVec.extractLsb sraw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sraw_input.r2_val.toNat % 32 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slliw slliw_input _ _ providerTable providerRow .. =>
      (Sail.BitVec.extractLsb slliw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ slliw_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srliw srliw_input _ _ providerTable providerRow .. =>
      (Sail.BitVec.extractLsb srliw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srliw_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sraiw sraiw_input _ _ providerTable providerRow .. =>
      (Sail.BitVec.extractLsb sraiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sraiw_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slli slli_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      slli_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ slli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srli srli_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      srli_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srai srai_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      srai_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srai_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sb sb_input .. =>
      m.ind_width r_main = 1
      ∧ m.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val
      ∧ m.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val
  | .sh sh_input .. =>
      m.ind_width r_main = 2
      ∧ m.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val
      ∧ m.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val
  | .sw sw_input .. =>
      m.ind_width r_main = 4
      ∧ m.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val
      ∧ m.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val
  | .sd sd_input .. =>
      m.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val
      ∧ m.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val
  | .ld .. =>
      m.ind_width r_main = 8
  | .lbu .. =>
      m.ind_width r_main = 1
  | .lhu .. =>
      m.ind_width r_main = 2
  | .lwu .. =>
      m.ind_width r_main = 4
  | .lb_via_static_match .. =>
      m.ind_width r_main = 1
  | .lh_via_static_match .. =>
      m.ind_width r_main = 2
  | .lw_via_static_match .. =>
      m.ind_width r_main = 4
  | .mul .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_MUL
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .mulh .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_MULH
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .mulhu .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_MULUH
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .mulhsu .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_MULSUH
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .mulw .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_MUL_W
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .div .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_DIV
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .divu .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_DIVU
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .divw .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_DIV_W
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .divuw .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_DIVU_W
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .rem .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_REM
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .remu .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_REMU
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .remw .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_REM_W
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
  | .remuw .. =>
      m.is_external_op r_main = 1
      ∧ m.op r_main = ZiskFv.Trusted.OP_REMU_W
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4

/-- Construct the BEQ branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.beqOfExtractedShape
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.beq beq_input ops promises

/-- The BEQ bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_beqOfExtractedShape
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.beqOfExtractedShape
      beq_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset2 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.beqOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.eqPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset2_of_extracted_shape provenance h_jmp_offset2⟩

/-- Construct the BNE branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bneOfExtractedShape
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bne bne_input ops promises

/-- The BNE bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bneOfExtractedShape
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bneOfExtractedShape
      bne_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset1 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bneOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.eqPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset1_of_extracted_shape provenance h_jmp_offset1⟩

/-- Construct the BLT branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bltOfExtractedShape
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.blt blt_input ops promises

/-- The BLT bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bltOfExtractedShape
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bltOfExtractedShape
      blt_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset2 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bltOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset2_of_extracted_shape provenance h_jmp_offset2⟩

/-- Construct the BGE branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bgeOfExtractedShape
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bge bge_input ops promises

/-- The BGE bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bgeOfExtractedShape
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bgeOfExtractedShape
      bge_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset1 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bgeOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset1_of_extracted_shape provenance h_jmp_offset1⟩

/-- Construct the BLTU branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bltuOfExtractedShape
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bltu bltu_input ops promises

/-- The BLTU bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bltuOfExtractedShape
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bltuOfExtractedShape
      bltu_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset2 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bltuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset2_of_extracted_shape provenance h_jmp_offset2⟩

/-- Construct the BGEU branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bgeuOfExtractedShape
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bgeu bgeu_input ops promises

/-- The BGEU bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bgeuOfExtractedShape
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bgeuOfExtractedShape
      bgeu_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset1 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bgeuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset1_of_extracted_shape provenance h_jmp_offset1⟩

/-- Construct the LUI envelope while deriving its row-mode field from
production-extracted row-shape equalities. -/
def OpEnvelope.luiOfExtractedShape
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_lui_subset : ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    OpEnvelope state m r_main :=
  OpEnvelope.lui lui_input imm rd next_pc exec_row e_rd store_pc_mem provenance
    (MainRowProvenance.luiRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc)
    h_lui_subset h_imm_lo_nat h_imm_hi_nat promises

/-- The LUI bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic LUI facts. -/
theorem OpEnvelope.aeneasBridgeTrust_luiOfExtractedShape
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_lui_subset : ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    (OpEnvelope.luiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lui_input imm rd next_pc exec_row e_rd store_pc_mem provenance
      h_op h_internal h_m32 h_set_pc h_store_pc
      h_lui_subset h_imm_lo_nat h_imm_hi_nat promises).aeneasBridgeTrust := by
  unfold OpEnvelope.luiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨⟨provenance⟩,
    MainRowProvenance.luiRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc,
    h_imm_lo_nat,
    h_imm_hi_nat⟩

/-- Construct the AUIPC envelope while deriving its row-mode field from
production-extracted row-shape equalities. -/
def OpEnvelope.auipcOfExtractedShape
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_auipc_subset : ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m r_main next_pc)
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
    OpEnvelope state m r_main :=
  OpEnvelope.auipc auipc_input imm rd exec_row e_rd nextPC_val next_pc
    store_pc_mem provenance
    (MainRowProvenance.auipcRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc)
    h_auipc_subset h_offset_bridge h_pc_bridge promises
    h_no_wrap h_pc_offset_lt_2_32

/-- The AUIPC bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic AUIPC facts. -/
theorem OpEnvelope.aeneasBridgeTrust_auipcOfExtractedShape
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_auipc_subset : ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m r_main next_pc)
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
    (OpEnvelope.auipcOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      auipc_input imm rd exec_row e_rd nextPC_val next_pc
      store_pc_mem provenance
      h_op h_internal h_m32 h_set_pc h_store_pc
      h_auipc_subset h_offset_bridge h_pc_bridge promises
      h_no_wrap h_pc_offset_lt_2_32).aeneasBridgeTrust := by
  unfold OpEnvelope.auipcOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨⟨provenance⟩,
    MainRowProvenance.auipcRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc,
    h_offset_bridge,
    h_pc_bridge⟩

/-- Construct the JAL envelope while deriving its row-mode field from
production-extracted row-shape equalities. -/
def OpEnvelope.jalOfExtractedShape
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
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
    OpEnvelope state m r_main :=
  OpEnvelope.jal jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
    store_pc_mem provenance
    (MainRowProvenance.jalRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc)
    h_jal_subset h_jmp2 h_pc_bridge promises h_input_imm h_not_throws
    h_pc_bound h_pc_offset_lt_2_32

/-- The JAL bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic JAL facts. -/
theorem OpEnvelope.aeneasBridgeTrust_jalOfExtractedShape
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
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
    (OpEnvelope.jalOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
      store_pc_mem provenance
      h_op h_internal h_m32 h_set_pc h_store_pc
      h_jal_subset h_jmp2 h_pc_bridge promises h_input_imm h_not_throws
      h_pc_bound h_pc_offset_lt_2_32).aeneasBridgeTrust := by
  unfold OpEnvelope.jalOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨⟨provenance⟩,
    MainRowProvenance.jalRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc,
    h_jmp2,
    h_pc_bridge⟩

/-- Construct the JALR envelope while deriving its final-row activation,
opcode, and control pins from production-extracted row-shape equalities. -/
def OpEnvelope.jalrOfExtractedShape
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
    (h_set_pc_shape : provenance.extractedRow.setPc = true)
    (h_store_pc_shape : provenance.extractedRow.storePc = true)
    (h_flag : m.flag r_main = 0)
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
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    OpEnvelope state m r_main :=
  let control := MainRowProvenance.jalrControl_of_extracted_shape provenance
    h_m32_shape h_set_pc_shape h_store_pc_shape
  OpEnvelope.jalr jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd
    nextPC_val next_pc store_pc_mem
    (MainRowProvenance.jalrPins_of_extracted_shape provenance h_op h_external)
    h_flag control.1 control.2.1 control.2.2 h_jalr_subset promises
    h_input_imm h_input_rs1 h_cur_privilege h_mseccfg h_link_bridge h_pc_bound
    h_pc_offset_lt_2_32

/-- The JALR bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic JALR facts. -/
theorem OpEnvelope.aeneasBridgeTrust_jalrOfExtractedShape
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
    (h_set_pc_shape : provenance.extractedRow.setPc = true)
    (h_store_pc_shape : provenance.extractedRow.storePc = true)
    (h_flag : m.flag r_main = 0)
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
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (OpEnvelope.jalrOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val next_pc
      store_pc_mem provenance
      h_op h_external h_m32_shape h_set_pc_shape h_store_pc_shape
      h_flag h_jalr_subset promises h_input_imm h_input_rs1 h_cur_privilege
      h_mseccfg h_link_bridge h_pc_bound h_pc_offset_lt_2_32).aeneasBridgeTrust := by
  let control := MainRowProvenance.jalrControl_of_extracted_shape provenance
    h_m32_shape h_set_pc_shape h_store_pc_shape
  unfold OpEnvelope.jalrOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_flag, control.1, control.2.1, control.2.2, h_link_bridge⟩

/-- Construct the FENCE envelope while deriving its activation/opcode pins from
production-extracted row-shape equalities. -/
def OpEnvelope.fenceOfExtractedShape
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.fence fence_input fm pred succ rs rd exec_row
    (MainRowProvenance.fencePins_of_extracted_shape provenance h_op h_internal)
    promises

/-- The FENCE bridge predicate is trivial, but this theorem records that the
real FENCE envelope pins can be filled from extracted row-shape equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) :
    (OpEnvelope.fenceOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      fence_input fm pred succ rs rd exec_row provenance h_op h_internal
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.fenceOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.fencePins_of_extracted_shape provenance h_op h_internal
  exact ⟨pins.main_active, pins.main_op⟩

/-- Transport the Main AIR `store_pc = 0` fact from extracted row-shape
provenance to the Clean row consumed by store wrappers. -/
theorem MainRowProvenance.cleanStorePcZero_of_extracted_shape
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_store_pc : provenance.extractedRow.storePc = false)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main) :
    (eval mainEnv mainRowVar).core.store_pc = 0 := by
  rw [h_main_row]
  simpa [ZiskFv.AirsClean.Main.rowAt] using
    MainRowProvenance.storePcZero_of_extracted_shape provenance h_store_pc

/-- Construct the SB store envelope while deriving its Main `OP_COPYB` pins,
store width, and Clean `store_pc` fact from extracted row-shape equalities. -/
def OpEnvelope.sbOfExtractedShape
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    OpEnvelope state m r_main :=
  OpEnvelope.sb sb_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value h_m1 h_m2 h_m3 h_m4 h_m5 h_m6 h_m7

/-- Construct the SH store envelope while deriving its Main store shape fields
from extracted row-shape equalities. -/
def OpEnvelope.shOfExtractedShape
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    OpEnvelope state m r_main :=
  OpEnvelope.sh sh_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value h_m2 h_m3 h_m4 h_m5 h_m6 h_m7

/-- Construct the SW store envelope while deriving its Main store shape fields
from extracted row-shape equalities. -/
def OpEnvelope.swOfExtractedShape
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    OpEnvelope state m r_main :=
  OpEnvelope.sw sw_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value h_m4 h_m5 h_m6 h_m7

/-- Construct the SD store envelope while deriving its Main `OP_COPYB` pins and
Clean `store_pc` fact from extracted row-shape equalities. -/
def OpEnvelope.sdOfExtractedShape
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
    OpEnvelope state m r_main :=
  OpEnvelope.sd sd_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value

/-- The SB bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sbOfExtractedShape
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    (OpEnvelope.sbOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sb_input regs bus provenance h_op h_internal h_width h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value h_m1 h_m2 h_m3 h_m4 h_m5 h_m6
      h_m7).aeneasBridgeTrust := by
  unfold OpEnvelope.sbOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width,
    h_b0_value, h_b1_value⟩

/-- The SH bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_shOfExtractedShape
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    (OpEnvelope.shOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sh_input regs bus provenance h_op h_internal h_width h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value h_m2 h_m3 h_m4 h_m5 h_m6
      h_m7).aeneasBridgeTrust := by
  unfold OpEnvelope.shOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width,
    h_b0_value, h_b1_value⟩

/-- The SW bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_swOfExtractedShape
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    (OpEnvelope.swOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sw_input regs bus provenance h_op h_internal h_width h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value h_m4 h_m5 h_m6 h_m7).aeneasBridgeTrust := by
  unfold OpEnvelope.swOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width,
    h_b0_value, h_b1_value⟩

/-- The SD bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sdOfExtractedShape
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
    (OpEnvelope.sdOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sd_input regs bus provenance h_op h_internal h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value).aeneasBridgeTrust := by
  unfold OpEnvelope.sdOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_b0_value, h_b1_value⟩

/-- Construct the LD load envelope while deriving its Main `OP_COPYB` pins and
Clean `store_pc` fact from extracted row-shape equalities. -/
def OpEnvelope.ldOfExtractedShape
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (_h_width : provenance.extractedRow.indWidth = 8)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.ld ld_input regs mem bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- The LD bridge predicate is derivable for the envelope constructed from
extracted load row-shape equalities and the remaining dynamic load facts. -/
theorem OpEnvelope.aeneasBridgeTrust_ldOfExtractedShape
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 8)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.ldOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      ld_input regs mem bus provenance h_op h_internal h_width
      h_store_pc_shape promises r_mem h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.ldOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- Construct the LBU load envelope while deriving its Main `OP_COPYB` pins,
width, and Clean `store_pc` fact from extracted row-shape equalities. -/
def OpEnvelope.lbuOfExtractedShape
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.lbu lbu_input regs mem bus align
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- The LBU bridge predicate is derivable for the envelope constructed from
extracted load row-shape equalities and the remaining dynamic load facts. -/
theorem OpEnvelope.aeneasBridgeTrust_lbuOfExtractedShape
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.lbuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lbu_input regs mem bus align provenance h_op h_internal h_width
      h_store_pc_shape promises r_mem h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.lbuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- Construct the LHU load envelope while deriving its Main load shape fields
from extracted row-shape equalities. -/
def OpEnvelope.lhuOfExtractedShape
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.lhu lhu_input regs mem bus align
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- The LHU bridge predicate is derivable for the envelope constructed from
extracted load row-shape equalities and the remaining dynamic load facts. -/
theorem OpEnvelope.aeneasBridgeTrust_lhuOfExtractedShape
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.lhuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lhu_input regs mem bus align provenance h_op h_internal h_width
      h_store_pc_shape promises r_mem h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.lhuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- Construct the LWU load envelope while deriving its Main load shape fields
from extracted row-shape equalities. -/
def OpEnvelope.lwuOfExtractedShape
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.lwu lwu_input regs mem bus align
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- The LWU bridge predicate is derivable for the envelope constructed from
extracted load row-shape equalities and the remaining dynamic load facts. -/
theorem OpEnvelope.aeneasBridgeTrust_lwuOfExtractedShape
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (align : ZiskFv.Compliance.MemAlignWitness m r_main bus.e1)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.lwuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lwu_input regs mem bus align provenance h_op h_internal h_width
      h_store_pc_shape promises r_mem h_mainEval h_providerEval h_msg
      h_main_row h_mem_row h_main_spec h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel
      h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.lwuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- Construct the LB signed-load envelope while deriving its Main
`OP_SIGNEXTEND_B` pins and Clean `store_pc` fact from extracted row-shape
equalities. -/
def OpEnvelope.lbOfExtractedShape
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSignextendB)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.lb_via_static_match lb_input regs mem v r_binary offset env
    h_static h_match bus
    (MainRowProvenance.signextendBPins_of_extracted_shape provenance h_op h_external)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- Construct the LH signed-load envelope while deriving its Main
`OP_SIGNEXTEND_H` pins and Clean `store_pc` fact from extracted row-shape
equalities. -/
def OpEnvelope.lhOfExtractedShape
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSignextendH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.lh_via_static_match lh_input regs mem v r_binary offset env
    h_static h_match bus
    (MainRowProvenance.signextendHPins_of_extracted_shape provenance h_op h_external)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- Construct the LW signed-load envelope while deriving its Main
`OP_SIGNEXTEND_W` pins and Clean `store_pc` fact from extracted row-shape
equalities. -/
def OpEnvelope.lwOfExtractedShape
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSignextendW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.lw_via_static_match lw_input regs mem v r_binary offset env
    h_static h_match bus
    (MainRowProvenance.signextendWPins_of_extracted_shape provenance h_op h_external)
    promises r_mem h_mainEval h_providerEval h_msg h_main_row h_mem_row
    h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
    h_mem_sel h_mem_wr

/-- The LB bridge predicate is derivable for the envelope constructed from
extracted signed-load row-shape equalities and the remaining dynamic facts. -/
theorem OpEnvelope.aeneasBridgeTrust_lbOfExtractedShape
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSignextendB)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.lbOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lb_input regs mem v r_binary offset env h_static h_match bus
      provenance h_op h_external h_width h_store_pc_shape promises r_mem
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
      h_mem_sel h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.lbOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- The LH bridge predicate is derivable for the envelope constructed from
extracted signed-load row-shape equalities and the remaining dynamic facts. -/
theorem OpEnvelope.aeneasBridgeTrust_lhOfExtractedShape
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSignextendH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.lhOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lh_input regs mem v r_binary offset env h_static h_match bus
      provenance h_op h_external h_width h_store_pc_shape promises r_mem
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
      h_mem_sel h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.lhOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- The LW bridge predicate is derivable for the envelope constructed from
extracted signed-load row-shape equalities and the remaining dynamic facts. -/
theorem OpEnvelope.aeneasBridgeTrust_lwOfExtractedShape
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSignextendW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
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
    (h_mem_wr : mem.wr r_mem = 0) :
    (OpEnvelope.lwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lw_input regs mem v r_binary offset env h_static h_match bus
      provenance h_op h_external h_width h_store_pc_shape promises r_mem
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx
      h_mem_sel h_mem_wr).aeneasBridgeTrust := by
  unfold OpEnvelope.lwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width

/-- Construct the MUL ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulOfExtractedShape
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMul)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
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
    OpEnvelope state m r_main :=
  OpEnvelope.mul mul_input r1 r2 rd srs1 srs2 bus v r_a
    (MainRowProvenance.mulPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value

/-- The MUL bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulOfExtractedShape
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMul)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
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
    (OpEnvelope.mulOfExtractedShape
      mul_input r1 r2 rd srs1 srs2 bus v r_a provenance h_op h_external
      h_m32 h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULH ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulhOfExtractedShape
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
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
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulh mulh_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulHPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value h_sign_a h_sign_b

/-- The MULH bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulhOfExtractedShape
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
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
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0) :
    (OpEnvelope.mulhOfExtractedShape
      mulh_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value h_sign_a h_sign_b).aeneasBridgeTrust := by
  unfold OpEnvelope.mulhOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulHPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULHU ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulhuOfExtractedShape
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
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
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulhu mulhu_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulUHPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value

/-- The MULHU bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulhuOfExtractedShape
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
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
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.mulhuOfExtractedShape
      mulhu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulhuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulUHPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULHSU ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulhsuOfExtractedShape
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulSUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
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
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulhsu mulhsu_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulSUHPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value h_sign_a

/-- The MULHSU bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulhsuOfExtractedShape
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulSUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
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
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0) :
    (OpEnvelope.mulhsuOfExtractedShape
      mulhsu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value h_sign_a).aeneasBridgeTrust := by
  unfold OpEnvelope.mulhsuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulSUHPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULW ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulwOfExtractedShape
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
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
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulw mulw_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulWPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_a23 h_b23 h_sext_choice
    h_rs1_value h_rs2_value

/-- The MULW bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulwOfExtractedShape
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
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
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    (OpEnvelope.mulwOfExtractedShape
      mulw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_a23 h_b23 h_sext_choice h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIV ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divOfExtractedShape
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDiv)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
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
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.div div_input r1 r2 rd bus v r_a
    (MainRowProvenance.divPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_no_overflow h_row_constraints h_boundary
    arith_table arith_chunk_ranges arith_carry_ranges
    h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
    h_r_le h_r_sign

/-- The DIV bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divOfExtractedShape
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDiv)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
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
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    (OpEnvelope.divOfExtractedShape
      div_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_no_overflow h_row_constraints h_boundary arith_table
      arith_chunk_ranges arith_carry_ranges
      h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
      h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.divOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIVU ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divuOfExtractedShape
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
    OpEnvelope state m r_main :=
  OpEnvelope.divu divu_input r1 r2 rd bus v r_a
    (MainRowProvenance.divUPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_rs1_value h_rs2_value

/-- The DIVU bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divuOfExtractedShape
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
    (OpEnvelope.divuOfExtractedShape
      divu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.divuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divUPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIVW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divwOfExtractedShape
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.divw divw_input r1 r2 rd bus v r_a
    (MainRowProvenance.divWPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
    h_rs1_value h_rs2_value h_op2_ne h_no_overflow h_r_le h_r_sign

/-- The DIVW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divwOfExtractedShape
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    (OpEnvelope.divwOfExtractedShape
      divw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
      h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
      h_rs1_value h_rs2_value h_op2_ne h_no_overflow h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.divwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIVUW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divuwOfExtractedShape
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    OpEnvelope state m r_main :=
  OpEnvelope.divuw divuw_input r1 r2 rd bus v r_a
    (MainRowProvenance.divUWPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_b23 h_c23
    h_sext_choice h_rs1_value h_rs2_value

/-- The DIVUW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divuwOfExtractedShape
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (OpEnvelope.divuwOfExtractedShape
      divuw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary promises
      arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_b23 h_c23 h_sext_choice h_rs1_value
      h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.divuwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divUWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REM ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remOfExtractedShape
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRem)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (rem_input.r1_val.toInt = -(2:ℤ)^63 ∧ rem_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
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
    OpEnvelope state m r_main :=
  OpEnvelope.rem rem_input r1 r2 rd bus v r_a
    (MainRowProvenance.remPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_op2_ne h_no_overflow h_row_constraints
    arith_table arith_chunk_ranges arith_carry_ranges
    h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
    h_r_le h_r_sign

/-- The REM bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remOfExtractedShape
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRem)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (rem_input.r1_val.toInt = -(2:ℤ)^63 ∧ rem_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
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
    (OpEnvelope.remOfExtractedShape
      rem_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary promises
      arith_mem bounds h_op2_ne h_no_overflow h_row_constraints arith_table
      arith_chunk_ranges arith_carry_ranges h_na_bool
      h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
      h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.remOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REMU ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remuOfExtractedShape
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
    OpEnvelope state m r_main :=
  OpEnvelope.remu remu_input r1 r2 rd bus v r_a
    (MainRowProvenance.remUPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_rs1_value h_rs2_value

/-- The REMU bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remuOfExtractedShape
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
    (OpEnvelope.remuOfExtractedShape
      remu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.remuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remUPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REMW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remwOfExtractedShape
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.remw remw_input r1 r2 rd bus v r_a
    (MainRowProvenance.remWPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
    h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w h_r_le h_r_sign

/-- The REMW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remwOfExtractedShape
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt) :
    (OpEnvelope.remwOfExtractedShape
      remw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
      h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
      h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.remwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REMUW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remuwOfExtractedShape
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    OpEnvelope state m r_main :=
  OpEnvelope.remuw remuw_input r1 r2 rd bus v r_a
    (MainRowProvenance.remUWPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_b23 h_c23
    h_sext_choice h_rs1_value h_rs2_value

/-- The REMUW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remuwOfExtractedShape
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
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
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (OpEnvelope.remuwOfExtractedShape
      remuw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_b23 h_c23 h_sext_choice h_rs1_value
      h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.remuwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remUWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the ADD Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addViaBinaryOfExtractedShape
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAdd)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.add_via_binary add_input r1 r2 rd bus
    (MainRowProvenance.addPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The ADD Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addViaBinaryOfExtractedShape
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAdd)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addViaBinaryOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      add_input r1 r2 rd bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addViaBinaryOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the ADDW Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addwOfExtractedShape
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.addw addw_input r1 r2 rd v bus
    (MainRowProvenance.addwPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_extract h_input_r2_extract h_lane_rd promises

/-- The ADDW Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addwOfExtractedShape
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      addw_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_extract, h_input_r2_extract⟩

/-- Construct the SUBW Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.subwOfExtractedShape
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSubW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.subw subw_input r1 r2 rd v bus
    (MainRowProvenance.subwPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_extract h_input_r2_extract h_lane_rd promises

/-- The SUBW Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_subwOfExtractedShape
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSubW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.subwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      subw_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.subwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_extract, h_input_r2_extract⟩

/-- Construct the ADDIW Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addiwOfExtractedShape
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_addiw_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main addiw_input.imm)
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
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.addiw addiw_input r1 rd imm v bus
    (MainRowProvenance.addwPins_of_extracted_shape provenance h_op h_external)
    h_addiw_subset providerTable providerRow h_component h_table_spec
    h_provider_row h_match_static h_input_r1_extract h_lane_rd promises

/-- The ADDIW Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addiwOfExtractedShape
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_addiw_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main addiw_input.imm)
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
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addiwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      addiw_input r1 rd imm v bus provenance h_op h_external h_addiw_subset
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_extract h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addiwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact h_input_r1_extract

/-- Construct the SUB Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.subOfExtractedShape
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSub)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sub sub_input r1 r2 rd v bus
    (MainRowProvenance.subPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The SUB Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_subOfExtractedShape
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSub)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.subOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sub_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.subOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the AND Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.andOfExtractedShape
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.and and_input r1 r2 rd v bus
    (MainRowProvenance.andPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The AND Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_andOfExtractedShape
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.andOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      and_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.andOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the OR Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.orOfExtractedShape
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opOr)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.or or_input r1 r2 rd v bus
    (MainRowProvenance.orPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The OR Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_orOfExtractedShape
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opOr)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.orOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      or_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.orOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the XOR Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.xorOfExtractedShape
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opXor)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.xor xor_input r1 r2 rd v bus
    (MainRowProvenance.xorPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The XOR Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_xorOfExtractedShape
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opXor)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.xorOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      xor_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.xorOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the SLT Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.sltOfExtractedShape
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.slt slt_input r1 r2 rd v bus
    (MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The SLT Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sltOfExtractedShape
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slt_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the SLTU Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.sltuOfExtractedShape
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sltu sltu_input r1 r2 rd v bus
    (MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The SLTU Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sltuOfExtractedShape
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sltu_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

def OpEnvelope.andiOfExtractedShape
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (h_andi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.andi andi_input r1 rd imm v bus
    (MainRowProvenance.andPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row h_andi_subset h_lane_rd
    promises

theorem OpEnvelope.aeneasBridgeTrust_andiOfExtractedShape
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (h_andi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.andiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      andi_input r1 rd imm v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_andi_subset h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.andiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

def OpEnvelope.oriOfExtractedShape
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opOr)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (h_ori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.ori ori_input r1 rd imm v bus
    (MainRowProvenance.orPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row h_ori_subset h_lane_rd
    promises

theorem OpEnvelope.aeneasBridgeTrust_oriOfExtractedShape
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opOr)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (h_ori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.oriOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      ori_input r1 rd imm v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_ori_subset h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.oriOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

def OpEnvelope.xoriOfExtractedShape
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opXor)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (h_xori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.xori xori_input r1 rd imm v bus
    (MainRowProvenance.xorPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row h_xori_subset h_lane_rd
    promises

theorem OpEnvelope.aeneasBridgeTrust_xoriOfExtractedShape
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opXor)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (h_xori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.xoriOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      xori_input r1 rd imm v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_xori_subset h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.xoriOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

def OpEnvelope.sltiOfExtractedShape
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : slti_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_slti_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.slti slti_input r1 rd imm v bus
    (MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static
    (by simpa [boolF, h_m32_shape] using provenance.m32_eq)
    h_input_r1_row h_slti_subset h_lane_rd promises

theorem OpEnvelope.aeneasBridgeTrust_sltiOfExtractedShape
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : slti_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_slti_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slti_input r1 rd imm v bus provenance h_op h_external h_m32_shape
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_slti_subset h_lane_rd
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [boolF, h_m32_shape] using provenance.m32_eq, h_input_r1_row⟩

def OpEnvelope.sltiuOfExtractedShape
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : sltiu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_sltiu_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sltiu sltiu_input r1 rd imm v bus
    (MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static
    (by simpa [boolF, h_m32_shape] using provenance.m32_eq)
    h_input_r1_row h_sltiu_subset h_lane_rd promises

theorem OpEnvelope.aeneasBridgeTrust_sltiuOfExtractedShape
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : sltiu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_sltiu_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltiuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sltiu_input r1 rd imm v bus provenance h_op h_external h_m32_shape
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_sltiu_subset h_lane_rd
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltiuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [boolF, h_m32_shape] using provenance.m32_eq, h_input_r1_row⟩

def OpEnvelope.sllOfExtractedShape
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.sll sll_input r1 r2 rd providerTable providerRow bus promises
    (MainRowProvenance.sllPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sllOfExtractedShape
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.sllOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sll_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sllOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srlOfExtractedShape
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.srl srl_input r1 r2 rd providerTable providerRow bus promises
    (MainRowProvenance.srlPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srlOfExtractedShape
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.srlOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srl_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srlOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.sraOfExtractedShape
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.sra sra_input r1 r2 rd providerTable providerRow bus promises
    (MainRowProvenance.sraPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sraOfExtractedShape
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.sraOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sra_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sraOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.sllwOfExtractedShape
    (sllw_input : PureSpec.SllwInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSllW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    OpEnvelope state m r_main :=
  OpEnvelope.sllw sllw_input r1 r2 rd providerTable providerRow bus
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc h_exec_len
    h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult
    h_m1_as h_m2_mult h_m2_as h_rd_idx
    (MainRowProvenance.sllwPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sllwOfExtractedShape
    (sllw_input : PureSpec.SllwInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSllW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (OpEnvelope.sllwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sllw_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as
      h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_component h_table_spec
      h_provider_row h_match h_input_r1_row h_shift_pin_row
      h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sllwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srlwOfExtractedShape
    (srlw_input : PureSpec.SrlwInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrlW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    OpEnvelope state m r_main :=
  OpEnvelope.srlw srlw_input r1 r2 rd providerTable providerRow bus
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc h_exec_len
    h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult
    h_m1_as h_m2_mult h_m2_as h_rd_idx
    (MainRowProvenance.srlwPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srlwOfExtractedShape
    (srlw_input : PureSpec.SrlwInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrlW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (OpEnvelope.srlwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srlw_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as
      h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_component h_table_spec
      h_provider_row h_match h_input_r1_row h_shift_pin_row
      h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srlwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srawOfExtractedShape
    (sraw_input : PureSpec.SrawInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSraW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    OpEnvelope state m r_main :=
  OpEnvelope.sraw sraw_input r1 r2 rd providerTable providerRow bus
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc h_exec_len
    h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult
    h_m1_as h_m2_mult h_m2_as h_rd_idx
    (MainRowProvenance.srawPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srawOfExtractedShape
    (sraw_input : PureSpec.SrawInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSraW)
    (h_external : provenance.extractedRow.isExternalOp = true)
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
    (OpEnvelope.srawOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sraw_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as
      h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_component h_table_spec
      h_provider_row h_match h_input_r1_row h_shift_pin_row
      h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srawOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.slliwOfExtractedShape
    (slliw_input : PureSpec.SlliwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSllW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.slliw slliw_input r1 rd providerTable providerRow bus promises
    (MainRowProvenance.sllwPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_slliwOfExtractedShape
    (slliw_input : PureSpec.SlliwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSllW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.slliwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slliw_input r1 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.slliwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srliwOfExtractedShape
    (srliw_input : PureSpec.SrliwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrlW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.srliw srliw_input r1 rd providerTable providerRow bus promises
    (MainRowProvenance.srlwPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srliwOfExtractedShape
    (srliw_input : PureSpec.SrliwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrlW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.srliwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srliw_input r1 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srliwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.sraiwOfExtractedShape
    (sraiw_input : PureSpec.SraiwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSraW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.sraiw sraiw_input r1 rd providerTable providerRow bus promises
    (MainRowProvenance.srawPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sraiwOfExtractedShape
    (sraiw_input : PureSpec.SraiwInput) (r1 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSraW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.sraiwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sraiw_input r1 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sraiwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.slliOfExtractedShape
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.slli slli_input r1 rd shamt providerTable providerRow bus promises
    (MainRowProvenance.sllPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_slliOfExtractedShape
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.slliOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slli_input r1 rd shamt providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.slliOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srliOfExtractedShape
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.srli srli_input r1 rd shamt providerTable providerRow bus promises
    (MainRowProvenance.srlPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srliOfExtractedShape
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.srliOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srli_input r1 rd shamt providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srliOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.sraiOfExtractedShape
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main :=
  OpEnvelope.srai srai_input r1 rd shamt providerTable providerRow bus promises
    (MainRowProvenance.sraPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sraiOfExtractedShape
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (OpEnvelope.sraiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srai_input r1 rd shamt providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sraiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

end ZiskFv.Compliance
