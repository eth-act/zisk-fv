import ZiskFv.Compliance.OpEnvelope

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

end ZiskFv.Compliance
