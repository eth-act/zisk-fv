import ZiskFv.Completeness.Rv64im.SailDecode.Domain

/-!
# Sail-derived RV64IM decode domain — concat-to-raw-shape bridges

This part holds the `sail_*_concat_eq_raw*` bit-concatenation bridges that
relate Sail's generated encoder concatenations to the `Rv64imShapes.raw*`
constructors, together with their per-field `*_component_eq` helper lemmas and
the alignment / shift side lemmas.  It is part of the split
`ZiskFv.Completeness.Rv64im.SailDecode` module.
-/

namespace ZiskFv.Completeness.SailDecode

open ZiskFv.Completeness

theorem sail_add_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b000#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sub_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0100000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b000#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 32
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sll_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b001#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        1
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_slt_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b010#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        2
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sltu_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b011#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        3
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_xor_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b100#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        4
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_srl_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sra_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0100000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 32
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_or_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b110#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        6
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_and_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b111#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        7
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_addw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b000#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0111011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_subw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0100000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b000#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0111011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 32
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sllw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b001#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0111011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        1
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_srlw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0111011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 0
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sraw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0100000#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0111011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 32
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_mul_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b000#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_mulh_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b001#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        1
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_mulhsu_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b010#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        2
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_mulhu_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b011#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0110011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        3
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_mulw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b000#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0111011#7)))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_div_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (2#2 ++
            (LeanRV64D.Functions.bool_bits_forwards false ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                51#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        4
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_divu_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (2#2 ++
            (LeanRV64D.Functions.bool_bits_forwards true ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                51#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_divw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (2#2 ++
            (LeanRV64D.Functions.bool_bits_forwards false ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                59#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        4
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_divuw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (2#2 ++
            (LeanRV64D.Functions.bool_bits_forwards true ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                59#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_rem_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (3#2 ++
            (LeanRV64D.Functions.bool_bits_forwards false ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                51#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        6
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_remu_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (3#2 ++
            (LeanRV64D.Functions.bool_bits_forwards true ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                51#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        7
        (regidx_to_fin rd).val
        0x33 := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_remw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (3#2 ++
            (LeanRV64D.Functions.bool_bits_forwards false ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                59#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        6
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_remuw_concat_eq_rawRType (rs2 rs1 rd : regidx) :
    ((0b0000001#7 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (3#2 ++
            (LeanRV64D.Functions.bool_bits_forwards true ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                59#7))))) : RawInstruction)) =
      Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        7
        (regidx_to_fin rd).val
        0x3b := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_itype_imm_component_eq (imm : BitVec 12) :
    BitVec.ofNat 32 ((imm.toNat % 4096) <<< 20) =
      (imm ++ 0#20 : BitVec 32) := by
  native_decide +revert

theorem sail_itype_rs1_component_eq (rs : BitVec 5) :
    BitVec.ofNat 32 (rs.toNat <<< 15) =
      (0#12 ++ (rs ++ 0#15) : BitVec 32) := by
  native_decide +revert

theorem sail_itype_funct3_component_eq (funct3 : BitVec 3) :
    BitVec.ofNat 32 (funct3.toNat <<< 12) =
      (0#17 ++ (funct3 ++ 0#12) : BitVec 32) := by
  native_decide +revert

theorem sail_itype_rd_component_eq (rd : BitVec 5) :
    BitVec.ofNat 32 (rd.toNat <<< 7) =
      (0#20 ++ (rd ++ 0#7) : BitVec 32) := by
  native_decide +revert

theorem sail_itype_opcode_component_eq (opcode : BitVec 7) :
    BitVec.ofNat 32 opcode.toNat =
      (0#25 ++ opcode : BitVec 32) := by
  native_decide +revert

theorem sail_itype_bitvec_concat_eq_rawIType
    (imm : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opcode : BitVec 7) :
    (((imm ++ (rs1 ++ (funct3 ++ (rd ++ opcode)))) : RawInstruction)) =
      Rv64imShapes.rawIType imm.toNat rs1.toNat funct3.toNat rd.toNat opcode.toNat := by
  dsimp [Rv64imShapes.rawIType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or]
  rw [sail_itype_imm_component_eq, sail_itype_rs1_component_eq,
    sail_itype_funct3_component_eq, sail_itype_rd_component_eq,
    sail_itype_opcode_component_eq]
  bv_decide

theorem sail_itype_parts_bitvec_concat_eq_rawIType
    (imm : BitVec 12) (rs1 : BitVec 5) (is_unsigned : BitVec 1)
    (width : BitVec 2) (rd : BitVec 5) (opcode : BitVec 7) :
    (((imm ++
      (rs1 ++
        (is_unsigned ++
          (width ++
            (rd ++ opcode))))) : RawInstruction)) =
      Rv64imShapes.rawIType imm.toNat rs1.toNat
        (is_unsigned ++ width).toNat rd.toNat opcode.toNat := by
  dsimp [Rv64imShapes.rawIType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or]
  rw [sail_itype_imm_component_eq, sail_itype_rs1_component_eq,
    sail_itype_funct3_component_eq, sail_itype_rd_component_eq,
    sail_itype_opcode_component_eq]
  bv_decide

theorem sail_itype_concat_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx) (funct3 : BitVec 3) :
    ((imm ++
      (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
        (funct3 ++
          (LeanRV64D.Functions.encdec_reg_forwards rd ++
            0b0010011#7)))) : RawInstruction) =
      Rv64imShapes.rawIType imm.toNat
        (regidx_to_fin rs1).val
        funct3.toNat
        (regidx_to_fin rd).val
        0x13 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    sail_itype_bitvec_concat_eq_rawIType imm rs1 funct3 rd 0b0010011#7

theorem sail_load_concat_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx) (funct3 : BitVec 3) :
    ((imm ++
      (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
        (funct3 ++
          (LeanRV64D.Functions.encdec_reg_forwards rd ++
            0b0000011#7)))) : RawInstruction) =
      Rv64imShapes.rawIType imm.toNat
        (regidx_to_fin rs1).val
        funct3.toNat
        (regidx_to_fin rd).val
        0x03 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    sail_itype_bitvec_concat_eq_rawIType imm rs1 funct3 rd 0b0000011#7

theorem sail_load_parts_concat_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx)
    (is_unsigned : BitVec 1) (width : BitVec 2) :
    ((imm ++
      (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
        (is_unsigned ++
          (width ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0000011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType imm.toNat
        (regidx_to_fin rs1).val
        (is_unsigned ++ width).toNat
        (regidx_to_fin rd).val
        0x03 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    sail_itype_parts_bitvec_concat_eq_rawIType imm rs1 is_unsigned width rd
      0b0000011#7

theorem sail_stype_imm_hi_component_eq (imm : BitVec 12) :
    BitVec.ofNat 32 (((imm.toNat % 4096) >>> 5) <<< 25) =
      (BitVec.extractLsb 11 5 imm ++ 0#25 : BitVec 32) := by
  native_decide +revert

theorem sail_stype_rs2_component_eq (rs : BitVec 5) :
    BitVec.ofNat 32 (rs.toNat <<< 20) =
      (0#7 ++ (rs ++ 0#20) : BitVec 32) := by
  native_decide +revert

theorem sail_stype_rs1_component_eq (rs : BitVec 5) :
    BitVec.ofNat 32 (rs.toNat <<< 15) =
      (0#12 ++ (rs ++ 0#15) : BitVec 32) := by
  native_decide +revert

theorem sail_stype_funct3_component_eq (funct3 : BitVec 3) :
    BitVec.ofNat 32 (funct3.toNat <<< 12) =
      (0#17 ++ (funct3 ++ 0#12) : BitVec 32) := by
  native_decide +revert

theorem sail_stype_imm_lo_component_eq (imm : BitVec 12) :
    BitVec.ofNat 32 (((imm.toNat % 4096) &&& 0x1f) <<< 7) =
      (0#20 ++ (BitVec.extractLsb 4 0 imm ++ 0#7) : BitVec 32) := by
  native_decide +revert

theorem sail_stype_opcode_component_eq :
    BitVec.ofNat 32 0x23 = (0#25 ++ 0b0100011#7 : BitVec 32) := by
  native_decide

theorem sail_store_parts_bitvec_concat_eq_rawSType
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3) :
    (((BitVec.extractLsb 11 5 imm ++
      (rs2 ++
        (rs1 ++
          (funct3 ++
            (BitVec.extractLsb 4 0 imm ++
              0b0100011#7))))) : RawInstruction)) =
      Rv64imShapes.rawSType imm.toNat rs2.toNat rs1.toNat funct3.toNat := by
  dsimp [Rv64imShapes.rawSType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or,
    BitVec.ofNat_or]
  rw [sail_stype_imm_hi_component_eq, sail_stype_rs2_component_eq,
    sail_stype_rs1_component_eq, sail_stype_funct3_component_eq,
    sail_stype_imm_lo_component_eq, sail_stype_opcode_component_eq]
  bv_decide

theorem sail_store_parts_split_bitvec_concat_eq_rawSType
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (width : BitVec 2) :
    (((BitVec.extractLsb 11 5 imm ++
      (rs2 ++
        (rs1 ++
          (0#1 ++
            (width ++
              (BitVec.extractLsb 4 0 imm ++
                0b0100011#7)))))) : RawInstruction)) =
      Rv64imShapes.rawSType imm.toNat rs2.toNat rs1.toNat
        ((0#1 : BitVec 1) ++ width).toNat := by
  dsimp [Rv64imShapes.rawSType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or,
    BitVec.ofNat_or]
  rw [sail_stype_imm_hi_component_eq, sail_stype_rs2_component_eq,
    sail_stype_rs1_component_eq, sail_stype_funct3_component_eq,
    sail_stype_imm_lo_component_eq, sail_stype_opcode_component_eq]
  bv_decide

theorem sail_store_parts_concat_eq_rawSType
    (imm : BitVec 12) (rs2 rs1 : regidx) (width : BitVec 2) :
    ((Sail.BitVec.extractLsb imm 11 5 ++
      (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0#1 ++
            (width ++
              (Sail.BitVec.extractLsb imm 4 0 ++
                0b0100011#7)))))) : RawInstruction) =
      Rv64imShapes.rawSType imm.toNat
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        ((0#1 : BitVec 1) ++ width).toNat := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, Sail.BitVec.extractLsb,
    regidx_to_fin] using
    sail_store_parts_split_bitvec_concat_eq_rawSType imm rs2 rs1 width

theorem sail_utype_imm_component_eq (imm : BitVec 20) :
    BitVec.ofNat 32 ((imm.toNat <<< 12) &&& 0xfffff000) =
      (imm ++ 0#12 : BitVec 32) := by
  native_decide +revert

theorem sail_utype_rd_component_eq (rd : BitVec 5) :
    BitVec.ofNat 32 (rd.toNat <<< 7) =
      (0#20 ++ (rd ++ 0#7) : BitVec 32) := by
  native_decide +revert

theorem sail_utype_opcode_component_eq (opcode : BitVec 7) :
    BitVec.ofNat 32 opcode.toNat =
      (0#25 ++ opcode : BitVec 32) := by
  native_decide +revert

theorem sail_utype_bitvec_concat_eq_rawUType
    (imm : BitVec 20) (rd : BitVec 5) (opcode : BitVec 7) :
    (((imm ++ (rd ++ opcode)) : RawInstruction)) =
      Rv64imShapes.rawUType (imm.toNat <<< 12) rd.toNat opcode.toNat := by
  dsimp [Rv64imShapes.rawUType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or]
  rw [sail_utype_imm_component_eq, sail_utype_rd_component_eq,
    sail_utype_opcode_component_eq]
  bv_decide

theorem sail_utype_concat_eq_rawUType
    (imm : BitVec 20) (rd : regidx) (opcode : BitVec 7) :
    ((imm ++
      (LeanRV64D.Functions.encdec_reg_forwards rd ++ opcode)) : RawInstruction) =
      Rv64imShapes.rawUType (imm.toNat <<< 12)
        (regidx_to_fin rd).val
        opcode.toNat := by
  cases rd with | Regidx rd =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    sail_utype_bitvec_concat_eq_rawUType imm rd opcode

theorem sail_jalr_concat_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx) :
    ((imm ++
      (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
        (0b000#3 ++
          (LeanRV64D.Functions.encdec_reg_forwards rd ++
            0b1100111#7)))) : RawInstruction) =
      Rv64imShapes.rawIType imm.toNat
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x67 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    sail_itype_bitvec_concat_eq_rawIType imm rs1 0b000#3 rd 0b1100111#7

theorem sail_fence_pred_component_eq (pred : BitVec 4) :
    BitVec.ofNat 32 (pred.toNat <<< 24) =
      (0#4 ++ (pred ++ 0#24) : BitVec 32) := by
  native_decide +revert

theorem sail_fence_succ_component_eq (succ : BitVec 4) :
    BitVec.ofNat 32 (succ.toNat <<< 20) =
      (0#8 ++ (succ ++ 0#20) : BitVec 32) := by
  native_decide +revert

theorem sail_fence_opcode_component_eq :
    BitVec.ofNat 32 0x0f = (0#25 ++ 0b0001111#7 : BitVec 32) := by
  native_decide

theorem sail_fence_bitvec_concat_eq_rawSupportedFence
    (pred succ : BitVec 4) :
    (((0#4 ++
      (pred ++
        (succ ++
          (0#5 ++
            (0#3 ++
              (0#5 ++ 0b0001111#7)))))) : RawInstruction)) =
      Rv64imShapes.rawSupportedFence pred.toNat succ.toNat := by
  dsimp [Rv64imShapes.rawSupportedFence, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or]
  rw [sail_fence_pred_component_eq, sail_fence_succ_component_eq,
    sail_fence_opcode_component_eq]
  bv_decide

theorem sail_fence_concat_eq_rawSupportedFence
    (pred succ : BitVec 4) :
    ((0#4 ++
      (pred ++
        (succ ++
          (LeanRV64D.Functions.encdec_reg_forwards (regidx.Regidx 0#5) ++
            (0b000#3 ++
              (LeanRV64D.Functions.encdec_reg_forwards (regidx.Regidx 0#5) ++
                0b0001111#7)))))) : RawInstruction) =
      Rv64imShapes.rawSupportedFence pred.toNat succ.toNat := by
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend] using
    sail_fence_bitvec_concat_eq_rawSupportedFence pred succ

theorem sail_jal_align_toNat_mod_two
    (imm : BitVec 21)
    (h_align : (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true) :
    imm.toNat % 2 = 0 := by
  native_decide +revert

theorem sail_utype_shift_toNat_lt (imm : BitVec 20) :
    imm.toNat <<< 12 < 2 ^ 32 := by
  rw [Nat.shiftLeft_eq]
  have h := Nat.mul_lt_mul_of_pos_right imm.isLt (by native_decide : 0 < 2 ^ 12)
  simpa using h

theorem sail_utype_shift_toNat_mod_4096 (imm : BitVec 20) :
    (imm.toNat <<< 12) % 4096 = 0 := by
  rw [Nat.shiftLeft_eq]
  norm_num [Nat.mul_comm]

theorem sail_jal_rd_component_eq (rd : BitVec 5) :
    BitVec.ofNat 32 (rd.toNat <<< 7) =
      (0#20 ++ (rd ++ 0#7) : BitVec 32) := by
  native_decide +revert

theorem sail_jal_imm20_component_eq (imm : BitVec 21) :
    BitVec.ofNat 32 ((((imm.toNat % 2097152) >>> 20) &&& 1) <<< 31) =
      (BitVec.extractLsb 20 20 imm ++ 0#31 : BitVec 32) := by
  native_decide +revert

theorem sail_jal_imm10_1_component_eq (imm : BitVec 21) :
    BitVec.ofNat 32 ((((imm.toNat % 2097152) >>> 1) &&& 1023) <<< 21) =
      (0#1 ++ (BitVec.extractLsb 10 1 imm ++ 0#21) : BitVec 32) := by
  native_decide +revert

theorem sail_jal_imm11_component_eq (imm : BitVec 21) :
    BitVec.ofNat 32 ((((imm.toNat % 2097152) >>> 11) &&& 1) <<< 20) =
      (0#11 ++ (BitVec.extractLsb 11 11 imm ++ 0#20) : BitVec 32) := by
  native_decide +revert

theorem sail_jal_imm19_12_component_eq (imm : BitVec 21) :
    BitVec.ofNat 32 ((((imm.toNat % 2097152) >>> 12) &&& 255) <<< 12) =
      (0#12 ++ (BitVec.extractLsb 19 12 imm ++ 0#12) : BitVec 32) := by
  native_decide +revert

theorem sail_jal_encImm_concat_eq_direct
    (imm : BitVec 21) (rd : BitVec 5) :
    let encImm := Sail.BitVec.extractLsb imm 20 1
    (((Sail.BitVec.extractLsb encImm 19 19 ++
      (Sail.BitVec.extractLsb encImm 9 0 ++
        (Sail.BitVec.extractLsb encImm 10 10 ++
          (Sail.BitVec.extractLsb encImm 18 11 ++
            (rd ++ 0b1101111#7))))) : RawInstruction)) =
    (((BitVec.extractLsb 20 20 imm ++
      (BitVec.extractLsb 10 1 imm ++
        (BitVec.extractLsb 11 11 imm ++
          (BitVec.extractLsb 19 12 imm ++
            (rd ++ 0b1101111#7))))) : RawInstruction)) := by
  simp only [Sail.BitVec.extractLsb]
  bv_decide

theorem sail_jal_direct_bitvec_concat_eq_rawJType
    (imm : BitVec 21) (rd : BitVec 5) :
    (((BitVec.extractLsb 20 20 imm ++
      (BitVec.extractLsb 10 1 imm ++
        (BitVec.extractLsb 11 11 imm ++
          (BitVec.extractLsb 19 12 imm ++
            (rd ++ 0b1101111#7))))) : RawInstruction)) =
      Rv64imShapes.rawJType imm.toNat rd.toNat := by
  dsimp [Rv64imShapes.rawJType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or,
    BitVec.ofNat_or]
  rw [sail_jal_imm20_component_eq, sail_jal_imm10_1_component_eq,
    sail_jal_imm11_component_eq, sail_jal_imm19_12_component_eq,
    sail_jal_rd_component_eq]
  bv_decide

theorem sail_jal_concat_eq_rawJType
    (imm : BitVec 21) (rd : regidx) :
    let encImm := Sail.BitVec.extractLsb imm 20 1
    (((Sail.BitVec.extractLsb encImm 19 19 ++
      (Sail.BitVec.extractLsb encImm 9 0 ++
        (Sail.BitVec.extractLsb encImm 10 10 ++
          (Sail.BitVec.extractLsb encImm 18 11 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b1101111#7))))) : RawInstruction)) =
      Rv64imShapes.rawJType imm.toNat (regidx_to_fin rd).val := by
  cases rd with | Regidx rd =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    (sail_jal_encImm_concat_eq_direct imm rd).trans
      (sail_jal_direct_bitvec_concat_eq_rawJType imm rd)

theorem sail_slli_concat_eq_rawIType
    (shamt : BitVec 6) (rs1 rd : regidx) :
    ((0b000000#6 ++
      (shamt ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b001#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0010011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType shamt.toNat
        (regidx_to_fin rs1).val
        1
        (regidx_to_fin rd).val
        0x13 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_srli_concat_eq_rawIType
    (shamt : BitVec 6) (rs1 rd : regidx) :
    ((0b000000#6 ++
      (shamt ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0010011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType shamt.toNat
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x13 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_srai_concat_eq_rawIType
    (shamt : BitVec 6) (rs1 rd : regidx) :
    ((0b010000#6 ++
      (shamt ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0010011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType (0x400 ||| shamt.toNat)
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x13 := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_addiw_concat_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx) :
    ((imm ++
      (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
        (0b000#3 ++
          (LeanRV64D.Functions.encdec_reg_forwards rd ++
            0b0011011#7)))) : RawInstruction) =
      Rv64imShapes.rawIType imm.toNat
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x1b := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_slliw_concat_eq_rawIType
    (shamt : BitVec 5) (rs1 rd : regidx) :
    ((0b0000000#7 ++
      (shamt ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b001#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0011011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType shamt.toNat
        (regidx_to_fin rs1).val
        1
        (regidx_to_fin rd).val
        0x1b := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_srliw_concat_eq_rawIType
    (shamt : BitVec 5) (rs1 rd : regidx) :
    ((0b0000000#7 ++
      (shamt ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0011011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType shamt.toNat
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x1b := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_sraiw_concat_eq_rawIType
    (shamt : BitVec 5) (rs1 rd : regidx) :
    ((0b0100000#7 ++
      (shamt ++
        (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
          (0b101#3 ++
            (LeanRV64D.Functions.encdec_reg_forwards rd ++
              0b0011011#7))))) : RawInstruction) =
      Rv64imShapes.rawIType (0x400 ||| shamt.toNat)
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x1b := by
  cases rs1 with | Regidx rs1 =>
  cases rd with | Regidx rd =>
  native_decide +revert

theorem sail_btype_align_toNat_mod_two
    (imm : BitVec 13)
    (h_align : (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true) :
    imm.toNat % 2 = 0 := by
  native_decide +revert

theorem sail_btype_rs2_component_eq (rs : BitVec 5) :
    BitVec.ofNat 32 (rs.toNat <<< 20) =
      (0#7 ++ (rs ++ 0#20) : BitVec 32) := by
  native_decide +revert

theorem sail_btype_rs1_component_eq (rs : BitVec 5) :
    BitVec.ofNat 32 (rs.toNat <<< 15) =
      (0#12 ++ (rs ++ 0#15) : BitVec 32) := by
  native_decide +revert

theorem sail_btype_funct3_component_eq (funct3 : BitVec 3) :
    BitVec.ofNat 32 (funct3.toNat <<< 12) =
      (0#17 ++ (funct3 ++ 0#12) : BitVec 32) := by
  native_decide +revert

theorem sail_btype_imm12_component_eq (imm : BitVec 13) :
    BitVec.ofNat 32 ((((imm.toNat % 8192) >>> 12) &&& 1) <<< 31) =
      (BitVec.extractLsb 12 12 imm ++ 0#31 : BitVec 32) := by
  native_decide +revert

theorem sail_btype_imm10_5_component_eq (imm : BitVec 13) :
    BitVec.ofNat 32 ((((imm.toNat % 8192) >>> 5) &&& 63) <<< 25) =
      (0#1 ++ (BitVec.extractLsb 10 5 imm ++ 0#25) : BitVec 32) := by
  native_decide +revert

theorem sail_btype_imm4_1_component_eq (imm : BitVec 13) :
    BitVec.ofNat 32 ((((imm.toNat % 8192) >>> 1) &&& 15) <<< 8) =
      (0#20 ++ (BitVec.extractLsb 4 1 imm ++ 0#8) : BitVec 32) := by
  native_decide +revert

theorem sail_btype_imm11_component_eq (imm : BitVec 13) :
    BitVec.ofNat 32 ((((imm.toNat % 8192) >>> 11) &&& 1) <<< 7) =
      (0#24 ++ (BitVec.extractLsb 11 11 imm ++ 0#7) : BitVec 32) := by
  native_decide +revert

theorem sail_btype_encImm_concat_eq_direct
    (imm : BitVec 13) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3) :
    let encImm := Sail.BitVec.extractLsb imm 12 1
    ((Sail.BitVec.extractLsb encImm 11 11 ++
      (Sail.BitVec.extractLsb encImm 9 4 ++
        (rs2 ++
          (rs1 ++
            (funct3 ++
              (Sail.BitVec.extractLsb encImm 3 0 ++
                (Sail.BitVec.extractLsb encImm 10 10 ++
                  0b1100011#7))))))) : RawInstruction) =
    ((BitVec.extractLsb 12 12 imm ++
      (BitVec.extractLsb 10 5 imm ++
        (rs2 ++
          (rs1 ++
            (funct3 ++
              (BitVec.extractLsb 4 1 imm ++
                (BitVec.extractLsb 11 11 imm ++
                  0b1100011#7))))))) : RawInstruction) := by
  simp only [Sail.BitVec.extractLsb]
  bv_decide

theorem sail_btype_direct_bitvec_concat_eq_rawBType
    (imm : BitVec 13) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3) :
    ((BitVec.extractLsb 12 12 imm ++
      (BitVec.extractLsb 10 5 imm ++
        (rs2 ++
          (rs1 ++
            (funct3 ++
              (BitVec.extractLsb 4 1 imm ++
                (BitVec.extractLsb 11 11 imm ++
                  0b1100011#7))))))) : RawInstruction) =
      Rv64imShapes.rawBType imm.toNat rs2.toNat rs1.toNat funct3.toNat := by
  dsimp [Rv64imShapes.rawBType, Rv64imShapes.rawOfNat32]
  rw [BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or,
    BitVec.ofNat_or, BitVec.ofNat_or, BitVec.ofNat_or]
  rw [sail_btype_imm12_component_eq, sail_btype_imm10_5_component_eq,
    sail_btype_rs2_component_eq, sail_btype_rs1_component_eq,
    sail_btype_funct3_component_eq, sail_btype_imm4_1_component_eq,
    sail_btype_imm11_component_eq]
  bv_decide

theorem sail_btype_direct_concat_eq_rawBType
    (imm : BitVec 13) (rs2 rs1 : regidx) (funct3 : BitVec 3) :
    ((BitVec.extractLsb 12 12 imm ++
      (BitVec.extractLsb 10 5 imm ++
        (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
            (funct3 ++
              (BitVec.extractLsb 4 1 imm ++
                (BitVec.extractLsb 11 11 imm ++
                  0b1100011#7))))))) : RawInstruction) =
      Rv64imShapes.rawBType imm.toNat
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        funct3.toNat := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  simpa [LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin] using
    sail_btype_direct_bitvec_concat_eq_rawBType imm rs2 rs1 funct3

theorem sail_btype_concat_eq_rawBType
    (imm : BitVec 13) (rs2 rs1 : regidx) (funct3 : BitVec 3) :
    let encImm := Sail.BitVec.extractLsb imm 12 1
    ((Sail.BitVec.extractLsb encImm 11 11 ++
      (Sail.BitVec.extractLsb encImm 9 4 ++
        (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
            (funct3 ++
              (Sail.BitVec.extractLsb encImm 3 0 ++
                (Sail.BitVec.extractLsb encImm 10 10 ++
                  0b1100011#7))))))) : RawInstruction) =
      Rv64imShapes.rawBType imm.toNat
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        funct3.toNat := by
  calc
    (let encImm := Sail.BitVec.extractLsb imm 12 1;
      ((Sail.BitVec.extractLsb encImm 11 11 ++
        (Sail.BitVec.extractLsb encImm 9 4 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (funct3 ++
                (Sail.BitVec.extractLsb encImm 3 0 ++
                  (Sail.BitVec.extractLsb encImm 10 10 ++
                    0b1100011#7))))))) : RawInstruction)) =
        ((BitVec.extractLsb 12 12 imm ++
          (BitVec.extractLsb 10 5 imm ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (funct3 ++
                  (BitVec.extractLsb 4 1 imm ++
                    (BitVec.extractLsb 11 11 imm ++
                      0b1100011#7))))))) : RawInstruction) := by
          exact sail_btype_encImm_concat_eq_direct imm
            (LeanRV64D.Functions.encdec_reg_forwards rs2)
            (LeanRV64D.Functions.encdec_reg_forwards rs1)
            funct3
    _ = Rv64imShapes.rawBType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          funct3.toNat :=
        sail_btype_direct_concat_eq_rawBType imm rs2 rs1 funct3

end ZiskFv.Completeness.SailDecode
