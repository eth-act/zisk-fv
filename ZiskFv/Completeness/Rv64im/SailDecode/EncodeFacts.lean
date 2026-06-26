import ZiskFv.Completeness.Rv64im.SailDecode.Domain
import ZiskFv.Completeness.Rv64im.SailDecode.ConcatShapes

/-!
# Sail-derived RV64IM decode domain — generated encoder facts

This part holds the `sail_encode_*_eq_raw*` theorems: each unfolds Sail's
generated `encdec_forwards` for a constructor and rewrites it to the matching
`Rv64imShapes.raw*` shape via the concat bridges.  It is part of the split
`ZiskFv.Completeness.Rv64im.SailDecode` module.
-/

namespace ZiskFv.Completeness.SailDecode

open ZiskFv.Completeness

/-- Generated Sail encoder fact for the ADD pilot. -/
theorem sail_encode_add_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b000#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33)
  rw [sail_add_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_sub_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0100000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b000#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33)
  rw [sail_sub_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_sll_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.SLL)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b001#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x33)
  rw [sail_sll_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_slt_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.SLT)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          2
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b010#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          2
          (regidx_to_fin rd).val
          0x33)
  rw [sail_slt_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_sltu_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          3
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b011#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          3
          (regidx_to_fin rd).val
          0x33)
  rw [sail_sltu_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_xor_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.XOR)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          4
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b100#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          4
          (regidx_to_fin rd).val
          0x33)
  rw [sail_xor_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_srl_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.SRL)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x33)
  rw [sail_srl_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_sra_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.SRA)) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0100000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x33)
  rw [sail_sra_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_or_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.OR)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          6
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b110#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          6
          (regidx_to_fin rd).val
          0x33)
  rw [sail_or_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_and_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPE (rs2, rs1, rd, rop.AND)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          7
          (regidx_to_fin rd).val
          0x33) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b111#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0110011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          7
          (regidx_to_fin rd).val
          0x33)
  rw [sail_and_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_addw_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPEW (rs2, rs1, rd, ropw.ADDW)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x3b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b000#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0111011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x3b)
  rw [sail_addw_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_subw_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPEW (rs2, rs1, rd, ropw.SUBW)) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x3b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0100000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b000#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0111011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x3b)
  rw [sail_subw_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_sllw_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x3b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b001#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0111011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x3b)
  rw [sail_sllw_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_srlw_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPEW (rs2, rs1, rd, ropw.SRLW)) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x3b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0111011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x3b)
  rw [sail_srlw_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_sraw_eq_rawRType (rs2 rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.RTYPEW (rs2, rs1, rd, ropw.SRAW)) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x3b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0100000#7 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0111011#7)))) : RawInstruction))) =
      pure
        (Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x3b)
  rw [sail_sraw_concat_eq_rawRType rs2 rs1 rd]

theorem sail_encode_mul_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.MUL (rs2, rs1, rd,
          { result_part := VectorHalf.Low,
            signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Signed }))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      (LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul >>= fun __do_lift_1 =>
      if (__do_lift || __do_lift_1) = true then
        (LeanRV64D.Functions.encdec_mul_op_forwards
          { result_part := VectorHalf.Low,
            signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Signed } >>= fun __do_lift =>
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (__do_lift ++
                  (LeanRV64D.Functions.encdec_reg_forwards rd ++
                    0b0110011#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit)) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  apply sailM_bind_ok h_zmmul
  simp [LeanRV64D.Functions.encdec_mul_op_forwards]
  simpa using sail_mul_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_mulh_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.MUL (rs2, rs1, rd,
          { result_part := VectorHalf.High,
            signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Signed }))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      (LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul >>= fun __do_lift_1 =>
      if (__do_lift || __do_lift_1) = true then
        (LeanRV64D.Functions.encdec_mul_op_forwards
          { result_part := VectorHalf.High,
            signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Signed } >>= fun __do_lift =>
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (__do_lift ++
                  (LeanRV64D.Functions.encdec_reg_forwards rd ++
                    0b0110011#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit)) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        1
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  apply sailM_bind_ok h_zmmul
  simp [LeanRV64D.Functions.encdec_mul_op_forwards]
  simpa using sail_mulh_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_mulhsu_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.MUL (rs2, rs1, rd,
          { result_part := VectorHalf.High,
            signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Unsigned }))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          2
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      (LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul >>= fun __do_lift_1 =>
      if (__do_lift || __do_lift_1) = true then
        (LeanRV64D.Functions.encdec_mul_op_forwards
          { result_part := VectorHalf.High,
            signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Unsigned } >>= fun __do_lift =>
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (__do_lift ++
                  (LeanRV64D.Functions.encdec_reg_forwards rd ++
                    0b0110011#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit)) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        2
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  apply sailM_bind_ok h_zmmul
  simp [LeanRV64D.Functions.encdec_mul_op_forwards]
  simpa using sail_mulhsu_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_mulhu_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.MUL (rs2, rs1, rd,
          { result_part := VectorHalf.High,
            signed_rs1 := Signedness.Unsigned,
            signed_rs2 := Signedness.Unsigned }))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          3
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      (LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul >>= fun __do_lift_1 =>
      if (__do_lift || __do_lift_1) = true then
        (LeanRV64D.Functions.encdec_mul_op_forwards
          { result_part := VectorHalf.High,
            signed_rs1 := Signedness.Unsigned,
            signed_rs2 := Signedness.Unsigned } >>= fun __do_lift =>
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (__do_lift ++
                  (LeanRV64D.Functions.encdec_reg_forwards rd ++
                    0b0110011#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit)) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        3
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  apply sailM_bind_ok h_zmmul
  simp [LeanRV64D.Functions.encdec_mul_op_forwards]
  simpa using sail_mulhu_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_mulw_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.MULW (rs2, rs1, rd))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x3b) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      (LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul >>= fun __do_lift_1 =>
      if (LeanRV64D.Functions.xlen == 64 && (__do_lift || __do_lift_1)) = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (0b000#3 ++
                  (LeanRV64D.Functions.encdec_reg_forwards rd ++
                    0b0111011#7)))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit)) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        0
        (regidx_to_fin rd).val
        0x3b) state
  apply sailM_bind_ok h_m
  apply sailM_bind_ok h_zmmul
  simp
  simpa using sail_mulw_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_div_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.DIV (rs2, rs1, rd, false))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          4
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if __do_lift = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (2#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards false ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      51#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        4
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_div_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_divu_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.DIV (rs2, rs1, rd, true))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if __do_lift = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (2#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards true ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      51#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_divu_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_divw_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.DIVW (rs2, rs1, rd, false))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          4
          (regidx_to_fin rd).val
          0x3b) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if (LeanRV64D.Functions.xlen == 64 && __do_lift) = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (2#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards false ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      59#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        4
        (regidx_to_fin rd).val
        0x3b) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_divw_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_divuw_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.DIVW (rs2, rs1, rd, true))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x3b) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if (LeanRV64D.Functions.xlen == 64 && __do_lift) = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (2#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards true ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      59#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        5
        (regidx_to_fin rd).val
        0x3b) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_divuw_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_rem_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.REM (rs2, rs1, rd, false))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          6
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if __do_lift = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (3#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards false ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      51#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        6
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_rem_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_remu_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.REM (rs2, rs1, rd, true))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          7
          (regidx_to_fin rd).val
          0x33) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if __do_lift = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (3#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards true ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      51#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        7
        (regidx_to_fin rd).val
        0x33) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_remu_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_remw_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.REMW (rs2, rs1, rd, false))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          6
          (regidx_to_fin rd).val
          0x3b) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if (LeanRV64D.Functions.xlen == 64 && __do_lift) = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (3#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards false ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      59#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        6
        (regidx_to_fin rd).val
        0x3b) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_remw_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_remuw_eq_rawRType_in
    (state : SailState) (h_state : IsaExtensionsEnabled state)
    (rs2 rs1 rd : regidx) :
    SailEncodesToIn state
        (instruction.REMW (rs2, rs1, rd, true))
        (Rv64imShapes.rawRType 1
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          7
          (regidx_to_fin rd).val
          0x3b) := by
  dsimp [SailEncodesToIn, SailReturns, IsaExtensionsEnabled] at *
  rcases h_state with ⟨h_m, _h_zmmul⟩
  unfold LeanRV64D.Functions.encdec_forwards
  change
    ((LeanRV64D.Functions.currentlyEnabled extension.Ext_M) >>= fun __do_lift =>
      if (LeanRV64D.Functions.xlen == 64 && __do_lift) = true then
        pure
          (0b0000001#7 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
              (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
                (3#2 ++
                  (LeanRV64D.Functions.bool_bits_forwards true ++
                    (LeanRV64D.Functions.encdec_reg_forwards rd ++
                      59#7))))))
      else do
        Sail.assert false "Pattern match failure at unknown location"
        throw Sail.Error.Exit) state =
    EStateM.Result.ok
      (Rv64imShapes.rawRType 1
        (regidx_to_fin rs2).val
        (regidx_to_fin rs1).val
        7
        (regidx_to_fin rd).val
        0x3b) state
  apply sailM_bind_ok h_m
  simp
  simpa using sail_remuw_concat_eq_rawRType rs2 rs1 rd

theorem sail_encode_itype_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.ITYPE (imm, rs1, rd, op)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          (LeanRV64D.Functions.encdec_iop_forwards op).toNat
          (regidx_to_fin rd).val
          0x13) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((imm ++
          (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
            (LeanRV64D.Functions.encdec_iop_forwards op ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                0b0010011#7)))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          (LeanRV64D.Functions.encdec_iop_forwards op).toNat
          (regidx_to_fin rd).val
          0x13)
  rw [sail_itype_concat_eq_rawIType imm rs1 rd
    (LeanRV64D.Functions.encdec_iop_forwards op)]

theorem sail_encode_load_eq_rawIType
    (imm : BitVec 12) (rs1 rd : regidx)
    (is_unsigned : Bool) (width : Int)
    (h_valid :
      LeanRV64D.Functions.valid_load_encdec (Int.toNat width) is_unsigned =
        true) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, is_unsigned, width)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          (LeanRV64D.Functions.bool_bits_forwards is_unsigned ++
            LeanRV64D.Functions.width_enc_forwards (Int.toNat width)).toNat
          (regidx_to_fin rd).val
          0x03) := by
  rw [LeanRV64D.Functions.encdec_forwards.eq_def]
  change
    (if LeanRV64D.Functions.valid_load_encdec (Int.toNat width) is_unsigned = true then
      (show SailM RawInstruction from
        pure
          ((imm ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (LeanRV64D.Functions.bool_bits_forwards is_unsigned ++
                (LeanRV64D.Functions.width_enc_forwards (Int.toNat width) ++
                  (LeanRV64D.Functions.encdec_reg_forwards rd ++
                    0b0000011#7))))) : RawInstruction))
    else do
      Sail.assert false "Pattern match failure at unknown location"
      throw Sail.Error.Exit) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          (LeanRV64D.Functions.bool_bits_forwards is_unsigned ++
            LeanRV64D.Functions.width_enc_forwards (Int.toNat width)).toNat
          (regidx_to_fin rd).val
          0x03)
  rw [h_valid]
  simp only [if_true]
  rw [sail_load_parts_concat_eq_rawIType imm rs1 rd
    (LeanRV64D.Functions.bool_bits_forwards is_unsigned)
    (LeanRV64D.Functions.width_enc_forwards (Int.toNat width))]

theorem sail_encode_lb_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, false, (1 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd false (1 : Int)
    (by native_decide)

theorem sail_encode_lh_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, false, (2 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd false (2 : Int)
    (by native_decide)

theorem sail_encode_lw_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, false, (4 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          2
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd false (4 : Int)
    (by native_decide)

theorem sail_encode_ld_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, false, (8 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          3
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd false (8 : Int)
    (by native_decide)

theorem sail_encode_lbu_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, true, (1 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          4
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd true (1 : Int)
    (by native_decide)

theorem sail_encode_lhu_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, true, (2 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd true (2 : Int)
    (by native_decide)

theorem sail_encode_lwu_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.LOAD (imm, rs1, rd, true, (4 : Int))) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          6
          (regidx_to_fin rd).val
          0x03) := by
  simpa [
    LeanRV64D.Functions.bool_bits_forwards,
    LeanRV64D.Functions.width_enc_forwards
  ] using sail_encode_load_eq_rawIType imm rs1 rd true (4 : Int)
    (by native_decide)

theorem sail_encode_store_eq_rawSType
    (imm : BitVec 12) (rs2 rs1 : regidx) (width : Int) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.STORE (imm, rs2, rs1, width)) =
      pure
        (Rv64imShapes.rawSType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          ((0#1 : BitVec 1) ++
            LeanRV64D.Functions.width_enc_forwards (Int.toNat width)).toNat) := by
  rw [LeanRV64D.Functions.encdec_forwards.eq_def]
  change
    pure
        (((Sail.BitVec.extractLsb imm 11 5 ++
          (LeanRV64D.Functions.encdec_reg_forwards rs2 ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0#1 ++
                (LeanRV64D.Functions.width_enc_forwards (Int.toNat width) ++
                  (Sail.BitVec.extractLsb imm 4 0 ++
                    0b0100011#7)))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawSType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          ((0#1 : BitVec 1) ++
            LeanRV64D.Functions.width_enc_forwards (Int.toNat width)).toNat)
  rw [sail_store_parts_concat_eq_rawSType imm rs2 rs1
    (LeanRV64D.Functions.width_enc_forwards (Int.toNat width))]

theorem sail_encode_sb_eq_rawSType (imm : BitVec 12) (rs2 rs1 : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.STORE (imm, rs2, rs1, (1 : Int))) =
      pure
        (Rv64imShapes.rawSType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0) := by
  simpa [LeanRV64D.Functions.width_enc_forwards] using
    sail_encode_store_eq_rawSType imm rs2 rs1 (1 : Int)

theorem sail_encode_sh_eq_rawSType (imm : BitVec 12) (rs2 rs1 : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.STORE (imm, rs2, rs1, (2 : Int))) =
      pure
        (Rv64imShapes.rawSType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          1) := by
  simpa [LeanRV64D.Functions.width_enc_forwards] using
    sail_encode_store_eq_rawSType imm rs2 rs1 (2 : Int)

theorem sail_encode_sw_eq_rawSType (imm : BitVec 12) (rs2 rs1 : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.STORE (imm, rs2, rs1, (4 : Int))) =
      pure
        (Rv64imShapes.rawSType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          2) := by
  simpa [LeanRV64D.Functions.width_enc_forwards] using
    sail_encode_store_eq_rawSType imm rs2 rs1 (4 : Int)

theorem sail_encode_sd_eq_rawSType (imm : BitVec 12) (rs2 rs1 : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.STORE (imm, rs2, rs1, (8 : Int))) =
      pure
        (Rv64imShapes.rawSType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          3) := by
  simpa [LeanRV64D.Functions.width_enc_forwards] using
    sail_encode_store_eq_rawSType imm rs2 rs1 (8 : Int)

theorem sail_encode_utype_eq_rawUType
    (imm : BitVec 20) (rd : regidx) (op : uop) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.UTYPE (imm, rd, op)) =
      pure
        (Rv64imShapes.rawUType (imm.toNat <<< 12)
          (regidx_to_fin rd).val
          (LeanRV64D.Functions.encdec_uop_forwards op).toNat) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((imm ++
          (LeanRV64D.Functions.encdec_reg_forwards rd ++
            LeanRV64D.Functions.encdec_uop_forwards op)) : RawInstruction)) =
      pure
        (Rv64imShapes.rawUType (imm.toNat <<< 12)
          (regidx_to_fin rd).val
          (LeanRV64D.Functions.encdec_uop_forwards op).toNat)
  rw [sail_utype_concat_eq_rawUType imm rd
    (LeanRV64D.Functions.encdec_uop_forwards op)]

theorem sail_encode_jalr_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.JALR (imm, rs1, rd)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x67) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((imm ++
          (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
            (0b000#3 ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                0b1100111#7)))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x67)
  rw [sail_jalr_concat_eq_rawIType imm rs1 rd]

theorem sail_encode_supported_fence_eq_rawSupportedFence
    (pred succ : BitVec 4) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.FENCE
          (0#4, pred, succ, regidx.Regidx 0#5, regidx.Regidx 0#5)) =
      pure
        (Rv64imShapes.rawSupportedFence pred.toNat succ.toNat) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0#4 ++
          (pred ++
            (succ ++
              (LeanRV64D.Functions.encdec_reg_forwards (regidx.Regidx 0#5) ++
                (0b000#3 ++
                  (LeanRV64D.Functions.encdec_reg_forwards (regidx.Regidx 0#5) ++
                    0b0001111#7)))))) : RawInstruction)) =
      pure (Rv64imShapes.rawSupportedFence pred.toNat succ.toNat)
  rw [sail_fence_concat_eq_rawSupportedFence pred succ]

theorem sail_encode_jal_eq_rawJType
    (imm : BitVec 21) (rd : regidx)
    (h_align : (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.JAL (imm, rd)) =
      pure
        (Rv64imShapes.rawJType imm.toNat
          (regidx_to_fin rd).val) := by
  cases rd with | Regidx rd =>
  have h_align' : BitVec.extractLsb 0 0 imm = 0#1 := by
    simpa [Sail.BitVec.extractLsb] using h_align
  unfold LeanRV64D.Functions.encdec_forwards
  simp [h_align', Sail.BitVec.extractLsb, LeanRV64D.Functions.encdec_reg_forwards,
    zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin]
  rw [show
      (((BitVec.extractLsb 19 19 (BitVec.extractLsb 20 1 imm) ++
        (BitVec.extractLsb 9 0 (BitVec.extractLsb 20 1 imm) ++
          (BitVec.extractLsb 10 10 (BitVec.extractLsb 20 1 imm) ++
            (BitVec.extractLsb 18 11 (BitVec.extractLsb 20 1 imm) ++
              (rd ++ 0b1101111#7))))) : RawInstruction)) =
        Rv64imShapes.rawJType imm.toNat rd.toNat
    from by
      exact (sail_jal_encImm_concat_eq_direct imm rd).trans
        (sail_jal_direct_bitvec_concat_eq_rawJType imm rd)]

theorem sail_encode_slli_eq_rawIType (shamt : BitVec 6) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.SHIFTIOP (shamt, rs1, rd, sop.SLLI)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x13) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b000000#6 ++
          (shamt ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b001#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0010011#7))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x13)
  rw [sail_slli_concat_eq_rawIType shamt rs1 rd]

theorem sail_encode_srli_eq_rawIType (shamt : BitVec 6) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.SHIFTIOP (shamt, rs1, rd, sop.SRLI)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x13) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b000000#6 ++
          (shamt ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0010011#7))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x13)
  rw [sail_srli_concat_eq_rawIType shamt rs1 rd]

theorem sail_encode_srai_eq_rawIType (shamt : BitVec 6) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.SHIFTIOP (shamt, rs1, rd, sop.SRAI)) =
      pure
        (Rv64imShapes.rawIType (0x400 ||| shamt.toNat)
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x13) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b010000#6 ++
          (shamt ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0010011#7))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType (0x400 ||| shamt.toNat)
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x13)
  rw [sail_srai_concat_eq_rawIType shamt rs1 rd]

theorem sail_encode_addiw_eq_rawIType (imm : BitVec 12) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.ADDIW (imm, rs1, rd)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x1b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((imm ++
          (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
            (0b000#3 ++
              (LeanRV64D.Functions.encdec_reg_forwards rd ++
                0b0011011#7)))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType imm.toNat
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x1b)
  rw [sail_addiw_concat_eq_rawIType imm rs1 rd]

theorem sail_encode_slliw_eq_rawIType (shamt : BitVec 5) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SLLIW)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x1b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (shamt ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b001#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0011011#7))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          1
          (regidx_to_fin rd).val
          0x1b)
  rw [sail_slliw_concat_eq_rawIType shamt rs1 rd]

theorem sail_encode_srliw_eq_rawIType (shamt : BitVec 5) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRLIW)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x1b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0000000#7 ++
          (shamt ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0011011#7))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType shamt.toNat
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x1b)
  rw [sail_srliw_concat_eq_rawIType shamt rs1 rd]

theorem sail_encode_sraiw_eq_rawIType (shamt : BitVec 5) (rs1 rd : regidx) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRAIW)) =
      pure
        (Rv64imShapes.rawIType (0x400 ||| shamt.toNat)
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x1b) := by
  unfold LeanRV64D.Functions.encdec_forwards
  change
    pure
        (((0b0100000#7 ++
          (shamt ++
            (LeanRV64D.Functions.encdec_reg_forwards rs1 ++
              (0b101#3 ++
                (LeanRV64D.Functions.encdec_reg_forwards rd ++
                  0b0011011#7))))) : RawInstruction)) =
      pure
        (Rv64imShapes.rawIType (0x400 ||| shamt.toNat)
          (regidx_to_fin rs1).val
          5
          (regidx_to_fin rd).val
          0x1b)
  rw [sail_sraiw_concat_eq_rawIType shamt rs1 rd]

theorem sail_encode_btype_eq_rawBType
    (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (h_align : (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true) :
    LeanRV64D.Functions.encdec_forwards
        (instruction.BTYPE (imm, rs2, rs1, op)) =
      pure
        (Rv64imShapes.rawBType imm.toNat
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          (LeanRV64D.Functions.encdec_bop_forwards op).toNat) := by
  cases rs2 with | Regidx rs2 =>
  cases rs1 with | Regidx rs1 =>
  have h_align' : BitVec.extractLsb 0 0 imm = 0#1 := by
    simpa [Sail.BitVec.extractLsb] using h_align
  unfold LeanRV64D.Functions.encdec_forwards
  simp [h_align', Sail.BitVec.extractLsb,
    LeanRV64D.Functions.encdec_reg_forwards, zero_extend,
    Sail.BitVec.zeroExtend, BitVec.zeroExtend, regidx_to_fin]
  have h_enc :=
    sail_btype_encImm_concat_eq_direct imm rs2 rs1
      (LeanRV64D.Functions.encdec_bop_forwards op)
  simp only [Sail.BitVec.extractLsb] at h_enc
  rw [h_enc]
  rw [sail_btype_direct_bitvec_concat_eq_rawBType]

end ZiskFv.Completeness.SailDecode
