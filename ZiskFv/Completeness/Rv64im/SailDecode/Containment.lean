import ZiskFv.Completeness.Rv64im.SailDecode.Domain
import ZiskFv.Completeness.Rv64im.SailDecode.ConcatShapes
import ZiskFv.Completeness.Rv64im.SailDecode.EncodeFacts

/-!
# Sail-derived RV64IM decode domain — raw-shape containment

This part holds the containment bridges: per-constructor
`sail_decode_*_contained_*` / `sail_encode_raw*_contained_*` lemmas, the
per-family `sail_*_executable_contained_in*` theorems, the `AddCompleteness`
pilot, and the top-level
`sail_rv64im_executable_contained_in_supported_decode*` theorems.  It is the
terminal part of the split `ZiskFv.Completeness.Rv64im.SailDecode` module.
-/

namespace ZiskFv.Completeness.SailDecode

open ZiskFv.Completeness

/-- Constructor-level bridge for the ADD pilot.  The premises are generated Sail
decode and generated Sail encode facts, not a hand-written raw decoder. -/
theorem sail_decode_add_contained_in_add_shape
    {raw : RawInstruction} {rs2 rs1 rd : regidx}
    (_h_decode :
      SailDecodesTo raw (instruction.RTYPE (rs2, rs1, rd, rop.ADD)))
    (h_encode :
      SailEncodesTo (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) raw) :
    Rv64imShapes.AddRawShape raw := by
  have h_raw :
      raw =
        Rv64imShapes.rawRType 0
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33 := by
    dsimp [SailEncodesTo] at h_encode
    rw [sail_encode_add_eq_rawRType rs2 rs1 rd] at h_encode
    exact sailM_pure_injective h_encode.symm
  subst raw
  refine
    ⟨(regidx_to_fin rd).val,
      (regidx_to_fin rs1).val,
      (regidx_to_fin rs2).val,
      ?_, ?_, ?_, rfl⟩
  · exact List.mem_range.mpr (regidx_to_fin rd).isLt
  · exact List.mem_range.mpr (regidx_to_fin rs1).isLt
  · exact List.mem_range.mpr (regidx_to_fin rs2).isLt

/-- Broad R-type containment for the ADD pilot, derived from the exact ADD
shape. -/
theorem sail_decode_add_contained_in_rtype_shape
    {raw : RawInstruction} {rs2 rs1 rd : regidx}
    (h_decode :
      SailDecodesTo raw (instruction.RTYPE (rs2, rs1, rd, rop.ADD)))
    (h_encode :
      SailEncodesTo (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) raw) :
    Rv64imShapes.RTypeRegisterShape raw :=
  Rv64imShapes.add_raw_shape_subset_r_type_register_shape
    (sail_decode_add_contained_in_add_shape h_decode h_encode)

theorem sail_decode_sub_contained_in_rtype_shape
    {raw : RawInstruction} {rs2 rs1 rd : regidx}
    (_h_decode :
      SailDecodesTo raw (instruction.RTYPE (rs2, rs1, rd, rop.SUB)))
    (h_encode :
      SailEncodesTo (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) raw) :
    Rv64imShapes.RTypeRegisterShape raw := by
  have h_raw :
      raw =
        Rv64imShapes.rawRType 32
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          0
          (regidx_to_fin rd).val
          0x33 := by
    dsimp [SailEncodesTo] at h_encode
    rw [sail_encode_sub_eq_rawRType rs2 rs1 rd] at h_encode
    exact sailM_pure_injective h_encode.symm
  subst raw
  refine
    ⟨32, 0, 0x33,
      (regidx_to_fin rd).val,
      (regidx_to_fin rs1).val,
      (regidx_to_fin rs2).val,
      ?_, ?_, ?_, ?_, rfl⟩
  · simp [Rv64imShapes.allRTypeOpcodeShapes]
  · exact List.mem_range.mpr (regidx_to_fin rd).isLt
  · exact List.mem_range.mpr (regidx_to_fin rs1).isLt
  · exact List.mem_range.mpr (regidx_to_fin rs2).isLt

theorem rawRType_mem_contained_in_rtype_shape
    {funct7 funct3 opcode rd rs1 rs2 : Nat}
    (h_mem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes)
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_rs2 : rs2 ∈ Rv64imShapes.allRvRegs) :
    Rv64imShapes.RTypeRegisterShape
      (Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode) :=
  ⟨funct7, funct3, opcode, rd, rs1, rs2,
    h_mem, h_rd, h_rs1, h_rs2, rfl⟩

theorem sail_decode_rtype_contained_in_rtype_shape
    {raw : RawInstruction} {rs2 rs1 rd : regidx}
    (h_encode :
      SailEncodesTo (instruction.RTYPE (rs2, rs1, rd, op)) raw)
    (h_encode_op :
      LeanRV64D.Functions.encdec_forwards
          (instruction.RTYPE (rs2, rs1, rd, op)) =
        pure
          (Rv64imShapes.rawRType funct7
            (regidx_to_fin rs2).val
            (regidx_to_fin rs1).val
            funct3
            (regidx_to_fin rd).val
            opcode))
    (h_mem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes) :
    Rv64imShapes.RTypeRegisterShape raw := by
  have h_raw :
      raw =
        Rv64imShapes.rawRType funct7
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          funct3
          (regidx_to_fin rd).val
          opcode := by
    dsimp [SailEncodesTo] at h_encode
    rw [h_encode_op] at h_encode
    exact sailM_pure_injective h_encode.symm
  subst raw
  exact
    rawRType_mem_contained_in_rtype_shape
      h_mem
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)

theorem sail_decode_rtypew_contained_in_rtype_shape
    {raw : RawInstruction} {rs2 rs1 rd : regidx}
    (h_encode :
      SailEncodesTo (instruction.RTYPEW (rs2, rs1, rd, op)) raw)
    (h_encode_op :
      LeanRV64D.Functions.encdec_forwards
          (instruction.RTYPEW (rs2, rs1, rd, op)) =
        pure
          (Rv64imShapes.rawRType funct7
            (regidx_to_fin rs2).val
            (regidx_to_fin rs1).val
            funct3
            (regidx_to_fin rd).val
            opcode))
    (h_mem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes) :
    Rv64imShapes.RTypeRegisterShape raw := by
  have h_raw :
      raw =
        Rv64imShapes.rawRType funct7
          (regidx_to_fin rs2).val
          (regidx_to_fin rs1).val
          funct3
          (regidx_to_fin rd).val
          opcode := by
    dsimp [SailEncodesTo] at h_encode
    rw [h_encode_op] at h_encode
    exact sailM_pure_injective h_encode.symm
  subst raw
  exact
    rawRType_mem_contained_in_rtype_shape
      h_mem
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)

theorem sail_encode_rawRType_contained_in_rtype_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {funct7 funct3 opcode rd rs1 rs2 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode))
    (h_mem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes)
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_rs2 : rs2 ∈ Rv64imShapes.allRvRegs) :
    Rv64imShapes.RTypeRegisterShape raw := by
  have h_raw : raw = Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact rawRType_mem_contained_in_rtype_shape h_mem h_rd h_rs1 h_rs2

theorem sail_encode_rawIType_contained_in_immediate_alu_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm funct3 opcode rd rs1 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawIType imm rs1 funct3 rd opcode))
    (h_mem : (funct3, opcode) ∈ [
      (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b)
    ])
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_imm : imm < 4096) :
    Rv64imShapes.ImmediateAluRegisterShape raw := by
  have h_raw : raw = Rv64imShapes.rawIType imm rs1 funct3 rd opcode := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, h_mem, rfl⟩

theorem sail_encode_rawIType_contained_in_load_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm funct3 rd rs1 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawIType imm rs1 funct3 rd 0x03))
    (h_mem : funct3 ∈ [0, 1, 2, 3, 4, 5, 6])
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_imm : imm < 4096) :
    Rv64imShapes.LoadRegisterImmediateShape raw := by
  have h_raw : raw = Rv64imShapes.rawIType imm rs1 funct3 rd 0x03 := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rd, rs1, imm, funct3, h_rd, h_rs1, h_imm, h_mem, rfl⟩

theorem sail_encode_rawSType_contained_in_store_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm funct3 rs1 rs2 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawSType imm rs2 rs1 funct3))
    (h_mem : funct3 ∈ [0, 1, 2, 3])
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_rs2 : rs2 ∈ Rv64imShapes.allRvRegs)
    (h_imm : imm < 4096) :
    Rv64imShapes.StoreRegisterImmediateShape raw := by
  have h_raw : raw = Rv64imShapes.rawSType imm rs2 rs1 funct3 := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rs1, rs2, imm, funct3, h_rs1, h_rs2, h_imm, h_mem, rfl⟩

theorem sail_encode_rawUType_contained_in_upper_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm opcode rd : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawUType imm rd opcode))
    (h_opcode : opcode ∈ [0x37, 0x17])
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_imm_lt : imm < 2 ^ 32)
    (h_imm_aligned : imm % 4096 = 0) :
    Rv64imShapes.UpperRegisterImmediateShape raw := by
  have h_raw : raw = Rv64imShapes.rawUType imm rd opcode := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rd, imm, opcode, h_rd, h_imm_lt, h_imm_aligned, h_opcode, rfl⟩

theorem sail_encode_rawJType_contained_in_jump_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm rd : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawJType imm rd))
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_imm_lt : imm < 2097152)
    (h_imm_aligned : imm % 2 = 0) :
    Rv64imShapes.JumpRegisterImmediateShape raw := by
  have h_raw : raw = Rv64imShapes.rawJType imm rd := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rd, imm, h_rd, h_imm_lt, h_imm_aligned, rfl⟩

theorem sail_encode_rawIType_contained_in_jalr_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm rd rs1 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawIType imm rs1 0 rd 0x67))
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_imm : imm < 4096) :
    Rv64imShapes.JalrRegisterImmediateShape raw := by
  have h_raw : raw = Rv64imShapes.rawIType imm rs1 0 rd 0x67 := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, rfl⟩

theorem sail_encode_rawSupportedFence_contained_in_supported_fence_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {pred succ : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawSupportedFence pred succ))
    (h_pred : pred ∈ List.range 16)
    (h_succ : succ ∈ List.range 16) :
    Rv64imShapes.SupportedFencePredSuccShape raw := by
  have h_raw : raw = Rv64imShapes.rawSupportedFence pred succ := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨pred, succ, h_pred, h_succ, rfl⟩

theorem sail_encode_shiftI_contained_in_shift_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {shamt funct3 upper rd rs1 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawIType (upper ||| shamt) rs1 funct3 rd 0x13))
    (h_mem : (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)])
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_shamt : shamt ∈ Rv64imShapes.shift64Amounts) :
    Rv64imShapes.ShiftRegisterShape raw := by
  have h_raw :
      raw = Rv64imShapes.rawIType (upper ||| shamt) rs1 funct3 rd 0x13 := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact .inl ⟨rd, rs1, shamt, funct3, upper,
    h_rd, h_rs1, h_shamt, h_mem, rfl⟩

theorem sail_encode_shiftIW_contained_in_shift_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {shamt funct3 upper rd rs1 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawIType (upper ||| shamt) rs1 funct3 rd 0x1b))
    (h_mem : (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)])
    (h_rd : rd ∈ Rv64imShapes.allRvRegs)
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_shamt : shamt ∈ Rv64imShapes.shift32Amounts) :
    Rv64imShapes.ShiftRegisterShape raw := by
  have h_raw :
      raw = Rv64imShapes.rawIType (upper ||| shamt) rs1 funct3 rd 0x1b := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact .inr ⟨rd, rs1, shamt, funct3, upper,
    h_rd, h_rs1, h_shamt, h_mem, rfl⟩

theorem sail_encode_rawBType_contained_in_branch_shape_in
    {raw : RawInstruction} {inst : instruction} {state : SailState}
    {imm funct3 rs1 rs2 : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_encode_op :
      SailEncodesToIn state inst
        (Rv64imShapes.rawBType imm rs2 rs1 funct3))
    (h_mem : funct3 ∈ [0, 1, 4, 5, 6, 7])
    (h_rs1 : rs1 ∈ Rv64imShapes.allRvRegs)
    (h_rs2 : rs2 ∈ Rv64imShapes.allRvRegs)
    (h_imm_lt : imm < 8192)
    (h_imm_aligned : imm % 2 = 0) :
    Rv64imShapes.BranchRegisterImmediateShape raw := by
  have h_raw : raw = Rv64imShapes.rawBType imm rs2 rs1 funct3 := by
    dsimp [SailEncodesToIn, SailReturns] at h_encode h_encode_op
    rw [h_encode_op] at h_encode
    simpa using h_encode.symm
  subst raw
  exact ⟨rs1, rs2, imm, funct3,
    h_rs1, h_rs2, h_imm_lt, h_imm_aligned, h_mem, rfl⟩

theorem sail_decode_rtype_contained_in_rtype_shape_in
    {raw : RawInstruction} {state : SailState} {rs2 rs1 rd : regidx}
    (h_encode :
      SailEncodesToIn state (instruction.RTYPE (rs2, rs1, rd, op)) raw)
    (h_encode_op :
      LeanRV64D.Functions.encdec_forwards
          (instruction.RTYPE (rs2, rs1, rd, op)) =
        pure
          (Rv64imShapes.rawRType funct7
            (regidx_to_fin rs2).val
            (regidx_to_fin rs1).val
            funct3
            (regidx_to_fin rd).val
            opcode))
    (h_mem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes) :
    Rv64imShapes.RTypeRegisterShape raw :=
  sail_encode_rawRType_contained_in_rtype_shape_in
    h_encode
    (sail_encodes_to_in_of_pure h_encode_op state)
    h_mem
    (List.mem_range.mpr (regidx_to_fin rd).isLt)
    (List.mem_range.mpr (regidx_to_fin rs1).isLt)
    (List.mem_range.mpr (regidx_to_fin rs2).isLt)

theorem sail_decode_rtypew_contained_in_rtype_shape_in
    {raw : RawInstruction} {state : SailState} {rs2 rs1 rd : regidx}
    (h_encode :
      SailEncodesToIn state (instruction.RTYPEW (rs2, rs1, rd, op)) raw)
    (h_encode_op :
      LeanRV64D.Functions.encdec_forwards
          (instruction.RTYPEW (rs2, rs1, rd, op)) =
        pure
          (Rv64imShapes.rawRType funct7
            (regidx_to_fin rs2).val
            (regidx_to_fin rs1).val
            funct3
            (regidx_to_fin rd).val
            opcode))
    (h_mem : (funct7, funct3, opcode) ∈ Rv64imShapes.allRTypeOpcodeShapes) :
    Rv64imShapes.RTypeRegisterShape raw :=
  sail_encode_rawRType_contained_in_rtype_shape_in
    h_encode
    (sail_encodes_to_in_of_pure h_encode_op state)
    h_mem
    (List.mem_range.mpr (regidx_to_fin rd).isLt)
    (List.mem_range.mpr (regidx_to_fin rs1).isLt)
    (List.mem_range.mpr (regidx_to_fin rs2).isLt)

/-- Pilot Step 3 exact-shape containment for ADD. -/
theorem sail_add_executable_contained_in_add_shape :
    ∀ raw,
      SailAddExecutableRaw raw →
      Rv64imShapes.AddRawShape raw := by
  intro raw h_sail
  rcases h_sail with ⟨rs2, rs1, rd, h_decode, h_encode⟩
  exact
    sail_decode_add_contained_in_add_shape
      h_decode
      h_encode

/-- Pilot Step 3 broad-shape containment for ADD. -/
theorem sail_add_executable_contained :
    ∀ raw,
      SailAddExecutableRaw raw →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro raw h_sail
  exact
    Rv64imShapes.add_raw_shape_subset_r_type_register_shape
      (sail_add_executable_contained_in_add_shape raw h_sail)

theorem sail_register_pilot_executable_contained :
    ∀ raw inst,
      SailDecodesTo raw inst →
      SailEncodesTo inst raw →
      SailRegisterPilotInstruction inst →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro raw inst h_decode h_encode h_inst
  rcases h_inst with
    ⟨rs2, rs1, rd, h_eq⟩ | ⟨rs2, rs1, rd, h_eq⟩
  · rw [h_eq] at h_decode h_encode
    exact sail_decode_add_contained_in_rtype_shape h_decode h_encode
  · rw [h_eq] at h_decode h_encode
    exact sail_decode_sub_contained_in_rtype_shape h_decode h_encode

theorem sail_register_alu_executable_contained :
    ∀ raw inst,
      SailDecodesTo raw inst →
      SailEncodesTo inst raw →
      SailRegisterAluInstruction inst →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_add_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_sub_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_sll_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_slt_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_sltu_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_xor_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_srl_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_sra_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_or_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape h_encode
      (sail_encode_and_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])

theorem sail_register_word_alu_executable_contained :
    ∀ raw inst,
      SailDecodesTo raw inst →
      SailEncodesTo inst raw →
      SailRegisterWordAluInstruction inst →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape h_encode
      (sail_encode_addw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape h_encode
      (sail_encode_subw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape h_encode
      (sail_encode_sllw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape h_encode
      (sail_encode_srlw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape h_encode
      (sail_encode_sraw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])

theorem sail_register_alu_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailRegisterAluInstruction inst →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_add_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_sub_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_sll_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_slt_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_sltu_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_xor_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_srl_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_sra_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_or_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtype_contained_in_rtype_shape_in h_encode
      (sail_encode_and_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])

theorem sail_register_word_alu_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailRegisterWordAluInstruction inst →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape_in h_encode
      (sail_encode_addw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape_in h_encode
      (sail_encode_subw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape_in h_encode
      (sail_encode_sllw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape_in h_encode
      (sail_encode_srlw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
  · rw [h_eq] at h_encode
    exact sail_decode_rtypew_contained_in_rtype_shape_in h_encode
      (sail_encode_sraw_eq_rawRType rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])

theorem sail_m_extension_executable_contained_in :
    ∀ state raw inst,
      Rv64imEnabledSailState state →
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailMExtensionInstruction inst →
      Rv64imShapes.RTypeRegisterShape raw := by
  intro state raw inst h_state _h_decode h_encode h_inst
  rcases h_inst with
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩ |
    ⟨rs2, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_mul_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_mulh_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_mulhsu_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_mulhu_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_mulw_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_div_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_divu_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_divw_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_divuw_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_rem_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_remu_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_remw_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_rawRType_contained_in_rtype_shape_in h_encode
      (sail_encode_remuw_eq_rawRType_in state h_state rs2 rs1 rd)
      (by simp [Rv64imShapes.allRTypeOpcodeShapes])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)

theorem sail_immediate_alu_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailImmediateAluInstruction inst →
      Rv64imShapes.ImmediateAluRegisterShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_itype_eq_rawIType imm rs1 rd iop.ADDI) state)
      (by simp [LeanRV64D.Functions.encdec_iop_forwards])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_itype_eq_rawIType imm rs1 rd iop.SLTI) state)
      (by simp [LeanRV64D.Functions.encdec_iop_forwards])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_itype_eq_rawIType imm rs1 rd iop.SLTIU) state)
      (by simp [LeanRV64D.Functions.encdec_iop_forwards])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_itype_eq_rawIType imm rs1 rd iop.XORI) state)
      (by simp [LeanRV64D.Functions.encdec_iop_forwards])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_itype_eq_rawIType imm rs1 rd iop.ORI) state)
      (by simp [LeanRV64D.Functions.encdec_iop_forwards])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_itype_eq_rawIType imm rs1 rd iop.ANDI) state)
      (by simp [LeanRV64D.Functions.encdec_iop_forwards])
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt

theorem sail_shift_immediate_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailShiftImmediateInstruction inst →
      Rv64imShapes.ShiftRegisterShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨shamt, rs1, rd, h_eq⟩ |
    ⟨shamt, rs1, rd, h_eq⟩ |
    ⟨shamt, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_encode_shiftI_contained_in_shift_shape_in
      (state := state) (raw := raw)
      (inst := instruction.SHIFTIOP (shamt, rs1, rd, sop.SLLI))
      (shamt := shamt.toNat) (funct3 := 1) (upper := 0)
      (rd := (regidx_to_fin rd).val) (rs1 := (regidx_to_fin rs1).val)
      h_encode
      (by
        simpa using
          sail_encodes_to_in_of_pure
            (sail_encode_slli_eq_rawIType shamt rs1 rd) state)
      (by simp)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr shamt.isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_shiftI_contained_in_shift_shape_in
      (state := state) (raw := raw)
      (inst := instruction.SHIFTIOP (shamt, rs1, rd, sop.SRLI))
      (shamt := shamt.toNat) (funct3 := 5) (upper := 0)
      (rd := (regidx_to_fin rd).val) (rs1 := (regidx_to_fin rs1).val)
      h_encode
      (by
        simpa using
          sail_encodes_to_in_of_pure
            (sail_encode_srli_eq_rawIType shamt rs1 rd) state)
      (by simp)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr shamt.isLt)
  · rw [h_eq] at h_encode
    exact sail_encode_shiftI_contained_in_shift_shape_in
      (state := state) (raw := raw)
      (inst := instruction.SHIFTIOP (shamt, rs1, rd, sop.SRAI))
      (shamt := shamt.toNat) (funct3 := 5) (upper := 0x400)
      (rd := (regidx_to_fin rd).val) (rs1 := (regidx_to_fin rs1).val)
      h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_srai_eq_rawIType shamt rs1 rd) state)
      (by simp)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr shamt.isLt)

theorem sail_immediate_word_alu_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailImmediateWordAluInstruction inst →
      Rv64imShapes.ImmediateAluRegisterShape raw ∨
        Rv64imShapes.ShiftRegisterShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨shamt, rs1, rd, h_eq⟩ |
    ⟨shamt, rs1, rd, h_eq⟩ |
    ⟨shamt, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact .inl
      (sail_encode_rawIType_contained_in_immediate_alu_shape_in h_encode
        (sail_encodes_to_in_of_pure
          (sail_encode_addiw_eq_rawIType imm rs1 rd) state)
        (by simp)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (List.mem_range.mpr (regidx_to_fin rs1).isLt)
        imm.isLt)
  · rw [h_eq] at h_encode
    exact .inr
      (sail_encode_shiftIW_contained_in_shift_shape_in
        (state := state) (raw := raw)
        (inst := instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SLLIW))
        (shamt := shamt.toNat) (funct3 := 1) (upper := 0)
        (rd := (regidx_to_fin rd).val) (rs1 := (regidx_to_fin rs1).val)
        h_encode
        (by
          simpa using
            sail_encodes_to_in_of_pure
              (sail_encode_slliw_eq_rawIType shamt rs1 rd) state)
        (by simp)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (List.mem_range.mpr (regidx_to_fin rs1).isLt)
        (List.mem_range.mpr shamt.isLt))
  · rw [h_eq] at h_encode
    exact .inr
      (sail_encode_shiftIW_contained_in_shift_shape_in
        (state := state) (raw := raw)
        (inst := instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRLIW))
        (shamt := shamt.toNat) (funct3 := 5) (upper := 0)
        (rd := (regidx_to_fin rd).val) (rs1 := (regidx_to_fin rs1).val)
        h_encode
        (by
          simpa using
            sail_encodes_to_in_of_pure
              (sail_encode_srliw_eq_rawIType shamt rs1 rd) state)
        (by simp)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (List.mem_range.mpr (regidx_to_fin rs1).isLt)
        (List.mem_range.mpr shamt.isLt))
  · rw [h_eq] at h_encode
    exact .inr
      (sail_encode_shiftIW_contained_in_shift_shape_in
        (state := state) (raw := raw)
        (inst := instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRAIW))
        (shamt := shamt.toNat) (funct3 := 5) (upper := 0x400)
        (rd := (regidx_to_fin rd).val) (rs1 := (regidx_to_fin rs1).val)
        h_encode
        (sail_encodes_to_in_of_pure
          (sail_encode_sraiw_eq_rawIType shamt rs1 rd) state)
        (by simp)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (List.mem_range.mpr (regidx_to_fin rs1).isLt)
        (List.mem_range.mpr shamt.isLt))

theorem sail_branch_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailBranchInstruction inst →
      Rv64imShapes.BranchRegisterImmediateShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨imm, rs2, rs1, h_align, h_eq⟩ |
    ⟨imm, rs2, rs1, h_align, h_eq⟩ |
    ⟨imm, rs2, rs1, h_align, h_eq⟩ |
    ⟨imm, rs2, rs1, h_align, h_eq⟩ |
    ⟨imm, rs2, rs1, h_align, h_eq⟩ |
    ⟨imm, rs2, rs1, h_align, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_encode_rawBType_contained_in_branch_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BEQ h_align) state)
      (by simp [LeanRV64D.Functions.encdec_bop_forwards])
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
      (sail_btype_align_toNat_mod_two imm h_align)
  · rw [h_eq] at h_encode
    exact sail_encode_rawBType_contained_in_branch_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BNE h_align) state)
      (by simp [LeanRV64D.Functions.encdec_bop_forwards])
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
      (sail_btype_align_toNat_mod_two imm h_align)
  · rw [h_eq] at h_encode
    exact sail_encode_rawBType_contained_in_branch_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BLT h_align) state)
      (by simp [LeanRV64D.Functions.encdec_bop_forwards])
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
      (sail_btype_align_toNat_mod_two imm h_align)
  · rw [h_eq] at h_encode
    exact sail_encode_rawBType_contained_in_branch_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BGE h_align) state)
      (by simp [LeanRV64D.Functions.encdec_bop_forwards])
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
      (sail_btype_align_toNat_mod_two imm h_align)
  · rw [h_eq] at h_encode
    exact sail_encode_rawBType_contained_in_branch_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BLTU h_align) state)
      (by simp [LeanRV64D.Functions.encdec_bop_forwards])
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
      (sail_btype_align_toNat_mod_two imm h_align)
  · rw [h_eq] at h_encode
    exact sail_encode_rawBType_contained_in_branch_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BGEU h_align) state)
      (by simp [LeanRV64D.Functions.encdec_bop_forwards])
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
      (sail_btype_align_toNat_mod_two imm h_align)

theorem sail_load_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailLoadInstruction inst →
      Rv64imShapes.LoadRegisterImmediateShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_lb_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_lh_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_lw_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_ld_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_lbu_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_lhu_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawIType_contained_in_load_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_lwu_eq_rawIType imm rs1 rd) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt

theorem sail_store_executable_contained_in :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailStoreInstruction inst →
      Rv64imShapes.StoreRegisterImmediateShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨imm, rs2, rs1, h_eq⟩ |
    ⟨imm, rs2, rs1, h_eq⟩ |
    ⟨imm, rs2, rs1, h_eq⟩ |
    ⟨imm, rs2, rs1, h_eq⟩
  · rw [h_eq] at h_encode
    exact sail_encode_rawSType_contained_in_store_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_sb_eq_rawSType imm rs2 rs1) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawSType_contained_in_store_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_sh_eq_rawSType imm rs2 rs1) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawSType_contained_in_store_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_sw_eq_rawSType imm rs2 rs1) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt
  · rw [h_eq] at h_encode
    exact sail_encode_rawSType_contained_in_store_shape_in h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_sd_eq_rawSType imm rs2 rs1) state)
      (by native_decide)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      (List.mem_range.mpr (regidx_to_fin rs2).isLt)
      imm.isLt

theorem sail_upper_jump_executable_contained_in_supported_decode :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailUpperJumpInstruction inst →
      Rv64imShapes.SupportedDecodeShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with
    ⟨imm, rd, h_eq⟩ |
    ⟨imm, rd, h_eq⟩ |
    ⟨imm, rd, h_align, h_eq⟩ |
    ⟨imm, rs1, rd, h_eq⟩
  · rw [h_eq] at h_encode
    exact Rv64imShapes.upper_register_immediate_shape_subset_supported_decode
      (sail_encode_rawUType_contained_in_upper_shape_in h_encode
        (sail_encodes_to_in_of_pure
          (sail_encode_utype_eq_rawUType imm rd uop.LUI) state)
        (by native_decide)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (sail_utype_shift_toNat_lt imm)
        (sail_utype_shift_toNat_mod_4096 imm))
  · rw [h_eq] at h_encode
    exact Rv64imShapes.upper_register_immediate_shape_subset_supported_decode
      (sail_encode_rawUType_contained_in_upper_shape_in h_encode
        (sail_encodes_to_in_of_pure
          (sail_encode_utype_eq_rawUType imm rd uop.AUIPC) state)
        (by native_decide)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (sail_utype_shift_toNat_lt imm)
        (sail_utype_shift_toNat_mod_4096 imm))
  · rw [h_eq] at h_encode
    exact Rv64imShapes.jump_register_immediate_shape_subset_supported_decode
      (sail_encode_rawJType_contained_in_jump_shape_in h_encode
        (sail_encodes_to_in_of_pure
          (sail_encode_jal_eq_rawJType imm rd h_align) state)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        imm.isLt
        (sail_jal_align_toNat_mod_two imm h_align))
  · rw [h_eq] at h_encode
    exact Rv64imShapes.jalr_register_immediate_shape_subset_supported_decode
      (sail_encode_rawIType_contained_in_jalr_shape_in h_encode
        (sail_encodes_to_in_of_pure
          (sail_encode_jalr_eq_rawIType imm rs1 rd) state)
        (List.mem_range.mpr (regidx_to_fin rd).isLt)
        (List.mem_range.mpr (regidx_to_fin rs1).isLt)
        imm.isLt)

theorem sail_supported_fence_executable_contained_in_supported_decode :
    ∀ state raw inst,
      SailDecodesToIn state raw inst →
      SailEncodesToIn state inst raw →
      SailSupportedFenceInstruction inst →
      Rv64imShapes.SupportedDecodeShape raw := by
  intro state raw inst _h_decode h_encode h_inst
  rcases h_inst with ⟨pred, succ, h_eq⟩
  rw [h_eq] at h_encode
  exact .inr (.inr (.inr (.inr (.inr (.inr
    (sail_encode_rawSupportedFence_contained_in_supported_fence_shape_in
      h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_supported_fence_eq_rawSupportedFence pred succ) state)
      (List.mem_range.mpr pred.isLt)
      (List.mem_range.mpr succ.isLt)))))))

theorem sail_rv64im_executable_contained_in_supported_decode :
    ∀ raw,
      SailRv64imExecutableRaw raw →
      Rv64imShapes.SupportedDecodeShape raw := by
  intro raw h_sail
  rcases h_sail with ⟨inst, h_decode, h_encode, h_inst⟩
  rcases h_inst with h_register_alu | h_register_word_alu
  · exact .inl
      (sail_register_alu_executable_contained
        raw inst h_decode h_encode h_register_alu)
  · exact .inl
      (sail_register_word_alu_executable_contained
        raw inst h_decode h_encode h_register_word_alu)

theorem sail_rv64im_executable_contained_in_supported_decode_pilot :
    ∀ raw,
      SailRv64imExecutableRaw raw →
      Rv64imShapes.SupportedDecodeShape raw :=
  sail_rv64im_executable_contained_in_supported_decode

theorem sail_rv64im_executable_contained_in_supported_decode_in :
    ∀ state raw,
      Rv64imEnabledSailState state →
      SailRv64imExecutableRawIn state raw →
      Rv64imShapes.SupportedDecodeShape raw := by
  intro state raw h_state h_sail
  rcases h_sail with ⟨inst, h_decode, h_encode, h_inst⟩
  rcases h_inst with h_register_alu | h_tail
  · exact .inl
      (sail_register_alu_executable_contained_in
        state raw inst h_decode h_encode h_register_alu)
  rcases h_tail with h_register_word_alu | h_tail
  · exact .inl
      (sail_register_word_alu_executable_contained_in
        state raw inst h_decode h_encode h_register_word_alu)
  rcases h_tail with h_m_extension | h_tail
  · exact .inl
      (sail_m_extension_executable_contained_in
        state raw inst h_state h_decode h_encode h_m_extension)
  rcases h_tail with h_immediate_alu | h_tail
  · exact
      Rv64imShapes.immediate_alu_register_shape_subset_supported_decode
        (sail_immediate_alu_executable_contained_in
          state raw inst h_decode h_encode h_immediate_alu)
  rcases h_tail with h_shift_immediate | h_tail
  · exact .inr (.inr (.inl
      (sail_shift_immediate_executable_contained_in
        state raw inst h_decode h_encode h_shift_immediate)))
  rcases h_tail with h_immediate_word_alu | h_tail
  · rcases
      sail_immediate_word_alu_executable_contained_in
        state raw inst h_decode h_encode h_immediate_word_alu with
      h_immediate_alu | h_shift
    · exact
        Rv64imShapes.immediate_alu_register_shape_subset_supported_decode
          h_immediate_alu
    · exact .inr (.inr (.inl h_shift))
  rcases h_tail with h_branch | h_tail
  · exact .inr (.inr (.inr (.inr (.inl
      (sail_branch_executable_contained_in
        state raw inst h_decode h_encode h_branch)))))
  rcases h_tail with h_load | h_tail
  · exact .inr (.inl
      (Rv64imShapes.load_register_immediate_shape_subset
        (sail_load_executable_contained_in
          state raw inst h_decode h_encode h_load)))
  rcases h_tail with h_store | h_tail
  · exact .inr (.inr (.inr (.inl
      (sail_store_executable_contained_in
        state raw inst h_decode h_encode h_store))))
  rcases h_tail with h_upper_jump | h_fence
  · exact sail_upper_jump_executable_contained_in_supported_decode
      state raw inst h_decode h_encode h_upper_jump
  · exact sail_supported_fence_executable_contained_in_supported_decode
      state raw inst h_decode h_encode h_fence


end ZiskFv.Completeness.SailDecode
