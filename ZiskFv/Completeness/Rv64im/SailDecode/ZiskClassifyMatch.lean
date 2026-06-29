/-
ZiskFv/Completeness/Rv64im/SailDecode/ZiskClassifyMatch.lean  (eth-act/zisk-fv#162)

EXPLICIT Sail-spec ↔ ZisK-decoder opcode match.  Composes the kernel-sound ZisK
classification (`ZiskFv/Compliance/AeneasBridgeTrust/Decode/Classify.lean`,
`*_classifies`) with the existing Sail encode-equality lemmas
(`SailDecode/{ConcatShapes,EncodeFacts}.lean`) to prove: for every RV64IM
instruction `inst` that the Sail spec decodes a raw word `raw` to, ZisK's real
extracted decoder `decode_32_core` classifies `raw` to exactly `inst`'s opcode
(`riscvOpcodeOfSailInstr inst`).

NATIVE_DECIDE BOUNDARY: the ZisK classification half is kernel-sound; the Sail
encode-equality lemmas this file composes with currently carry `native_decide`
(eth-act/zisk-fv#174, under #75).  This file INTRODUCES NO NEW `native_decide`;
it only reuses the existing ones.  When #174 lands, the match theorems here
become kernel-sound with no change to this file.
-/
import ZiskFv.Completeness.Rv64im.SailDecode
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Classify

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Completeness ZiskFv.Completeness.Rv64imShapes
open ZiskFv.Compliance.Decode

namespace ZiskFv.Completeness.SailDecode

/-- The ZisK `RiscvOpcode` corresponding to a Sail-decoded `instruction`.  Pinned
to `decode_32_core` (via the `*_classifies` lemmas) by `rfl` in the per-family
match helpers — any mismatch fails the build.  Only the RV64IM-supported
constructors are mapped; everything else is `Unsupported`. -/
def riscvOpcodeOfSailInstr : instruction → RiscvOpcode
  | .RTYPE (_, _, _, .ADD) => .Add
  | .RTYPE (_, _, _, .SUB) => .Sub
  | .RTYPE (_, _, _, .SLL) => .Sll
  | .RTYPE (_, _, _, .SLT) => .Slt
  | .RTYPE (_, _, _, .SLTU) => .Sltu
  | .RTYPE (_, _, _, .XOR) => .Xor
  | .RTYPE (_, _, _, .SRL) => .Srl
  | .RTYPE (_, _, _, .SRA) => .Sra
  | .RTYPE (_, _, _, .OR) => .Or
  | .RTYPE (_, _, _, .AND) => .And
  | .RTYPEW (_, _, _, .ADDW) => .Addw
  | .RTYPEW (_, _, _, .SUBW) => .Subw
  | .RTYPEW (_, _, _, .SLLW) => .Sllw
  | .RTYPEW (_, _, _, .SRLW) => .Srlw
  | .RTYPEW (_, _, _, .SRAW) => .Sraw
  | .MUL (_, _, _, ⟨.Low, .Signed, .Signed⟩) => .Mul
  | .MUL (_, _, _, ⟨.High, .Signed, .Signed⟩) => .Mulh
  | .MUL (_, _, _, ⟨.High, .Signed, .Unsigned⟩) => .Mulhsu
  | .MUL (_, _, _, ⟨.High, .Unsigned, .Unsigned⟩) => .Mulhu
  | .MULW (_, _, _) => .Mulw
  | .DIV (_, _, _, false) => .Div
  | .DIV (_, _, _, true) => .Divu
  | .DIVW (_, _, _, false) => .Divw
  | .DIVW (_, _, _, true) => .Divuw
  | .REM (_, _, _, false) => .Rem
  | .REM (_, _, _, true) => .Remu
  | .REMW (_, _, _, false) => .Remw
  | .REMW (_, _, _, true) => .Remuw
  | .ITYPE (_, _, _, .ADDI) => .Addi
  | .ITYPE (_, _, _, .SLTI) => .Slti
  | .ITYPE (_, _, _, .SLTIU) => .Sltiu
  | .ITYPE (_, _, _, .XORI) => .Xori
  | .ITYPE (_, _, _, .ORI) => .Ori
  | .ITYPE (_, _, _, .ANDI) => .Andi
  | .SHIFTIOP (_, _, _, .SLLI) => .Slli
  | .SHIFTIOP (_, _, _, .SRLI) => .Srli
  | .SHIFTIOP (_, _, _, .SRAI) => .Srai
  | .ADDIW (_, _, _) => .Addiw
  | .SHIFTIWOP (_, _, _, .SLLIW) => .Slliw
  | .SHIFTIWOP (_, _, _, .SRLIW) => .Srliw
  | .SHIFTIWOP (_, _, _, .SRAIW) => .Sraiw
  | .BTYPE (_, _, _, .BEQ) => .Beq
  | .BTYPE (_, _, _, .BNE) => .Bne
  | .BTYPE (_, _, _, .BLT) => .Blt
  | .BTYPE (_, _, _, .BGE) => .Bge
  | .BTYPE (_, _, _, .BLTU) => .Bltu
  | .BTYPE (_, _, _, .BGEU) => .Bgeu
  | .LOAD (_, _, _, false, (1 : Int)) => .Lb
  | .LOAD (_, _, _, false, (2 : Int)) => .Lh
  | .LOAD (_, _, _, false, (4 : Int)) => .Lw
  | .LOAD (_, _, _, false, (8 : Int)) => .Ld
  | .LOAD (_, _, _, true, (1 : Int)) => .Lbu
  | .LOAD (_, _, _, true, (2 : Int)) => .Lhu
  | .LOAD (_, _, _, true, (4 : Int)) => .Lwu
  | .STORE (_, _, _, (1 : Int)) => .Sb
  | .STORE (_, _, _, (2 : Int)) => .Sh
  | .STORE (_, _, _, (4 : Int)) => .Sw
  | .STORE (_, _, _, (8 : Int)) => .Sd
  | .UTYPE (_, _, .LUI) => .Lui
  | .UTYPE (_, _, .AUIPC) => .Auipc
  | .JAL _ => .Jal
  | .JALR _ => .Jalr
  | .FENCE _ => .Fence
  | _ => .Unsupported

/-- Extract `raw = rawval` from two state-aware encode relations of the same
instruction (`SailReturns` is functional). -/
theorem raw_eq_in {state : SailState} {inst : instruction} {raw rawval : RawInstruction}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst rawval) :
    raw = rawval := by
  dsimp [SailEncodesToIn, SailReturns] at h_encode h_op
  rw [h_op] at h_encode
  simpa using h_encode.symm

/-! ## Per-format match helpers.  Each composes `raw_eq_in` (raw shape from the
existing Sail encode lemma) with the kernel-sound `*_classifies` (ZisK opcode),
then pins `<fmt>Opcode = riscvOpcodeOfSailInstr inst` by the caller's `rfl`. -/

theorem rtype_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    (funct7 funct3 opcode : Nat) {rs2v rs1v rdv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawRType funct7 rs2v rs1v funct3 rdv opcode))
    (hmem : (funct7, funct3, opcode) ∈ allRTypeOpcodeShapes)
    (hrd : rdv < 32) (hrs1 : rs1v < 32) (hrs2 : rs2v < 32)
    (hop : rtypeOpcode funct7 funct3 opcode = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := rtype_family_classifies funct7 funct3 opcode rdv rs1v rs2v hmem hrd hrs1 hrs2
  exact ⟨d, hd, ho.trans hop⟩

theorem itype_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immv funct3 opcode rs1v rdv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawIType immv rs1v funct3 rdv opcode))
    (hmem : (funct3, opcode) ∈ [
      (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
      (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)])
    (hrd : rdv < 32) (hrs1 : rs1v < 32) (himm : immv < 4096)
    (hop : itypeOpcode funct3 opcode = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := itype_family_classifies rdv rs1v immv funct3 opcode hrd hrs1 himm hmem
  exact ⟨d, hd, ho.trans hop⟩

theorem stype_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immv funct3 rs2v rs1v : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawSType immv rs2v rs1v funct3))
    (hmem : funct3 ∈ [0, 1, 2, 3])
    (hrs1 : rs1v < 32) (hrs2 : rs2v < 32) (himm : immv < 4096)
    (hop : stypeOpcode funct3 = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := stype_family_classifies rs1v rs2v immv funct3 hrs1 hrs2 himm hmem
  exact ⟨d, hd, ho.trans hop⟩

theorem btype_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immv funct3 rs2v rs1v : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawBType immv rs2v rs1v funct3))
    (hmem : funct3 ∈ [0, 1, 4, 5, 6, 7])
    (hrs1 : rs1v < 32) (hrs2 : rs2v < 32) (himm : immv < 8192)
    (hop : btypeOpcode funct3 = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := btype_family_classifies rs1v rs2v immv funct3 hrs1 hrs2 himm hmem
  exact ⟨d, hd, ho.trans hop⟩

theorem utype_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immv opcode rdv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawUType immv rdv opcode))
    (hmem : opcode ∈ [0x37, 0x17]) (hrd : rdv < 32)
    (hop : utypeOpcode opcode = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := utype_family_classifies rdv immv opcode hrd hmem
  exact ⟨d, hd, ho.trans hop⟩

theorem jtype_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immv rdv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawJType immv rdv))
    (hop : RiscvOpcode.Jal = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := jtype_family_classifies rdv immv
  exact ⟨d, hd, ho.trans hop⟩

theorem shift64_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immfield shamtv funct3 upper rs1v rdv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawIType immfield rs1v funct3 rdv 0x13))
    (himmf : immfield = upper ||| shamtv)
    (hfu : (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)])
    (hrd : rdv < 32) (hrs1 : rs1v < 32) (hsh : shamtv < 64)
    (hop : shift64Opcode funct3 upper = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  rw [himmf]
  obtain ⟨d, hd, ho⟩ := shift64_family_classifies rdv rs1v shamtv funct3 upper hrd hrs1 hsh hfu
  exact ⟨d, hd, ho.trans hop⟩

theorem shift32_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {immfield shamtv funct3 upper rs1v rdv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawIType immfield rs1v funct3 rdv 0x1b))
    (himmf : immfield = upper ||| shamtv)
    (hfu : (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)])
    (hrd : rdv < 32) (hrs1 : rs1v < 32) (hsh : shamtv < 32)
    (hop : shift32Opcode funct3 upper = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  rw [himmf]
  obtain ⟨d, hd, ho⟩ := shift32_family_classifies rdv rs1v shamtv funct3 upper hrd hrs1 hsh hfu
  exact ⟨d, hd, ho.trans hop⟩

theorem fence_match {state : SailState} {raw : RawInstruction} {inst : instruction}
    {predv succv : Nat}
    (h_encode : SailEncodesToIn state inst raw)
    (h_op : SailEncodesToIn state inst (rawSupportedFence predv succv))
    (hp : predv < 16) (hs : succv < 16)
    (hop : RiscvOpcode.Fence = riscvOpcodeOfSailInstr inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  have hraw := raw_eq_in h_encode h_op; subst hraw
  obtain ⟨d, hd, ho⟩ := fence_family_classifies predv succv hp hs
  exact ⟨d, hd, ho.trans hop⟩

/-- **Per-family classification match.** -/
theorem matches_of_instruction {state : SailState} {raw : RawInstruction} {inst : instruction}
    (h_state : IsaExtensionsEnabled state)
    (h_encode : SailEncodesToIn state inst raw)
    (h_inst : SailRv64imInstruction inst) :
    ∃ d, decode_32_core (toU32 raw) = ok d ∧ d.opcode = riscvOpcodeOfSailInstr inst := by
  rcases h_inst with hRA | hRWA | hM | hIA | hSI | hIWA | hB | hL | hS | hUJ | hF
  -- register ALU
  · rcases hRA with ⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩
    · exact rtype_match 0 0 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_add_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 32 0 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_sub_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 1 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_sll_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 2 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_slt_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 3 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_sltu_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 4 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_xor_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 5 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_srl_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 32 5 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_sra_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 6 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_or_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 7 0x33 h_encode (sail_encodes_to_in_of_pure (sail_encode_and_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
  -- register word ALU
  · rcases hRWA with ⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩
    · exact rtype_match 0 0 0x3b h_encode (sail_encodes_to_in_of_pure (sail_encode_addw_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 32 0 0x3b h_encode (sail_encodes_to_in_of_pure (sail_encode_subw_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 1 0x3b h_encode (sail_encodes_to_in_of_pure (sail_encode_sllw_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 0 5 0x3b h_encode (sail_encodes_to_in_of_pure (sail_encode_srlw_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 32 5 0x3b h_encode (sail_encodes_to_in_of_pure (sail_encode_sraw_eq_rawRType rs2 rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
  -- M extension
  · rcases hM with ⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩|⟨rs2,rs1,rd,rfl⟩
    · exact rtype_match 1 0 0x33 h_encode (sail_encode_mul_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 1 0x33 h_encode (sail_encode_mulh_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 2 0x33 h_encode (sail_encode_mulhsu_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 3 0x33 h_encode (sail_encode_mulhu_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 0 0x3b h_encode (sail_encode_mulw_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 4 0x33 h_encode (sail_encode_div_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 5 0x33 h_encode (sail_encode_divu_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 4 0x3b h_encode (sail_encode_divw_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 5 0x3b h_encode (sail_encode_divuw_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 6 0x33 h_encode (sail_encode_rem_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 7 0x33 h_encode (sail_encode_remu_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 6 0x3b h_encode (sail_encode_remw_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
    · exact rtype_match 1 7 0x3b h_encode (sail_encode_remuw_eq_rawRType_in state h_state rs2 rs1 rd) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt rfl
  -- immediate ALU
  · rcases hIA with ⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_itype_eq_rawIType imm rs1 rd iop.ADDI) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_itype_eq_rawIType imm rs1 rd iop.SLTI) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_itype_eq_rawIType imm rs1 rd iop.SLTIU) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_itype_eq_rawIType imm rs1 rd iop.XORI) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_itype_eq_rawIType imm rs1 rd iop.ORI) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_itype_eq_rawIType imm rs1 rd iop.ANDI) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
  -- shift immediate (64-bit)
  · rcases hSI with ⟨shamt,rs1,rd,rfl⟩|⟨shamt,rs1,rd,rfl⟩|⟨shamt,rs1,rd,rfl⟩
    · exact shift64_match h_encode (sail_encodes_to_in_of_pure (sail_encode_slli_eq_rawIType shamt rs1 rd) state) (Nat.zero_or _).symm (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt shamt.isLt rfl
    · exact shift64_match h_encode (sail_encodes_to_in_of_pure (sail_encode_srli_eq_rawIType shamt rs1 rd) state) (Nat.zero_or _).symm (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt shamt.isLt rfl
    · exact shift64_match h_encode (sail_encodes_to_in_of_pure (sail_encode_srai_eq_rawIType shamt rs1 rd) state) rfl (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt shamt.isLt rfl
  -- immediate word ALU (ADDIW + word shifts)
  · rcases hIWA with ⟨imm,rs1,rd,rfl⟩|⟨shamt,rs1,rd,rfl⟩|⟨shamt,rs1,rd,rfl⟩|⟨shamt,rs1,rd,rfl⟩
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_addiw_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact shift32_match h_encode (sail_encodes_to_in_of_pure (sail_encode_slliw_eq_rawIType shamt rs1 rd) state) (Nat.zero_or _).symm (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt shamt.isLt rfl
    · exact shift32_match h_encode (sail_encodes_to_in_of_pure (sail_encode_srliw_eq_rawIType shamt rs1 rd) state) (Nat.zero_or _).symm (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt shamt.isLt rfl
    · exact shift32_match h_encode (sail_encodes_to_in_of_pure (sail_encode_sraiw_eq_rawIType shamt rs1 rd) state) rfl (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt shamt.isLt rfl
  -- branches
  · rcases hB with ⟨imm,rs2,rs1,ha,rfl⟩|⟨imm,rs2,rs1,ha,rfl⟩|⟨imm,rs2,rs1,ha,rfl⟩|⟨imm,rs2,rs1,ha,rfl⟩|⟨imm,rs2,rs1,ha,rfl⟩|⟨imm,rs2,rs1,ha,rfl⟩
    · exact btype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BEQ ha) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact btype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BNE ha) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact btype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BLT ha) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact btype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BGE ha) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact btype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BLTU ha) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact btype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_btype_eq_rawBType imm rs2 rs1 bop.BGEU ha) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
  -- loads
  · rcases hL with ⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩|⟨imm,rs1,rd,rfl⟩
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_lb_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_lh_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_lw_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_ld_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_lbu_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_lhu_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_lwu_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
  -- stores
  · rcases hS with ⟨imm,rs2,rs1,rfl⟩|⟨imm,rs2,rs1,rfl⟩|⟨imm,rs2,rs1,rfl⟩|⟨imm,rs2,rs1,rfl⟩
    · exact stype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_sb_eq_rawSType imm rs2 rs1) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact stype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_sh_eq_rawSType imm rs2 rs1) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact stype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_sw_eq_rawSType imm rs2 rs1) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
    · exact stype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_sd_eq_rawSType imm rs2 rs1) state) (by decide) (regidx_to_fin rs1).isLt (regidx_to_fin rs2).isLt imm.isLt rfl
  -- upper / jump
  · rcases hUJ with ⟨imm,rd,rfl⟩|⟨imm,rd,rfl⟩|⟨imm,rd,ha,rfl⟩|⟨imm,rs1,rd,rfl⟩
    · exact utype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_utype_eq_rawUType imm rd uop.LUI) state) (by decide) (regidx_to_fin rd).isLt rfl
    · exact utype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_utype_eq_rawUType imm rd uop.AUIPC) state) (by decide) (regidx_to_fin rd).isLt rfl
    · exact jtype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_jal_eq_rawJType imm rd ha) state) rfl
    · exact itype_match h_encode (sail_encodes_to_in_of_pure (sail_encode_jalr_eq_rawIType imm rs1 rd) state) (by decide) (regidx_to_fin rd).isLt (regidx_to_fin rs1).isLt imm.isLt rfl
  -- fence
  · rcases hF with ⟨pred,succ,rfl⟩
    exact fence_match h_encode (sail_encodes_to_in_of_pure (sail_encode_supported_fence_eq_rawSupportedFence pred succ) state) pred.isLt succ.isLt rfl

/-- **Explicit Sail-spec ↔ ZisK opcode match (eth-act/zisk-fv#162).** For every raw
word the Sail spec decodes to a supported RV64IM instruction `inst`, ZisK's real
extracted decoder `decode_32_core` classifies it to exactly `inst`'s opcode. -/
theorem zisk_decoder_classifies_matches_sail (state : SailState) (raw : RawInstruction)
    (h_state : IsaExtensionsEnabled state)
    (h_exec : SailRv64imExecutableRawIn state raw) :
    ∃ inst d, SailDecodesToIn state raw inst ∧
      decode_32_core (toU32 raw) = ok d ∧
      d.opcode = riscvOpcodeOfSailInstr inst := by
  obtain ⟨inst, h_decode, h_encode, h_inst⟩ := h_exec
  obtain ⟨d, hd, hop⟩ := matches_of_instruction h_state h_encode h_inst
  exact ⟨inst, d, h_decode, hd, hop⟩

end ZiskFv.Completeness.SailDecode
