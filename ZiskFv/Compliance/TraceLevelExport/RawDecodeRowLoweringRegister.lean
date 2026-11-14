import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLoweringBase

/-!
# Source widths for register and immediate raw-decode evidence

The witnesses below use the actual `transpile_<op>` results exported by
`RawProgramBindingRegister`, `RawProgramBindingImmediate`, and
`RawProgramBindingCopyb`. Their nonzero opcode pins rule out the terminal
extractor's rejected/default arm; the source's non-JALR branch then supplies
an accepted `SuccessfulRowLowering` of width one.

The conditional-copyb families retain exactly their existing raw-decode
boundaries, rather than adding exclusions here. In particular, unconditional
register/shift families and OR/XORI/ORI keep their permitted zero destinations.
ADDI's decoded-immediate guard is derived from its existing `himm0` field.
-/

namespace ZiskFv.Compliance.RawDecodeRowLowering

open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

/-! The producer modules already use local per-family command macros; these
only share the repeated proof, not a new raw-program interface. -/

local macro "register_source_width" nm:ident : command => do
  let s := nm.getId.toString
  let name := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("transpile_" ++ s))
  `(theorem $name {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    obtain ⟨ext, hok, hop, _⟩ := $transpileName
      (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val
      (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
    refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
    have haccepted := accepted_of_live_terminal _ ext hok
      (Or.inl (by rw [hop]; decide))
    refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
    rw [ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.rawRType_opcode]
    all_goals decide)

register_source_width sub
register_source_width and
register_source_width xor
register_source_width slt
register_source_width sltu
register_source_width sll
register_source_width srl
register_source_width sra
register_source_width addw
register_source_width subw
register_source_width sllw
register_source_width srlw
register_source_width sraw
register_source_width mulw

local macro "immediate_source_width" nm:ident : command => do
  let s := nm.getId.toString
  let name := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("transpile_" ++ s))
  `(theorem $name {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    obtain ⟨ext, hok, hop, _⟩ := $transpileName
      (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val c.imm.toNat
      (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt
    refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
    have haccepted := accepted_of_live_terminal _ ext hok
      (Or.inl (by rw [hop]; decide))
    refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
    rw [ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.rawIType_opcode]
    all_goals decide)

immediate_source_width slti
immediate_source_width sltiu
immediate_source_width andi

local macro "shift_source_width" nm:ident "," shget:term : command => do
  let s := nm.getId.toString
  let name := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("transpile_" ++ s))
  `(theorem $name {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    obtain ⟨ext, hok, hop, _⟩ := $transpileName
      (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val ($shget c).shamt.toNat
      (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt ($shget c).shamt.isLt
    refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
    have haccepted := accepted_of_live_terminal _ ext hok
      (Or.inl (by rw [hop]; decide))
    refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
    rw [ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.rawIType_opcode]
    all_goals decide)

shift_source_width slli, (fun c => c)
shift_source_width srli, (fun c => c)
shift_source_width srai, (fun c => c)
shift_source_width slliw, ZiskFv.Compliance.Claim_slliw.slliw_input
shift_source_width srliw, ZiskFv.Compliance.Claim_srliw.srliw_input
shift_source_width sraiw, ZiskFv.Compliance.Claim_sraiw.sraiw_input

/-! These are the source-special dispatcher families. All guard evidence is
already present in their corresponding `RawProgramDecode_<op>` structures. -/

theorem sourceWidth_add {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_add trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_add trace i c addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨ext, hok, hop, _⟩ := transpile_add
    (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val
    (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
    rawDecode.hrd0 rawDecode.hrs10 rawDecode.hrs20
  refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
  have haccepted := accepted_of_live_terminal _ ext hok
    (Or.inl (by rw [hop]; decide))
  refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
  rw [ZiskFv.Compliance.Decode.toU32_and127,
    ZiskFv.Compliance.Decode.rawRType_opcode]
  all_goals decide

theorem sourceWidth_or {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_or trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_or trace i c addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨ext, hok, hop, _⟩ := transpile_or
    (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val
    (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
    rawDecode.hrs10 rawDecode.hrs20
  refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
  have haccepted := accepted_of_live_terminal _ ext hok
    (Or.inl (by rw [hop]; decide))
  refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
  rw [ZiskFv.Compliance.Decode.toU32_and127,
    ZiskFv.Compliance.Decode.rawRType_opcode]
  all_goals decide

local macro "copyb_immediate_source_width" nm:ident : command => do
  let s := nm.getId.toString
  let name := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("transpile_" ++ s))
  `(theorem $name {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    obtain ⟨ext, hok, hop, _⟩ := $transpileName
      (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val c.imm.toNat
      (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt rawDecode.hrs10
    refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
    have haccepted := accepted_of_live_terminal _ ext hok
      (Or.inl (by rw [hop]; decide))
    refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
    rw [ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.rawIType_opcode]
    all_goals decide)

copyb_immediate_source_width xori
copyb_immediate_source_width ori

theorem sourceWidth_addiw {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_addiw trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_addiw trace i c addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨ext, hok, hop, _⟩ := transpile_addiw
    (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val c.imm.toNat
    (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt rawDecode.h_rd_ne_zero
  refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
  have haccepted := accepted_of_live_terminal _ ext hok
    (Or.inl (by rw [hop]; decide))
  refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
  rw [ZiskFv.Compliance.Decode.toU32_and127,
    ZiskFv.Compliance.Decode.rawIType_opcode]
  all_goals decide

theorem sourceWidth_addi {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_addi trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_addi trace i c addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  have himm : ∀ d, aeneas_extract.rv64im_decode.decode_i
      (ZiskFv.Compliance.Decode.toU32
        (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
          (regidx_to_fin c.r1).val 0 (regidx_to_fin c.rd).val 0x13))
      aeneas_extract.rv64im_decode.RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32 := by
    intro d hd hz
    have hb := decode_i_rawIType_imm c.imm.toNat (regidx_to_fin c.r1).val 0
      (regidx_to_fin c.rd).val 0x13 (regidx_to_fin c.r1).isLt (by decide)
      (regidx_to_fin c.rd).isLt (by decide)
      aeneas_extract.rv64im_decode.RiscvOpcode.Addi d hd
    rw [hz] at hb
    have ht := congrArg BitVec.toInt hb
    simp only [BitVec.ofNat_toNat, BitVec.toInt_zero,
      BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 32)] at ht
    apply rawDecode.himm0
    apply BitVec.eq_of_toInt_eq
    exact ht.symm
  obtain ⟨ext, hok, hop, _⟩ := transpile_addi
    (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val c.imm.toNat
    (regidx_to_fin c.rd).isLt (regidx_to_fin c.r1).isLt
    rawDecode.hrd0 rawDecode.hrs10 himm
  refine at_pc_of_word trace i addr rawProgram _ 1 rawDecode.hLine ?_
  have haccepted := accepted_of_live_terminal _ ext hok
    (Or.inl (by rw [hop]; decide))
  refine ⟨oneOfTerminal ext hok haccepted ?_, rfl⟩
  rw [ZiskFv.Compliance.Decode.toU32_and127,
    ZiskFv.Compliance.Decode.rawIType_opcode]
  all_goals decide

end ZiskFv.Compliance.RawDecodeRowLowering
