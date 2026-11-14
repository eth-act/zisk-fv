import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLoweringBase

/-!
# Existing M-extension/load/store evidence implies real one-row source lowering

The raw words and operand bounds below are exactly the existing
RawProgramDecode fields. Existing per-op transpile proofs execute the pinned
ProductionM2 lowering, and Base inverts that same computation for acceptance.
No arith/native/Sail assumption is introduced or moved into these conclusions.
-/

namespace ZiskFv.Compliance.RawDecodeRowLowering

open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding
open ZiskFv.Compliance.Decode (toU32)

local macro "mext_source_width" nm:ident "," f3:term "," opcode:term : command => do
  let s := nm.getId.toString
  let theoremName := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str ("transpile_" ++ s))
  `(theorem $theoremName {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    refine at_pc_of_word trace i addr rawProgram
      (ZiskFv.Completeness.Rv64imShapes.rawRType 1
        (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
        (regidx_to_fin c.rd).val $opcode) 1 rawDecode.hLine ?_
    obtain ⟨terminal, source, _, _, _, _, _, hjump, _⟩ :=
      $transpileName (regidx_to_fin c.rd).val (regidx_to_fin c.r1).val
        (regidx_to_fin c.r2).val (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
    have accepted := accepted_of_live_terminal _ terminal source
      (Or.inr (Or.inl (by rw [hjump]; decide)))
    have nonJalr : (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType 1
        (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
        (regidx_to_fin c.rd).val $opcode) &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawRType_opcode]
      all_goals decide
    exact ⟨oneOfTerminal terminal source accepted nonJalr, rfl⟩)

mext_source_width mul, 0, 0x33
mext_source_width mulh, 1, 0x33
mext_source_width mulhsu, 2, 0x33
mext_source_width mulhu, 3, 0x33
mext_source_width div, 4, 0x33
mext_source_width rem, 6, 0x33
mext_source_width divw, 4, 0x3b
mext_source_width remw, 6, 0x3b
mext_source_width divu, 5, 0x33
mext_source_width divuw, 5, 0x3b
mext_source_width remu, 7, 0x33
mext_source_width remuw, 7, 0x3b

local macro "load_source_width" nm:ident "," input:term "," f3:term : command => do
  let s := nm.getId.toString
  let theoremName := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str ("transpile_" ++ s))
  `(theorem $theoremName {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    refine at_pc_of_word trace i addr rawProgram
      (ZiskFv.Completeness.Rv64imShapes.rawIType ($input c).imm.toNat
        ($input c).r1.toNat $f3 ($input c).rd.toNat 0x03)
      1 rawDecode.hLine ?_
    obtain ⟨terminal, source, _, _, _, _, _, _, hjump, _⟩ :=
      $transpileName ($input c).rd.toNat ($input c).r1.toNat ($input c).imm.toNat
        ($input c).rd.isLt ($input c).r1.isLt
    have accepted := accepted_of_live_terminal _ terminal source
      (Or.inr (Or.inl (by rw [hjump]; decide)))
    have nonJalr : (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType
        ($input c).imm.toNat ($input c).r1.toNat $f3 ($input c).rd.toNat 0x03)
        &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode]
      all_goals decide
    exact ⟨oneOfTerminal terminal source accepted nonJalr, rfl⟩)

load_source_width ld, Claim_ld.ld_input, 3
load_source_width lbu, Claim_lbu.lbu_input, 4
load_source_width lhu, Claim_lhu.lhu_input, 5
load_source_width lwu, Claim_lwu.lwu_input, 6
load_source_width lb, Claim_lb.lb_input, 0
load_source_width lh, Claim_lh.lh_input, 1
load_source_width lw, Claim_lw.lw_input, 2

local macro "store_source_width" nm:ident "," input:term "," f3:term : command => do
  let s := nm.getId.toString
  let theoremName := Lean.mkIdent (Lean.Name.mkSimple ("sourceWidth_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str ("RawProgramDecode_" ++ s))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str ("transpile_" ++ s))
  `(theorem $theoremName {n rawLength : Nat} (trace : AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (rawDecode : $rawName trace i c addr rawProgram) :
      SourceWidthAt trace i addr rawProgram 1 := by
    refine at_pc_of_word trace i addr rawProgram
      (ZiskFv.Completeness.Rv64imShapes.rawSType ($input c).imm.toNat
        ($input c).r2.toNat ($input c).r1.toNat $f3)
      1 rawDecode.hLine ?_
    obtain ⟨terminal, source, _, _, _, _, _, _, hjump, _⟩ :=
      $transpileName ($input c).r1.toNat ($input c).r2.toNat ($input c).imm.toNat
        ($input c).r1.isLt ($input c).r2.isLt
    have accepted := accepted_of_live_terminal _ terminal source
      (Or.inr (Or.inl (by rw [hjump]; decide)))
    have nonJalr : (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType
        ($input c).imm.toNat ($input c).r2.toNat ($input c).r1.toNat $f3)
        &&& 127#u32) ≠ 103#u32 := by
      rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawSType_opcode]
      all_goals decide
    exact ⟨oneOfTerminal terminal source accepted nonJalr, rfl⟩)

store_source_width sb, Claim_sb.sb_input, 0
store_source_width sh, Claim_sh.sh_input, 1
store_source_width sw, Claim_sw.sw_input, 2
store_source_width sd, Claim_sd.sd_input, 3

end ZiskFv.Compliance.RawDecodeRowLowering
