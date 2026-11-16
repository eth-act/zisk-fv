import ZiskFv.Compliance.TraceLevelExport.SerializedSpanBase

/-!
# Expanded source bounds are derived, not caller promises

The production rows computation only expands raw opcode103. Its real core
decoder uses decode_i, whose register fields are masked to five bits. These
facts recover the bounds required by the existing JALR first-row pin theorem.
No extra well-formed-word validator or parser-success domain is introduced.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction

private theorem terminal_decode_from_core (raw : BitVec 32)
    (decoded : aeneas_extract.rv64im_decode.DecodedRv64im)
    (core : aeneas_extract.rv64im_decode.decode_32_core (Decode.toU32 raw) = .ok decoded)
    (terminal : aeneas_extract.Rv64imTranspileExtract)
    (source : aeneas_extract.extract_transpile_rv64im_raw (Decode.toU32 raw) = .ok terminal) :
    ∃ extracted : aeneas_extract.Rv64imDecodeExtract,
      aeneas_extract.decode_extract_from_decoded decoded = .ok extracted ∧
        terminal.decode = extracted := by
  unfold aeneas_extract.extract_transpile_rv64im_raw at source
  rw [core] at source
  simp only [Bind.bind, bind_ok] at source
  obtain ⟨extracted, hextracted, source⟩ := bind_eq_ok_imp source
  obtain ⟨opcode, _, source⟩ := bind_eq_ok_imp source
  cases opcode with
  | none =>
      obtain ⟨zero, _, source⟩ := bind_eq_ok_imp source
      exact ⟨extracted, hextracted,
        (congrArg aeneas_extract.Rv64imTranspileExtract.decode (Result.ok.inj source)).symm⟩
  | some opcode =>
      obtain ⟨input, _, source⟩ := bind_eq_ok_imp source
      obtain ⟨ctx, _, source⟩ := bind_eq_ok_imp source
      obtain ⟨inst, _, source⟩ := bind_eq_ok_imp source
      obtain ⟨row, _, source⟩ := bind_eq_ok_imp source
      exact ⟨extracted, hextracted,
        (congrArg aeneas_extract.Rv64imTranspileExtract.decode (Result.ok.inj source)).symm⟩

/-- Bounds needed by the production expanded-row theorem follow from the
actual successful rows computation and actual opcode103 decoder. -/
theorem expanded_source_register_bounds {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (widthTwo : lowering.width = 2) :
    lowering.rows.decode.rd.val < 32 ∧ lowering.rows.decode.rs1.val < 32 := by
  obtain ⟨terminal, hterminal, _, hdecode, _, hcases⟩ := lowering.source_cases
  have tag : (Decode.toU32 raw &&& 127#u32) = 103#u32 := by
    rcases hcases with ⟨hcount, _⟩ | ⟨_, htag, _⟩
    · have hone : lowering.width = 1 := congrArg UScalar.val hcount
      omega
    · exact htag
  have core : aeneas_extract.rv64im_decode.decode_32_core (Decode.toU32 raw) =
      aeneas_extract.rv64im_decode.decode_i (Decode.toU32 raw)
        aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, Bind.bind, bind_ok, tag]
    rfl
  obtain ⟨decoded, hdecoded, _, hrd, hrs1, _⟩ := decode_i_bounds (Decode.toU32 raw)
    aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false
  obtain ⟨extracted, hextracted, hterminalDecode⟩ := terminal_decode_from_core raw decoded
    (core.trans hdecoded) terminal hterminal
  unfold aeneas_extract.decode_extract_from_decoded at hextracted
  obtain ⟨supported, _, hextracted⟩ := bind_eq_ok_imp hextracted
  obtain ⟨opcode, _, hextracted⟩ := bind_eq_ok_imp hextracted
  obtain ⟨format, _, hextracted⟩ := bind_eq_ok_imp hextracted
  have fields := Result.ok.inj hextracted
  have rd := congrArg aeneas_extract.Rv64imDecodeExtract.rd fields
  have rs1 := congrArg aeneas_extract.Rv64imDecodeExtract.rs1 fields
  rw [hdecode, hterminalDecode, ← rd, ← rs1]
  exact ⟨hrd, hrs1⟩

end ZiskFv.Compliance.SerializedExecutionRows
