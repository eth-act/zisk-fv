import ZiskFv.Compliance.TraceLevelExport.CanonicalExecutionRows
import ZiskFv.Compliance.TraceLevelExport.RawProgramDecode

/-!
# Executed-word source-width comparison prerequisites

These helpers consume the existing accepted Main/ROM lookup and the existing
raw-decode line evidence. They add no root premise or successful-parser binder.
Acceptance is recovered from the actual ProductionM2 terminal computation:
`core/src/aeneas_extract.rs:361–375` at ZisK9ca88b5. Its rejected arm emits
an all-zero default row; the live pin below is supplied by existing per-op
source proofs, never by the public root caller.
-/

namespace ZiskFv.Compliance.RawDecodeRowLowering

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

/-- A derived executed raw-word choice and its actual source width. -/
def SourceWidthAt {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) (width : Nat) : Prop :=
  ∃ k : Fin rawLength, addr k = (mainOfTable trace.program trace.mainTable).pc i.val ∧
    ∃ lowering : SuccessfulRowLowering (rawProgram k), lowering.width = width

/-- No supported-domain premise is hidden in this inversion: a successful
terminal result with one of these non-default pins cannot be the rejected arm. -/
theorem accepted_of_live_terminal (raw : BitVec 32)
    (terminal : aeneas_extract.Rv64imTranspileExtract)
    (source : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal)
    (live : terminal.row.op ≠ 0#u8 ∨ terminal.row.jmp_offset1 ≠ 0#i64 ∨
      terminal.row.store_pc = true) : terminal.accepted = true := by
  unfold aeneas_extract.extract_transpile_rv64im_raw at source
  obtain ⟨decoded, _, source⟩ := bind_eq_ok_imp source
  obtain ⟨decode, _, source⟩ := bind_eq_ok_imp source
  obtain ⟨opcode, _, source⟩ := bind_eq_ok_imp source
  cases opcode with
  | none =>
      obtain ⟨zero, hzero, hop, hjump, hpc⟩ :
          ∃ zero : aeneas_extract.ZiskInstExtract,
            aeneas_extract.ZiskInstExtract.Insts.CoreDefaultDefault.default = .ok zero ∧
              zero.op = 0#u8 ∧ zero.jmp_offset1 = 0#i64 ∧ zero.store_pc = false := by
        exact ⟨_, rfl, rfl, rfl, rfl⟩
      rw [hzero] at source
      simp only [bind_ok] at source
      have heq := Result.ok.inj source
      subst terminal
      rcases live with h | h | h
      · exact False.elim (h hop)
      · exact False.elim (h hjump)
      · rw [hpc] at h
        contradiction
  | some opcode =>
      obtain ⟨input, _, source⟩ := bind_eq_ok_imp source
      obtain ⟨ctx, _, source⟩ := bind_eq_ok_imp source
      obtain ⟨inst, _, source⟩ := bind_eq_ok_imp source
      obtain ⟨row, _, source⟩ := bind_eq_ok_imp source
      exact (congrArg aeneas_extract.Rv64imTranspileExtract.accepted
        (Result.ok.inj source)).symm

/-- The source's actual non-JALR arm constructs a successful one-row result. -/
def oneOfTerminal {raw : BitVec 32}
    (terminal : aeneas_extract.Rv64imTranspileExtract)
    (source : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal)
    (accepted : terminal.accepted = true)
    (nonJalr : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32) :
    SuccessfulRowLowering raw where
  rows :=
    { accepted := terminal.accepted
      decode := terminal.decode
      row_count := 1#u32
      first_row := terminal.row
      last_row := terminal.row }
  source := by
    unfold aeneas_extract.extract_transpile_rv64im_rows_raw
    rw [source]
    simp only [bind_ok, lift, nonJalr, if_false]
  accepted := accepted

@[simp] theorem oneOfTerminal_width {raw : BitVec 32}
    (terminal : aeneas_extract.Rv64imTranspileExtract)
    (source : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal)
    (accepted : terminal.accepted = true)
    (nonJalr : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32) :
    (oneOfTerminal terminal source accepted nonJalr).width = 1 := rfl

/-- Existing conditional raw-line evidence is nonvacuous: accepted Main's ROM
lookup supplies an actual committed line at the current execution row. -/
theorem at_pc_of_word {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) (word : BitVec 32) (width : Nat)
    (line : ∀ j : Fin trace.programLength,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength, addr k = (trace.program j).line ∧ rawProgram k = word)
    (lowering : ∃ lowering : SuccessfulRowLowering word, lowering.width = width) :
    SourceWidthAt trace i addr rawProgram width := by
  obtain ⟨j, hj, _⟩ := RomDecodeBinding.mainDecodeColumns_at_eq_program trace
    ⟨i.val, trace.mainTable_index i⟩
  obtain ⟨k, haddr, hword⟩ := line j hj
  obtain ⟨lowering, hwidth⟩ := lowering
  refine ⟨k, haddr.trans hj, ?_⟩
  rw [hword]
  exact ⟨lowering, hwidth⟩

end ZiskFv.Compliance.RawDecodeRowLowering
