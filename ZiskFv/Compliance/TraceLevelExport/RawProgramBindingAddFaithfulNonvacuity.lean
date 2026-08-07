import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingNonvacuity
import ZiskFv.Compliance.AddFaithfulPaddedWitness

/-!
# Raw-program binding for the faithful two-row ADD witness (#320 non-vacuity)

Both committed ROM rows of `AddFaithfulPaddedWitness.addFaithfulAcceptedTrace` are the SAME
faithful production lowering of `add x1,x1,x1` (`0x001080b3`): row 0 at line 0, row 1 at line 4.
`romMessageOfRaw`'s only dependence on its `line` argument is the `.line` field itself
(`romMessageOfRaw_line_eq`), so row 1's fact is derived from the already-proven row-0 fact
(`RawProgramBindingNonvacuity.singleAddProgramBinding`) rather than re-run through the extraction
pipeline. This gives a genuine `ProgramRowsBinding` witness with `rawLength = 2`, closing the
non-vacuity gap for `ZiskFv.Compliance.root_soundness` (eth-act/zisk-fv#320).
-/

open Goldilocks

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Compliance.AddFaithfulPaddedWitness
open ZiskFv.Compliance.SingleAddWitness
open Aeneas Aeneas.Std Result zisk_core

/-- `romMessageOfRaw`'s only dependence on its `line` argument is the `.line` field itself: the
    underlying Aeneas lowering/serialization pipeline runs entirely off `raw`, in both the
    successful-lowering and default-zero branches. -/
theorem romMessageOfRaw_line_eq (line line' : FGL) (raw : BitVec 32) :
    romMessageOfRaw line raw = { romMessageOfRaw line' raw with line := line } := by
  unfold romMessageOfRaw
  cases aeneas_extract.extract_transpile_rv64im_raw (ZiskFv.Compliance.Decode.toU32 raw) <;> rfl

/-- Row 0's committed ROM entry is the faithful ADD lowering, re-derived (not re-proved) from
    `singleAddProgramBinding`. -/
theorem addX1ProgramRow_eq_romMessageOfRaw :
    RegisterMemBusBalance.addX1ProgramRow = romMessageOfRaw 0 0x001080b3 := by
  have h := singleAddProgramBinding.2 (⟨0, by decide⟩ : Fin singleAddAcceptedTrace.programLength)
  simpa [singleAddAcceptedTrace, RegisterMemBusBalance.addX1Program, singleAddAddr,
    singleAddRawProgram] using h

/-- Row 1's committed ROM entry is the SAME faithful ADD lowering, at line 4. -/
theorem addFaithfulRow1ProgramRow_eq_romMessageOfRaw :
    addFaithfulRow1ProgramRow = romMessageOfRaw 4 0x001080b3 := by
  unfold addFaithfulRow1ProgramRow
  rw [addX1ProgramRow_eq_romMessageOfRaw]
  exact (romMessageOfRaw_line_eq 4 0 0x001080b3).symm

/-- The faithful ADD word never expands to two physical rows (non-JALR): every use of
    `romMessagesOfRaw` on it has no second row, at every committed line. -/
theorem addFaithfulRomMessagesOfRaw_snd (line : FGL) :
    (romMessagesOfRaw line (0x001080b3 : BitVec 32)).2 = none := by
  have hraw : (Completeness.Rv64imShapes.rawRType 0 1 1 0 1 0x33 : BitVec 32) = 0x001080b3 := by
    decide
  obtain ⟨ext, hext, _⟩ := transpile_add 1 1 1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [hraw] at hext
  have hnon : (ZiskFv.Compliance.Decode.toU32 (0x001080b3 : BitVec 32) &&& 127#u32) ≠ 103#u32 := by
    decide
  unfold romMessagesOfRaw
  rw [aeneas_extract.extract_transpile_rv64im_rows_raw, hext]
  simp only [lift, Bind.bind, bind_ok, hnon]
  rfl

theorem addFaithfulRomMessagesOfRaw_fst (line : FGL) :
    (romMessagesOfRaw line (0x001080b3 : BitVec 32)).1 = romMessageOfRaw line 0x001080b3 := by
  have hraw : (Completeness.Rv64imShapes.rawRType 0 1 1 0 1 0x33 : BitVec 32) = 0x001080b3 := by
    decide
  obtain ⟨ext, hext, _⟩ := transpile_add 1 1 1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [hraw] at hext
  have hnon : (ZiskFv.Compliance.Decode.toU32 (0x001080b3 : BitVec 32) &&& 127#u32) ≠ 103#u32 := by
    decide
  exact romMessagesOfRaw_fst_of_non_jalr line 0x001080b3 ext hext hnon

/-! ## The raw program layout: two architectural raw words, both `add x1,x1,x1` -/

/-- Identity embedding of architectural raw-word indices into physical ROM rows: both raw words
    have exactly one physical row each (ADD is non-JALR), at the SAME physical index. -/
def addFaithfulStart : Fin 2 → Fin addFaithfulAcceptedTrace.programLength := id

def addFaithfulAddr : Fin 2 → FGL
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 4

def addFaithfulRawProgram : Fin 2 → BitVec 32 := fun _ => 0x001080b3

theorem addFaithfulProgramRowsBinding :
    ProgramRowsBinding addFaithfulAcceptedTrace addFaithfulStart addFaithfulAddr
      addFaithfulRawProgram := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' h
    fin_cases k <;> fin_cases k' <;> revert h <;> decide
  · intro k
    fin_cases k <;> decide
  · intro k
    fin_cases k <;> decide
  · intro k k' h
    fin_cases k <;> fin_cases k' <;>
      simp only [addFaithfulAddr, addFaithfulRawProgram, addFaithfulRomMessagesOfRaw_snd] <;>
      revert h <;> decide
  · intro k
    fin_cases k
    · simp only [addFaithfulStart, id_eq, addFaithfulAddr, addFaithfulRawProgram]
      refine ⟨?_, ?_⟩
      · rw [addFaithfulRomMessagesOfRaw_fst]
        exact addX1ProgramRow_eq_romMessageOfRaw
      · rw [addFaithfulRomMessagesOfRaw_snd]
        trivial
    · simp only [addFaithfulStart, id_eq, addFaithfulAddr, addFaithfulRawProgram]
      refine ⟨?_, ?_⟩
      · rw [addFaithfulRomMessagesOfRaw_fst]
        exact addFaithfulRow1ProgramRow_eq_romMessageOfRaw
      · rw [addFaithfulRomMessagesOfRaw_snd]
        trivial
  · intro j
    fin_cases j
    · exact ⟨⟨0, by decide⟩, Or.inl rfl⟩
    · exact ⟨⟨1, by decide⟩, Or.inl rfl⟩

#print axioms addFaithfulProgramRowsBinding

end ZiskFv.Compliance.RawProgramBinding
