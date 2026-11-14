import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLowering

/-!
# Serialized physical source-span binding prerequisites

All row indices below range over the actual Main table, not architectural
step numbers. Accepted Main/ROM membership, the existing ProgramRowsBinding
partition/alignment/no-wrap facts, and successful production lowering imply
these equalities. No successful-parser or independent placement oracle is
added. The statements do not require the old StepRowsAligned restriction.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.AirsClean.Main (romMessage romFlags packFlags)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

/-- The actual Main row at a selected architectural address is the successful
source lowering's first serialized row, including for an expanded instruction. -/
theorem main_first_rom {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    romMessage (mainTableRowAtOrZero trace.program trace.mainTable row.val) =
      romRowOf (addr k) lowering.rows.first_row := by
  obtain ⟨j, hj⟩ := RomDecodeBinding.mainRomMessage_at_eq_program trace row
  have line : (trace.program j).line = addr k := by
    rw [← hj]
    exact atPc
  exact hj.trans ((primary_row_at_architectural_line binding j k line).2.trans
    (lowering.serialized_first (addr k)))

/-- The corresponding packed flag equality is consumed by accepted Boolean
selector inversion, rather than assumed as a new per-row source pin. -/
theorem main_first_flags {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val) =
      packFlags (romFlagBitsOfExtract lowering.rows.first_row) := by
  exact congrArg ZiskRomMessage.flags
    (main_first_rom trace start addr rawProgram binding k lowering row atPc)

/-- At the auxiliary address, the existing source partition cannot choose a
primary word (all primary addresses are four-byte aligned), nor a different
word's auxiliary row (strict source-address order gives uniqueness). -/
theorem program_at_auxiliary_line {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2) (j : Fin trace.programLength)
    (line : (trace.program j).line = addr k + 1) :
    trace.program j = romRowOf (addr k + 1) lowering.rows.last_row := by
  have binding' := binding
  obtain ⟨ordered, aligned, noWrap, _, _, _⟩ := binding
  obtain ⟨other, ⟨_, hrow⟩ | ⟨serialized, hsecond, _, hrow⟩⟩ :=
    physical_row_of_programRowsBinding binding' j
  · have mismatch : addr other = addr k + 1 := by
      have h := congrArg ZiskRomMessage.line hrow
      rw [romMessagesOfRaw_first_line] at h
      exact h.symm.trans line
    have values := congrArg Fin.val mismatch
    simp [Fin.add_def, Nat.mod_eq_of_lt (noWrap k)] at values
    have hk := aligned k
    have ho := aligned other
    omega
  · have serializedLine := romMessagesOfRaw_second_line hsecond
    have addresses : addr other + 1 = addr k + 1 := by
      rw [← serializedLine, ← line, hrow]
    have addressEq : addr other = addr k := add_right_cancel addresses
    have same : other = k := by
      by_contra different
      rcases lt_or_gt_of_ne different with hlt | hgt
      · have h := (ordered other k hlt).2
        rw [addressEq] at h
        omega
      · have h := (ordered k other hgt).2
        rw [addressEq] at h
        omega
    subst other
    rw [lowering.serialized_second, if_pos widthTwo] at hsecond
    exact hrow.trans (Option.some.inj hsecond).symm

/-- Once the actual PC transition reaches the source auxiliary address, the
accepted Main/ROM lookup fixes the entire terminal row, not just its opcode. -/
theorem main_terminal_rom_of_auxiliary_pc {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2) (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k + 1) :
    romMessage (mainTableRowAtOrZero trace.program trace.mainTable row.val) =
      romRowOf (addr k + 1) lowering.rows.last_row := by
  obtain ⟨j, hj⟩ := RomDecodeBinding.mainRomMessage_at_eq_program trace row
  have line : (trace.program j).line = addr k + 1 := by
    rw [← hj]
    exact atPc
  exact hj.trans (program_at_auxiliary_line trace start addr rawProgram binding
    k lowering widthTwo j line)

/-- Actual source addresses are injective by the existing strict ordering,
not by a new program-uniqueness premise. -/
theorem source_address_injective {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram) :
    Function.Injective addr := by
  intro a b equal
  by_contra different
  rcases lt_or_gt_of_ne different with hlt | hgt
  · have h := (binding.1 a b hlt).2
    rw [equal] at h
    omega
  · have h := (binding.1 b a hgt).2
    rw [equal] at h
    omega

/-- Existing raw decode identifies the width of ANY successful source
certificate selected at that same actual PC. No producer-placement oracle or
independent width promise is supplied. -/
theorem source_width_at_selected_pc {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i step start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (atPc : (mainOfTable trace.program trace.mainTable).pc i.val = addr k) :
    lowering.width = stepProducerRow i step (rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i step start addr rawProgram
        binding rawDecode)) + 1 - i.val := by
  obtain ⟨chosen, address, actual, width⟩ :=
    RawDecodeRowLowering.sourceWidth_of_rawProgramDecode trace i step start addr
      rawProgram binding rawDecode
  have same : chosen = k := source_address_injective trace start addr rawProgram
    binding (address.trans atPc)
  subst chosen
  have rows : actual.rows = lowering.rows :=
    Result.ok.inj (actual.source.symm.trans lowering.source)
  have widths : actual.width = lowering.width :=
    congrArg (fun r : aeneas_extract.Rv64imTranspileRowsExtract => r.row_count.val) rows
  exact widths.symm.trans width

end ZiskFv.Compliance.SerializedExecutionRows
