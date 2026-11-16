import ZiskFv.Compliance.TraceLevelExport.CanonicalSourceParser
import ZiskFv.Compliance.TraceLevelExport.CanonicalPhysicalState
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingJalrExpansionNonvacuity

/-!
# Checked parsing and actual physical state at the next source cut

The parse consumes the full source-width prefix. Its continuation PC and its
register/memory state are the existing actual-Main refinement, not new parser
oracles. Expanded JALR's internal row is retained in both physical folds and
never receives a fictitious Sail step. This does not prove runtime completion.
-/

namespace ZiskFv.Compliance.CanonicalSourceParser

open CanonicalExecutionRows RawProgramBinding SerializedExecutionRows
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

section Source

variable {m rawLength : Nat}
variable (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
variable (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
variable (trace : AcceptedZiskTrace (sourceEnd L))
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (steps : ∀ i, ZiskStep trace (physicalStart L i))
variable (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
  start addr rawProgram)
variable (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
  (physicalStart L i).val = addr (selected i))

local notation "D" => (fun i => rowDecode_of_programDecode trace (physicalStart L i)
  (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
    start addr rawProgram binding (rawDecodes i)))

include atPc

/-- The parser's derived next-source boundary has the real retired PC and the
actual physical register/memory fold. Soundness is required only for preceding
architectural instructions, exactly as in the existing physical-cut induction. -/
theorem parsed_next_source_cut
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (i j : Fin m) (next : j.val = i.val + 1)
    (sounds : ∀ k : Fin m, k.val < j.val →
      StepSound trace (mappedSailTrace L steps init)
        (physicalStart L k) (steps k) (D k)) :
    canonicalParse trace addr rawProgram m =
        some (List.ofFn (fun k => (⟨selected k, L k⟩ :
          Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd L) ∧
      (mappedSailTrace L steps init (physicalStart L j)).regs.get? Register.PC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc (physicalStart L j).val).val) ∧
      (mappedSailStates L steps init j.val (Nat.le_of_lt j.isLt)).mem =
        replayMemoryAfterBusRows init.mem
          (((actualMainMutablePhysicalSlots trace).take
            (rowPrefix (sourceWidth L) j.val)).flatten) ∧
      (∀ k : Fin 32, k ≠ 0 →
        (mappedSailStates L steps init j.val (Nat.le_of_lt j.isLt)).regs.get? (reg_of_fin k) =
          some (cast (by rw [register_type_reg_of_fin_equiv])
            (actualPhysicalRegFile trace (rowPrefix (sourceWidth L) j.val)
              (prefix_mono (sourceWidth L) (Nat.le_of_lt j.isLt)) k))) := by
  have parsed := canonicalParse_at_source_starts rawProgram selected L trace
    start addr binding (by simpa only [physicalStart_val] using atPc)
  have pc := mapped_pc_at_next_source_start rawProgram selected L trace start addr
    binding steps rawDecodes atPc init i j next (sounds i (by omega))
  have physical := canonical_physical_state_at_source_cut rawProgram selected L trace
    start addr binding steps rawDecodes atPc init regBoot j.val (Nat.le_of_lt j.isLt) sounds
  exact ⟨parsed, pc, physical⟩

end Source

/-- A nonfinal width2 source lowering is the real expanded JALR arm. The next
architectural step is at row2; its PC and memory/register prestate follow the
entire actual two-row physical fold. The remaining lowering is still consumed
by the parser, without forcing width1 or using old starts=i. -/
theorem nonfinal_expansion_parsed_physical_cut {rawLength : Nat}
    (rawProgram : Fin rawLength → BitVec 32) (selected : Fin 2 → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (steps : ∀ i, ZiskStep trace (physicalStart L i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
      start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i))
    (two : (L (0 : Fin 2)).width = 2)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (sound : StepSound trace (mappedSailTrace L steps init)
      (physicalStart L (0 : Fin 2)) (steps (0 : Fin 2))
      (rowDecode_of_programDecode trace (physicalStart L (0 : Fin 2))
        (programDecode_of_rawProgramDecode trace (physicalStart L (0 : Fin 2))
          (steps (0 : Fin 2)) start addr rawProgram binding (rawDecodes (0 : Fin 2))))) :
    sourceStart L (1 : Fin 2) = 2 ∧
      canonicalParse trace addr rawProgram 2 =
        some (List.ofFn (fun k => (⟨selected k, L k⟩ :
          Σ k, SuccessfulRowLowering (rawProgram k))), 2 + (L (1 : Fin 2)).width) ∧
      (mappedSailTrace L steps init (physicalStart L (1 : Fin 2))).regs.get? Register.PC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc (physicalStart L (1 : Fin 2)).val).val) ∧
      (mappedSailStates L steps init 1 (by decide)).mem =
        replayMemoryAfterBusRows init.mem
          (((actualMainMutablePhysicalSlots trace).take 2).flatten) ∧
      (∀ k : Fin 32, k ≠ 0 →
        (mappedSailStates L steps init 1 (by decide)).regs.get? (reg_of_fin k) =
          some (cast (by rw [register_type_reg_of_fin_equiv])
            (actualPhysicalRegFile trace (rowPrefix (sourceWidth L) 1)
              (prefix_mono (sourceWidth L) (by decide : 1 ≤ 2)) k))) := by
  obtain ⟨second, parsed⟩ := nonfinal_expansion_canonicalParse rawProgram selected L trace
    start addr binding (by simpa only [physicalStart_val] using atPc) two
  have cut := parsed_next_source_cut rawProgram selected L trace start addr binding steps
    rawDecodes atPc init regBoot (0 : Fin 2) (1 : Fin 2) rfl (by
      intro k before
      have zero : k = (0 : Fin 2) := by apply Fin.ext; change k.val = 0; omega
      subst k
      exact sound)
  have cutRow : rowPrefix (sourceWidth L) 1 = 2 := second
  refine ⟨second, parsed, cut.2.1, ?_, cut.2.2.2⟩
  have memory := cut.2.2.1
  change (mappedSailStates L steps init 1 (by decide)).mem =
    replayMemoryAfterBusRows init.mem
      (((actualMainMutablePhysicalSlots trace).take (rowPrefix (sourceWidth L) 1)).flatten)
    at memory
  simpa only [cutRow] using memory

/-! ## A real repeating source JALR, not the imm2/NOP layout-only toy.

Only the existing literal source-count proof is reused from the ROM-image
module. Its empty Accepted0 witness is NOT used. The execution below remains
conditional on an actual accepted trace, its real raw-decode providers, boot
registers and the first actual Sail step; no Accepted4 existence is claimed.
-/

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction

private theorem source_rows_accepted_of_two {raw : BitVec 32}
    {rows : aeneas_extract.Rv64imTranspileRowsExtract}
    (source : aeneas_extract.extract_transpile_rv64im_rows_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok rows)
    (two : rows.row_count = 2#u32) : rows.accepted = true := by
  unfold aeneas_extract.extract_transpile_rv64im_rows_raw at source
  obtain ⟨terminal, _, source⟩ := bind_eq_ok_imp source
  simp only [lift, Bind.bind, bind_ok] at source
  split at source
  · split at source
    · obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
      split at source
      · obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
        obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
        obtain ⟨_, _, source⟩ := bind_eq_ok_imp source
        rw [Result.ok.injEq] at source
        subst rows
        rfl
      · rw [Result.ok.injEq] at source
        subst rows
        rfl
    · rw [Result.ok.injEq] at source
      subst rows
      exact False.elim ((by decide : (1#u32 : Aeneas.Std.U32) ≠ 2#u32) two)
  · rw [Result.ok.injEq] at source
    subst rows
    exact False.elim ((by decide : (1#u32 : Aeneas.Std.U32) ≠ 2#u32) two)

/-- Real `JALR x1,x2,1`: x2 is not written and a zero x2 returns to PC0.
Both executed occurrences have the source's two-row ADD/AND expansion. -/
def repeatJalrRawProgram : Fin 1 → BitVec 32 := fun _ => jalrExpansionRaw

def repeatJalrSelected : Fin 2 → Fin 1 := fun _ => 0

noncomputable def repeatJalrLowering : SuccessfulRowLowering jalrExpansionRaw where
  rows := jalrExpansionRows
  source := jalrExpansionRows_spec.1
  accepted := source_rows_accepted_of_two jalrExpansionRows_spec.1 jalrExpansionRows_spec.2

noncomputable def repeatJalrLowerings :
    ∀ i : Fin 2, SuccessfulRowLowering (repeatJalrRawProgram (repeatJalrSelected i)) :=
  fun _ => repeatJalrLowering

theorem repeatJalrLowerings_width (i : Fin 2) : (repeatJalrLowerings i).width = 2 := by
  change jalrExpansionRows.row_count.val = 2
  rw [jalrExpansionRows_spec.2]
  rfl

theorem repeatJalr_sourceEnd : sourceEnd repeatJalrLowerings = 4 := by
  have next := prefix_succ (sourceWidth repeatJalrLowerings) (0 : Fin 2)
  have second : sourceStart repeatJalrLowerings (1 : Fin 2) = 2 := by
    simpa only [sourceStart, prefix_zero, sourceWidth, repeatJalrLowerings_width, zero_add]
      using next
  have last := prefix_succ (sourceWidth repeatJalrLowerings) (1 : Fin 2)
  change sourceEnd repeatJalrLowerings =
    sourceStart repeatJalrLowerings (1 : Fin 2) + (repeatJalrLowerings (1 : Fin 2)).width at last
  simpa only [second, repeatJalrLowerings_width] using last

/-- An actual two-occurrence JALR source-prefix example. PC selection is
DERIVED from the real Fin1 raw-decode family, not an added alignment/atPc
certificate. The first actual Sail step remains an explicit condition;
neither bare Accepted nor the old empty-ROM witness is claimed to prove it. -/
theorem repeated_jalr_actual_prefix_example
    (trace : AcceptedZiskTrace (sourceEnd repeatJalrLowerings))
    (start : Fin 1 → Fin trace.programLength)
    (binding : ProgramRowsBinding trace start (fun _ => 0) repeatJalrRawProgram)
    (claims : ∀ i : Fin 2, Claim_jalr trace (physicalStart repeatJalrLowerings i))
    (rawDecodes : ∀ i : Fin 2,
      RawProgramDecode trace (physicalStart repeatJalrLowerings i) (.jalr (claims i))
        start (fun _ => 0) repeatJalrRawProgram)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (firstSound : StepSound trace (fun _ => init) (physicalStart repeatJalrLowerings (0 : Fin 2))
      (.jalr (claims (0 : Fin 2)))
      (rowDecode_of_programDecode trace (physicalStart repeatJalrLowerings (0 : Fin 2))
        (programDecode_of_rawProgramDecode trace (physicalStart repeatJalrLowerings (0 : Fin 2))
          (.jalr (claims (0 : Fin 2))) start (fun _ => 0) repeatJalrRawProgram binding
          (rawDecodes (0 : Fin 2))))) :
    sourceEnd repeatJalrLowerings = 4 ∧
      sourceStart repeatJalrLowerings (1 : Fin 2) = 2 ∧
      canonicalParse trace (fun _ => 0) repeatJalrRawProgram 2 =
        some (List.ofFn (fun i => (⟨repeatJalrSelected i, repeatJalrLowerings i⟩ :
          Σ k, SuccessfulRowLowering (repeatJalrRawProgram k))), 4) ∧
      (mappedSailStates repeatJalrLowerings (fun i => .jalr (claims i)) init 1
        (by decide)).regs.get? Register.PC = some (register_type_pc_equiv ▸ (0 : BitVec 64)) ∧
      (mappedSailStates repeatJalrLowerings (fun i => .jalr (claims i)) init 1
        (by decide)).mem =
        replayMemoryAfterBusRows init.mem
          (((actualMainMutablePhysicalSlots trace).take 2).flatten) ∧
      (∀ k : Fin 32, k ≠ 0 →
        (mappedSailStates repeatJalrLowerings (fun i => .jalr (claims i)) init 1
          (by decide)).regs.get? (reg_of_fin k) =
          some (cast (by rw [register_type_reg_of_fin_equiv])
            (actualPhysicalRegFile trace 2 (by rw [repeatJalr_sourceEnd]; decide) k))) := by
  let steps := fun i => ZiskStep.jalr (claims i)
  have atPc : ∀ i : Fin 2, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart repeatJalrLowerings i).val = (0 : FGL) := by
    intro i
    obtain ⟨_, pc, _, _⟩ := RawDecodeRowLowering.sourceWidth_of_rawProgramDecode
      trace (physicalStart repeatJalrLowerings i) (steps i) start (fun _ => 0)
      repeatJalrRawProgram binding (rawDecodes i)
    exact pc.symm
  have initial : mappedSailTrace repeatJalrLowerings steps init
      (physicalStart repeatJalrLowerings (0 : Fin 2)) = init := by
    rw [state_at_start]
    rfl
  have sound : StepSound trace (mappedSailTrace repeatJalrLowerings steps init)
      (physicalStart repeatJalrLowerings (0 : Fin 2)) (steps (0 : Fin 2))
      (rowDecode_of_programDecode trace (physicalStart repeatJalrLowerings (0 : Fin 2))
        (programDecode_of_rawProgramDecode trace (physicalStart repeatJalrLowerings (0 : Fin 2))
          (steps (0 : Fin 2)) start (fun _ => 0) repeatJalrRawProgram binding
          (rawDecodes (0 : Fin 2)))) := by
    apply (stepSound_iff _ _ _).mpr
    rw [initial]
    exact (stepSound_iff _ _ _).mp firstSound
  have actual := nonfinal_expansion_parsed_physical_cut repeatJalrRawProgram repeatJalrSelected
    repeatJalrLowerings trace start (fun _ => 0) binding steps rawDecodes atPc
    (repeatJalrLowerings_width 0) init regBoot sound
  have cutRow : rowPrefix (sourceWidth repeatJalrLowerings) 1 = 2 := actual.1
  refine ⟨repeatJalr_sourceEnd, actual.1, ?_, ?_, actual.2.2.2.1, ?_⟩
  · simpa only [repeatJalrLowerings_width] using actual.2.1
  · have pc := actual.2.2.1
    rw [state_at_start] at pc
    change (mappedSailStates repeatJalrLowerings steps init 1 (by decide)).regs.get? Register.PC =
      some (register_type_pc_equiv ▸ BitVec.ofNat 64
        ((mainOfTable trace.program trace.mainTable).pc
          (physicalStart repeatJalrLowerings (1 : Fin 2)).val).val) at pc
    simpa only [atPc] using pc
  · simpa only [cutRow] using actual.2.2.2.2

end ZiskFv.Compliance.CanonicalSourceParser
