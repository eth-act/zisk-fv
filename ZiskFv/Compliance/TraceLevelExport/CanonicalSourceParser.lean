import ZiskFv.Compliance.TraceLevelExport.SerializedExecutionRows

/-!
# Checked source parsing of the physical RV prefix

The entry point starts at row0. Each accepted production result determines the
next row; neither an independent row map nor a default width is accepted.
Failed/rejected extraction, a missing architectural PC, and insufficient Main
room return none. Old decode/placement evidence proves success as a conclusion.
This is RV-prefix parsing, NOT full runtime-history or final-source completion.
-/

namespace ZiskFv.Compliance.CanonicalSourceParser

open CanonicalExecutionRows RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

private theorem addr_injective {q rawLength : Nat} {trace : AcceptedZiskTrace q}
    {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    (binding : ProgramRowsBinding trace start addr rawProgram) : Function.Injective addr := by
  intro a b same
  apply Fin.ext
  have values := congrArg Fin.val same
  rcases lt_trichotomy a.val b.val with h | h | h
  · have ordered := (binding.1 a b h).2
    omega
  · exact h
  · have ordered := (binding.1 b a h).2
    omega

private theorem find_at_pc {q rawLength : Nat} {trace : AcceptedZiskTrace q}
    {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    (binding : ProgramRowsBinding trace start addr rawProgram) (row : Nat)
    (k : Fin rawLength) (atPc : (mainOfTable trace.program trace.mainTable).pc row = addr k) :
    (List.finRange rawLength).find?
      (fun j => decide (addr j = (mainOfTable trace.program trace.mainTable).pc row)) = some k := by
  let p := fun j => decide (addr j = (mainOfTable trace.program trace.mainTable).pc row)
  have found : ((List.finRange rawLength).find? p).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_finRange k, by simp [p, atPc]⟩
  cases result : (List.finRange rawLength).find? p with
  | none => simp [result] at found
  | some j =>
      have selected := List.find?_some result
      have same : j = k := addr_injective binding (by simpa [p, atPc] using selected)
      simpa only [same] using result

/-- Only the private recursion has a cursor. The checked entry point below
always starts at0 and advances by the actual successful source width. -/
private noncomputable def parseFrom {q rawLength : Nat} (trace : AcceptedZiskTrace q)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) :
    Nat → Nat → Option (List (Σ k, SuccessfulRowLowering (rawProgram k)) × Nat)
  | 0, row => some ([], row)
  | count + 1, row =>
      if row < trace.mainTable.table.length then
        match (List.finRange rawLength).find?
            (fun k => decide (addr k = (mainOfTable trace.program trace.mainTable).pc row)) with
        | none => none
        | some k =>
            match SuccessfulRowLowering.check (rawProgram k) with
            | none => none
            | some lowering =>
                if row + lowering.width ≤ trace.mainTable.table.length then
                  match parseFrom trace addr rawProgram count (row + lowering.width) with
                  | none => none
                  | some (rest, finish) => some (⟨k, lowering⟩ :: rest, finish)
                else none
      else none

/-- A checked canonical parse. Every token contains its actual source equation;
widths and the consumed endpoint come from those results, not architectural count. -/
noncomputable def canonicalParse {q rawLength : Nat} (trace : AcceptedZiskTrace q)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (architecturalCount : Nat) :
    Option (List (Σ k, SuccessfulRowLowering (rawProgram k)) × Nat) :=
  parseFrom trace addr rawProgram architecturalCount 0

private theorem parseFrom_complete {m q rawLength : Nat} (trace : AcceptedZiskTrace q)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (selected : Fin m → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (room : sourceEnd L ≤ trace.mainTable.table.length)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (sourceStart L i) = addr (selected i))
    (count cut : Nat) (length : cut + count = m) :
    parseFrom trace addr rawProgram count (rowPrefix (sourceWidth L) cut) =
      some ((List.ofFn (fun i => (⟨selected i, L i⟩ :
        Σ k, SuccessfulRowLowering (rawProgram k)))).drop cut, sourceEnd L) := by
  induction count generalizing cut with
  | zero =>
      have last : cut = m := by omega
      subst cut
      simp [parseFrom, sourceEnd]
  | succ count ih =>
      have cutBound : cut < m := by omega
      let i : Fin m := ⟨cut, cutBound⟩
      have positive := (L i).width_pos
      have next := prefix_succ (sourceWidth L) i
      change rowPrefix (sourceWidth L) (cut + 1) =
        rowPrefix (sourceWidth L) cut + (L i).width at next
      have prefixBound := prefix_mono (sourceWidth L) (show cut + 1 ≤ m by omega)
      change rowPrefix (sourceWidth L) (cut + 1) ≤ sourceEnd L at prefixBound
      have rowRoom : rowPrefix (sourceWidth L) cut < trace.mainTable.table.length := by omega
      have endRoom : rowPrefix (sourceWidth L) cut + (L i).width ≤
          trace.mainTable.table.length := by omega
      have lookup := find_at_pc binding (rowPrefix (sourceWidth L) cut) (selected i) (atPc i)
      have rest := ih (cut + 1) (by omega)
      have tokens : (List.ofFn (fun i => (⟨selected i, L i⟩ :
          Σ k, SuccessfulRowLowering (rawProgram k)))).drop cut =
          ⟨selected i, L i⟩ :: (List.ofFn (fun i => (⟨selected i, L i⟩ :
            Σ k, SuccessfulRowLowering (rawProgram k)))).drop (cut + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using cutBound)]
        simp only [List.getElem_ofFn]
        rfl
      simp only [parseFrom, if_pos rowRoom, lookup,
        SuccessfulRowLowering.check_complete (L i), if_pos endRoom]
      rw [← next, rest, tokens]

/-- Totality on the existing source-selected physical-prefix domain. In
particular NO StepRowsAligned/starts=i restriction is imposed here: an expanded
nonfinal JALR advances the cursor by2, and the next word is read at that row. -/
theorem canonicalParse_complete {m q rawLength : Nat} (trace : AcceptedZiskTrace q)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (selected : Fin m → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (room : sourceEnd L ≤ trace.mainTable.table.length)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (sourceStart L i) = addr (selected i)) :
    canonicalParse trace addr rawProgram m =
      some (List.ofFn (fun i => (⟨selected i, L i⟩ :
        Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd L) := by
  simpa [canonicalParse] using
    parseFrom_complete trace start addr rawProgram binding selected L room atPc m 0 (by omega)

/-- Old supported callers obtain parsing success without any added success,
room, or placement binder. The full old producer endpoint, including a final
width2 instruction, is retained; it is not replaced by n. -/
theorem old_canonicalParse_total {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (steps : ∀ i, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (aligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i)))) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        canonicalParse trace addr rawProgram n =
          some (List.ofFn (fun i => (⟨selected i, L i⟩ :
            Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd L) ∧
        (∀ i, sourceStart L i = i.val) ∧
        (∀ last : Fin n, last.val + 1 = n → sourceEnd L =
          stepProducerRow last (steps last) (rowDecode_of_programDecode trace last
            (programDecode_of_rawProgramDecode trace last (steps last) start addr
              rawProgram binding (rawDecodes last))) + 1) := by
  obtain ⟨selected, L, widths, starts, ends⟩ :=
    RawDecodeRowLowering.old_raw_source_widths_and_placement trace steps start addr rawProgram
      binding rawDecodes aligned
  have room : sourceEnd L ≤ trace.mainTable.table.length := by
    by_cases nonempty : 0 < n
    · let last : Fin n := ⟨n - 1, by omega⟩
      rw [ends last (by dsimp [last]; omega)]
      exact Nat.le_of_lt (ExecutionSpanLegacy.producer_has_successor last (steps last)
        (rowDecode_of_programDecode trace last (programDecode_of_rawProgramDecode trace last
          (steps last) start addr rawProgram binding (rawDecodes last))))
    · have empty : n = 0 := by omega
      subst n
      simp [sourceEnd, rowPrefix]
  refine ⟨selected, L, canonicalParse_complete trace start addr rawProgram binding selected L
    room ?_, starts, ends⟩
  intro i
  rw [starts i]
  exact (widths i).1.symm

/-- The existing accepted physical-prefix bound supplies all parser room.
No successful-parse or height promise is added to the mapped source domain. -/
theorem canonicalParse_at_source_starts {m rawLength : Nat}
    (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (sourceStart L i) = addr (selected i)) :
    canonicalParse trace addr rawProgram m =
      some (List.ofFn (fun i => (⟨selected i, L i⟩ :
        Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd L) := by
  have room : sourceEnd L ≤ trace.mainTable.table.length := by
    by_cases positive : 0 < sourceEnd L
    · have index := trace.mainTable_index ⟨sourceEnd L - 1, by
        change sourceEnd L - 1 < sourceEnd L
        omega⟩
      change sourceEnd L - 1 < trace.mainTable.table.length at index
      omega
    · omega
  exact canonicalParse_complete trace start addr rawProgram binding selected L room atPc

/-- The genuinely nonfinal expanded case: the second architectural word is
read at physical row2 and the entire second lowering is consumed. Its width
is not forced to1, and no auxiliary row is made into an architectural step. -/
theorem nonfinal_expansion_canonicalParse {rawLength : Nat}
    (rawProgram : Fin rawLength → BitVec 32) (selected : Fin 2 → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (sourceStart L i) = addr (selected i))
    (two : (L (0 : Fin 2)).width = 2) :
    sourceStart L (1 : Fin 2) = 2 ∧
      canonicalParse trace addr rawProgram 2 =
        some (List.ofFn (fun i => (⟨selected i, L i⟩ :
          Σ k, SuccessfulRowLowering (rawProgram k))), 2 + (L (1 : Fin 2)).width) := by
  have next := prefix_succ (sourceWidth L) (0 : Fin 2)
  have second : sourceStart L (1 : Fin 2) = 2 := by
    simpa only [sourceStart, prefix_zero, sourceWidth, two, zero_add] using next
  have last := prefix_succ (sourceWidth L) (1 : Fin 2)
  change sourceEnd L = sourceStart L (1 : Fin 2) + (L (1 : Fin 2)).width at last
  rw [second] at last
  refine ⟨second, ?_⟩
  rw [← last]
  exact canonicalParse_at_source_starts rawProgram selected L trace start addr binding atPc

/-- Complete public-caller projection, not an additional alignment assumption.
The current433/438 public Root still explicitly takes programBinding,
rawProgramDecodes, and rowsAligned (Soundness.lean at ade695c5:2100-2120).
All other original caller inputs are retained here, but parsing needs only
that existing structural subset and never invokes root_soundness. This proof
is checked in the preserved schema; current-main integration is separate. -/
theorem root_domain_canonicalParse_total
    (n rawLength : Nat) (trace : AcceptedZiskTrace n)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (_core : ∀ i, InputsAgreeCore trace (chainedSailTrace steps init) i (steps i))
    (_pcBoot : ∀ (_ : 0 < n), ((mainOfTable trace.program trace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (rowsAligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i))))
    (_bootSeed : BootSegmentMemorySeed trace (chainedSailTrace steps init) steps)
    (_regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (_avoid : ∀ i, RowOutsideDefectRegion trace i (steps i)) :
    ∃ parsed : List (Σ k, SuccessfulRowLowering (rawProgram k)) × Nat,
      canonicalParse trace addr rawProgram n = some parsed ∧
      (∀ last : Fin n, last.val + 1 = n → parsed.2 =
        stepProducerRow last (steps last) (rowDecode_of_programDecode trace last
          (programDecode_of_rawProgramDecode trace last (steps last) start addr
            rawProgram binding (rawDecodes last))) + 1) := by
  obtain ⟨selected, L, parsed, _, ends⟩ :=
    old_canonicalParse_total trace steps start addr rawProgram binding rawDecodes rowsAligned
  exact ⟨(List.ofFn (fun i => (⟨selected i, L i⟩ :
    Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd L), parsed, ends⟩

end ZiskFv.Compliance.CanonicalSourceParser
