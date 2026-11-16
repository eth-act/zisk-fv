import ZiskFv.Compliance.TraceLevelExport.CanonicalJalrWorldSoundness

/-!
Additive SOURCE-ONLY #417 boundary proposal. No production declaration changes.
The candidate Root is a proposition below, NOT an asserted soundness theorem.
The checked syntax replaces old steps/raw-decodes/alignment, carries no StepSound
or InputsAgreeCore discharge, and keeps the ORIGINAL Accepted trace and state.
-/

namespace ZiskFv.Compliance.CanonicalSyntaxBoundary

open Goldilocks
open CanonicalExecutionRows CanonicalSourceParser RawProgramBinding SerializedExecutionRows
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.ZiskCircuit.MemTimeline.Spike

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

/-- This index is always computed from real source widths, never supplied. -/
def sourceIndex {n m : Nat} {words : Fin m → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i))
    (within : ∀ i, sourceStart lowering i < n) (i : Fin m) : Fin n :=
  ⟨sourceStart lowering i, within i⟩

/-- Checked SOURCE data, not a semantic execution certificate.
`parsed` pins selected/lowering to the actual checker result. There is no free
row map/end or parser-success Root binder. The finite head/coverage checks retain
every physical row below n. P=sourceEnd lowering may exceed n only because the
last real head can own a terminal auxiliary row; no extra RV step is invented.
The original raw-decode source obligations are retained honestly, not disguised
as a discharge of the per-op Core/platform/memory obligations. -/
structure CheckedSyntax {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) where
  count : Nat
  selected : Fin count → Fin rawLength
  lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i))
  parsed : canonicalParse trace addr rawProgram count =
    some (List.ofFn (fun i => (⟨selected i, lowering i⟩ :
      Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd lowering)
  headWithin : ∀ i, sourceStart lowering i < n
  covered : n ≤ sourceEnd lowering
  room : sourceEnd lowering ≤ trace.mainTable.table.length
  atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
    (sourceStart lowering i) = addr (selected i)
  steps : ∀ i, ZiskStep trace (sourceIndex lowering headWithin i)
  rawDecodes : ∀ i, RawProgramDecode trace (sourceIndex lowering headWithin i)
    (steps i) start addr rawProgram

namespace CheckedSyntax

variable {n rawLength : Nat} {trace : AcceptedZiskTrace n}
variable {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
variable {rawProgram : Fin rawLength → BitVec 32}

def index (checked : CheckedSyntax trace start addr rawProgram) (i : Fin checked.count) : Fin n :=
  sourceIndex checked.lowering checked.headWithin i

def endpoint (checked : CheckedSyntax trace start addr rawProgram) : Nat :=
  sourceEnd checked.lowering

noncomputable def decoded (checked : CheckedSyntax trace start addr rawProgram)
    (binding : ProgramRowsBinding trace start addr rawProgram) (i : Fin checked.count) :
    RowDecode trace (checked.index i) (checked.steps i) :=
  rowDecode_of_programDecode trace (checked.index i)
    (programDecode_of_rawProgramDecode trace (checked.index i) (checked.steps i)
      start addr rawProgram binding (checked.rawDecodes i))

/-- Only genuine architectural Fin count indices execute Sail. -/
noncomputable def states (checked : CheckedSyntax trace start addr rawProgram) (init : State) :
    (j : Nat) → j ≤ checked.count → State
  | 0, _ => init
  | j + 1, h => retirePC (sailStepPost
      (sailInstructionOf (checked.index ⟨j, by omega⟩) (checked.steps ⟨j, by omega⟩))
      (states checked init j (by omega)))

noncomputable def owner (checked : CheckedSyntax trace start addr rawProgram) (r : Fin n) :
    Fin checked.count :=
  physicalOwner checked.lowering ⟨r.val, Nat.lt_of_lt_of_le r.isLt checked.covered⟩

/-- Auxiliaries carry the owner's PRE-state; they never execute a dummy step. -/
noncomputable def ownerTrace (checked : CheckedSyntax trace start addr rawProgram)
    (init : State) : SailTrace n :=
  fun r => checked.states init (checked.owner r).val (Nat.le_of_lt (checked.owner r).isLt)

theorem owner_at_index (checked : CheckedSyntax trace start addr rawProgram) (i : Fin checked.count) :
    checked.owner (checked.index i) = i := by
  apply (physicalOwner_unique checked.lowering _ i ?_).symm
  exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (checked.lowering i).width_pos⟩

theorem state_at_index (checked : CheckedSyntax trace start addr rawProgram)
    (init : State) (i : Fin checked.count) :
    checked.ownerTrace init (checked.index i) = checked.states init i.val (Nat.le_of_lt i.isLt) := by
  simp only [ownerTrace, owner_at_index]

end CheckedSyntax

private def transportStep {n : Nat} {trace : AcceptedZiskTrace n} {i j : Fin n}
    (same : i = j) (step : ZiskStep trace i) : ZiskStep trace j := same ▸ step

private def transportRaw {n rawLength : Nat} {trace : AcceptedZiskTrace n} {i j : Fin n}
    (same : i = j) (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (raw : RawProgramDecode trace i step start addr rawProgram) :
    RawProgramDecode trace j (transportStep same step) start addr rawProgram := by
  cases same
  exact raw

private theorem transportInstruction {n : Nat} {trace : AcceptedZiskTrace n} {i j : Fin n}
    (same : i = j) (step : ZiskStep trace i) :
    sailInstructionOf j (transportStep same step) = sailInstructionOf i step := by
  cases same
  rfl

universe u

private def transportEvidence {n : Nat} {trace : AcceptedZiskTrace n} {i j : Fin n}
    (same : i = j) (step : ZiskStep trace i)
    (predicate : (k : Fin n) → ZiskStep trace k → Sort u) (evidence : predicate i step) :
    predicate j (transportStep same step) := by
  cases same
  exact evidence

private theorem soundOfTransportRaw {n rawLength : Nat}
    {trace : AcceptedZiskTrace n} {i j : Fin n} (same : i = j) (step : ZiskStep trace i)
    (history : Fin n → State) (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (raw : RawProgramDecode trace i step start addr rawProgram)
    (sound : StepSound trace history j (transportStep same step)
      (rowDecode_of_programDecode trace j
        (programDecode_of_rawProgramDecode trace j (transportStep same step)
          start addr rawProgram binding (transportRaw same step start addr rawProgram raw)))) :
    StepSound trace history i step
      (rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i step start addr rawProgram binding raw)) := by
  cases same
  exact sound

section Legacy

variable {n rawLength : Nat} (trace : AcceptedZiskTrace n)
variable (steps : ∀ i : Fin n, ZiskStep trace i)
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (rawProgram : Fin rawLength → BitVec 32)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (raw : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)

private noncomputable def oldDecoded (i : Fin n) : RowDecode trace i (steps i) :=
  rowDecode_of_programDecode trace i
    (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram binding (raw i))

variable (aligned : StepRowsAligned trace steps (oldDecoded trace steps start addr rawProgram binding raw))

private structure LegacyLayout where
  selected : Fin n → Fin rawLength
  lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i))
  starts : ∀ i, sourceStart lowering i = i.val
  room : sourceEnd lowering ≤ trace.mainTable.table.length
  atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
    (sourceStart lowering i) = addr (selected i)
  parsed : canonicalParse trace addr rawProgram n =
    some (List.ofFn (fun i => (⟨selected i, lowering i⟩ :
      Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd lowering)

private noncomputable def legacyLayout : LegacyLayout trace addr rawProgram := by
  classical
  apply Classical.choice
  obtain ⟨selected, lowering, widths, starts, ends⟩ :=
    RawDecodeRowLowering.old_raw_source_widths_and_placement trace steps start addr rawProgram
      binding raw aligned
  have room : sourceEnd lowering ≤ trace.mainTable.table.length := by
    by_cases nonempty : 0 < n
    · let last : Fin n := ⟨n - 1, by omega⟩
      rw [ends last (by dsimp [last]; omega)]
      exact Nat.le_of_lt (ExecutionSpanLegacy.producer_has_successor last (steps last)
        (oldDecoded trace steps start addr rawProgram binding raw last))
    · have empty : n = 0 := by omega
      subst n
      simp [sourceEnd, rowPrefix]
  have atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (sourceStart lowering i) = addr (selected i) := by
    intro i
    rw [starts i]
    exact (widths i).1.symm
  exact ⟨{
    selected := selected
    lowering := lowering
    starts := starts
    room := room
    atPc := atPc
    parsed := canonicalParse_complete trace start addr rawProgram binding
      selected lowering room atPc }⟩

private def legacyWithin (i : Fin n) :
    sourceStart (legacyLayout trace steps start addr rawProgram binding raw aligned).lowering i < n := by
  rw [(legacyLayout trace steps start addr rawProgram binding raw aligned).starts i]
  exact i.isLt

private theorem legacyIndexEq (i : Fin n) :
    sourceIndex (legacyLayout trace steps start addr rawProgram binding raw aligned).lowering
      (legacyWithin trace steps start addr rawProgram binding raw aligned) i = i :=
  Fin.ext ((legacyLayout trace steps start addr rawProgram binding raw aligned).starts i)

/-- Whole old SOURCE inputs construct checked syntax. Parser success/room/map
are conclusions, including empty and final-width-two old cases. SAME trace. -/
noncomputable def ofLegacy : CheckedSyntax trace start addr rawProgram :=
  let layout := legacyLayout trace steps start addr rawProgram binding raw aligned
  { count := n, selected := layout.selected, lowering := layout.lowering,
    parsed := layout.parsed, headWithin := legacyWithin trace steps start addr rawProgram binding raw aligned,
    covered := architecturalCount_le_sourceEnd layout.lowering,
    room := layout.room, atPc := layout.atPc,
    steps := fun i => transportStep
      (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm (steps i),
    rawDecodes := fun i => transportRaw
      (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
      (steps i) start addr rawProgram (raw i) }

theorem ofLegacy_count : (ofLegacy trace steps start addr rawProgram binding raw aligned).count = n := rfl

theorem ofLegacy_index (i : Fin n) :
    (ofLegacy trace steps start addr rawProgram binding raw aligned).index i = i :=
  legacyIndexEq trace steps start addr rawProgram binding raw aligned i

private theorem ofLegacy_instruction (i : Fin n) :
    sailInstructionOf ((ofLegacy trace steps start addr rawProgram binding raw aligned).index i)
      ((ofLegacy trace steps start addr rawProgram binding raw aligned).steps i) =
        sailInstructionOf i (steps i) :=
  transportInstruction (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm (steps i)

private theorem ofLegacy_states (init : State) (j : Nat) (bound : j ≤ n) :
    (ofLegacy trace steps start addr rawProgram binding raw aligned).states init j bound =
      chainedSailStates steps init j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have inside : j < n := by omega
    simp only [CheckedSyntax.states, chainedSailStates]
    rw [ofLegacy_instruction, ih (by omega)]
    split_ifs with h
    · rfl
    · exact False.elim (h inside)

theorem ofLegacy_owner (r : Fin n) :
    (ofLegacy trace steps start addr rawProgram binding raw aligned).owner r = r := by
  let checked := ofLegacy trace steps start addr rawProgram binding raw aligned
  have atStart : checked.index r = r := ofLegacy_index trace steps start addr rawProgram binding raw aligned r
  calc
    checked.owner r = checked.owner (checked.index r) := congrArg checked.owner atStart.symm
    _ = r := checked.owner_at_index r

theorem ofLegacy_ownerTrace (init : State) :
    (ofLegacy trace steps start addr rawProgram binding raw aligned).ownerTrace init =
      chainedSailTrace steps init := by
  funext r
  simp only [CheckedSyntax.ownerTrace, ofLegacy_owner, chainedSailTrace]
  exact ofLegacy_states trace steps start addr rawProgram binding raw aligned init r.val (Nat.le_of_lt r.isLt)

end Legacy

/-- The THREE retained original narrow-store leaves, evaluated at the actual
architecturally generated state. They are not a relocated seven-field seed. -/
def SbPreservedAt {n : Nat} (trace : AcceptedZiskTrace n) (history : SailTrace n)
    (i : Fin n) (step : ZiskStep trace i) : Prop :=
  ∀ config, step = .sb config → StoreRmwPreservedBytesAtPrefix (history i).mem
    (busSt trace i (Pilot.execRowOf trace i)).e2 1

def ShPreservedAt {n : Nat} (trace : AcceptedZiskTrace n) (history : SailTrace n)
    (i : Fin n) (step : ZiskStep trace i) : Prop :=
  ∀ config, step = .sh config → StoreRmwPreservedBytesAtPrefix (history i).mem
    (busSt trace i (Pilot.execRowOf trace i)).e2 2

def SwPreservedAt {n : Nat} (trace : AcceptedZiskTrace n) (history : SailTrace n)
    (i : Fin n) (step : ZiskStep trace i) : Prop :=
  ∀ config, step = .sw config → StoreRmwPreservedBytesAtPrefix (history i).mem
    (busSt trace i (Pilot.execRowOf trace i)).e2 4

/-- Only a genuine boot/image memory equation remains. It is guarded to retain
old empty-trace domain; no per-step replay/read/presence/placement is assumed. -/
def BootMemoryAt {n rawLength : Nat} {trace : AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    (checked : CheckedSyntax trace start addr rawProgram) (init : State) : Prop :=
  0 < checked.count → ∀ present : MutableMemPresent trace.witness,
    init.mem = (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (trace.memReplayBridge present)).initialMemory

structure NewPremises {n rawLength : Nat} (trace : AcceptedZiskTrace n) (init : State)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (checked : CheckedSyntax trace start addr rawProgram) where
  inputsAgree : ∀ i, InputsAgreeCore trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
  pcBoot : 0 < checked.count → ((mainOfTable trace.program trace.mainTable).pc 0).val =
    (init.regs.get? Register.PC).elim 0 BitVec.toNat
  memoryBoot : BootMemoryAt checked init
  sbPreserved : ∀ i, SbPreservedAt trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
  shPreserved : ∀ i, ShPreservedAt trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
  swPreserved : ∀ i, SwPreservedAt trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
  regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
    some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64))
  avoid : ∀ i, RowOutsideDefectRegion trace (checked.index i) (checked.steps i)

/-- EXACT candidate replacement statement. This is a TYPE DEFINITION for owner
review, NOT a theorem or new axiom. No new Source/Accepted/validator premise,
map/parser-success/presence/read/range/free-end/StepSound promise is added. -/
def WouldBeRoot : Prop :=
  ∀ (n rawLength : Nat) (trace : AcceptedZiskTrace n) (init : State)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (checked : CheckedSyntax trace start addr rawProgram)
    (inputsAgree : ∀ i, InputsAgreeCore trace (checked.ownerTrace init) (checked.index i) (checked.steps i))
    (pcBoot : 0 < checked.count → ((mainOfTable trace.program trace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (memoryBoot : BootMemoryAt checked init)
    (sbPreserved : ∀ i, SbPreservedAt trace (checked.ownerTrace init) (checked.index i) (checked.steps i))
    (shPreserved : ∀ i, ShPreservedAt trace (checked.ownerTrace init) (checked.index i) (checked.steps i))
    (swPreserved : ∀ i, SwPreservedAt trace (checked.ownerTrace init) (checked.index i) (checked.steps i))
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (avoid : ∀ i, RowOutsideDefectRegion trace (checked.index i) (checked.steps i))
    (i : Fin checked.count),
      StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i) (checked.decoded binding i)

section OldWholePremises

variable {n rawLength : Nat} (trace : AcceptedZiskTrace n) (init : State)
variable (steps : ∀ i : Fin n, ZiskStep trace i)
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (rawProgram : Fin rawLength → BitVec 32)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (raw : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
variable (inputs : ∀ i, InputsAgreeCore trace (chainedSailTrace steps init) i (steps i))
variable (pcBoot : 0 < n → ((mainOfTable trace.program trace.mainTable).pc 0).val =
  (init.regs.get? Register.PC).elim 0 BitVec.toNat)
variable (aligned : StepRowsAligned trace steps (oldDecoded trace steps start addr rawProgram binding raw))
variable (seed : BootSegmentMemorySeed trace (chainedSailTrace steps init) steps)
variable (regs : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
  some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
variable (avoid : ∀ i, RowOutsideDefectRegion trace i (steps i))

include seed in
private theorem oldSb (i : Fin n) : SbPreservedAt trace (chainedSailTrace steps init) i (steps i) := by
  intro config same
  have placed := seed.placement i
  rw [same] at placed
  have positive : 0 < n := Nat.zero_lt_of_lt i.isLt
  have memory := exec_order_fold_fin (chainedSailTrace steps init) seed.memInit seed.rowsOf
    positive (seed.boot positive) seed.step i
  rw [memory]
  exact placed.2

include seed in
private theorem oldSh (i : Fin n) : ShPreservedAt trace (chainedSailTrace steps init) i (steps i) := by
  intro config same
  have placed := seed.placement i
  rw [same] at placed
  have positive : 0 < n := Nat.zero_lt_of_lt i.isLt
  have memory := exec_order_fold_fin (chainedSailTrace steps init) seed.memInit seed.rowsOf
    positive (seed.boot positive) seed.step i
  rw [memory]
  exact placed.2

include seed in
private theorem oldSw (i : Fin n) : SwPreservedAt trace (chainedSailTrace steps init) i (steps i) := by
  intro config same
  have placed := seed.placement i
  rw [same] at placed
  have positive : 0 < n := Nat.zero_lt_of_lt i.isLt
  have memory := exec_order_fold_fin (chainedSailTrace steps init) seed.memInit seed.rowsOf
    positive (seed.boot positive) seed.step i
  rw [memory]
  exact placed.2

/-- ALL original public Root hypotheses imply the proposed new hypotheses on
EXACTLY the same Accepted trace/initial state. No old/new Root theorem is used.
In particular no StepSound field, oracle, parse/map/success premise or relocated
memory-step/read/presence/placement bundle enters the new object. -/
noncomputable def wholeOldPremisesToNew :
    NewPremises trace init start addr rawProgram
      (ofLegacy trace steps start addr rawProgram binding raw aligned) := by
  let checked := ofLegacy trace steps start addr rawProgram binding raw aligned
  have histories : checked.ownerTrace init = chainedSailTrace steps init :=
    ofLegacy_ownerTrace trace steps start addr rawProgram binding raw aligned init
  refine {
    inputsAgree := ?_
    pcBoot := pcBoot
    memoryBoot := ?_
    sbPreserved := ?_
    shPreserved := ?_
    swPreserved := ?_
    regBoot := regs
    avoid := ?_ }
  · intro i
    rw [histories]
    exact transportEvidence (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
      (steps i) (fun j step => InputsAgreeCore trace (chainedSailTrace steps init) j step) (inputs i)
  · intro positive present
    have boot := seed.boot positive
    change init.mem = seed.memInit at boot
    exact boot.trans (seed.readSoundInputs present).initialMemory_eq
  · intro i
    rw [histories]
    exact transportEvidence (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
      (steps i) (SbPreservedAt trace (chainedSailTrace steps init)) (oldSb trace init steps seed i)
  · intro i
    rw [histories]
    exact transportEvidence (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
      (steps i) (ShPreservedAt trace (chainedSailTrace steps init)) (oldSh trace init steps seed i)
  · intro i
    rw [histories]
    exact transportEvidence (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
      (steps i) (SwPreservedAt trace (chainedSailTrace steps init)) (oldSw trace init steps seed i)
  · intro i
    exact transportEvidence (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
      (steps i) (RowOutsideDefectRegion trace) (avoid i)

include inputs pcBoot seed regs avoid in
/-- Propositional form of the actual whole-old→new premise constructor.
This includes the requested old width-one subdomain and does not need a
width-one assumption: old final-width-two fixtures retain their real endpoint. -/
theorem wholeOldPremises_implication :
    Nonempty (NewPremises trace init start addr rawProgram
      (ofLegacy trace steps start addr rawProgram binding raw aligned)) :=
  ⟨wholeOldPremisesToNew trace init steps start addr rawProgram binding raw inputs
    pcBoot aligned seed regs avoid⟩

end OldWholePremises

/-- Literal old root telescope, including its conclusion index.
The proposed replacement implies this exact statement on the same trace/init,
without appealing to either the existing root proof value or a recount theorem. -/
def CurrentOldRootStatement : Prop :=
  ∀ (n rawLength : Nat) (trace : AcceptedZiskTrace n) (init : State)
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (raw : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (inputs : ∀ i, InputsAgreeCore trace (chainedSailTrace steps init) i (steps i))
    (pcBoot : ∀ _ : 0 < n, ((mainOfTable trace.program trace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (aligned : StepRowsAligned trace steps
      (fun i => rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram binding (raw i))))
    (seed : BootSegmentMemorySeed trace (chainedSailTrace steps init) steps)
    (regs : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (avoid : ∀ i, RowOutsideDefectRegion trace i (steps i))
    (i : Fin n),
    StepSound trace (chainedSailTrace steps init) i (steps i)
      (rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram binding (raw i)))

theorem proposedRoot_implies_exactOld (proved : WouldBeRoot) : CurrentOldRootStatement := by
  intro n rawLength trace init steps start addr rawProgram binding raw inputs
    pcBoot aligned seed regs avoid i
  let checked := ofLegacy trace steps start addr rawProgram binding raw aligned
  let premises := wholeOldPremisesToNew trace init steps start addr rawProgram binding raw
    inputs pcBoot aligned seed regs avoid
  have current := proved n rawLength trace init start addr rawProgram binding checked
    premises.inputsAgree premises.pcBoot premises.memoryBoot premises.sbPreserved
    premises.shPreserved premises.swPreserved premises.regBoot premises.avoid i
  rw [ofLegacy_ownerTrace] at current
  exact soundOfTransportRaw
    (legacyIndexEq trace steps start addr rawProgram binding raw aligned i).symm
    (steps i) (chainedSailTrace steps init) start addr rawProgram binding (raw i) current

section ActualTwoRowWorld

open CanonicalJalrWorld
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation AddFaithfulPaddedRootSoundness

private def worldWithin (i : Fin 2) : sourceStart repeatJalrLowerings i < 4 := by
  rw [← worldSourceBounds.2.2.1 i]
  exact (worldSourceIndex i).isLt

private theorem worldIndexEq (i : Fin 2) :
    sourceIndex repeatJalrLowerings worldWithin i = worldSourceIndex i :=
  Fin.ext (worldSourceBounds.2.2.1 i).symm

/-- The NEW two-row source world inhabits the proposed syntax/domain on the
same Accepted4, not Accepted2 and not an old false-alignment specialization.
No first-Sail-soundness/core/state/memory oracle is an input to this object. -/
noncomputable def actualWorldSyntax :
    CheckedSyntax worldTrace worldStart (fun _ => 0) repeatJalrRawProgram where
  count := 2
  selected := repeatJalrSelected
  lowering := repeatJalrLowerings
  parsed := by simpa only [repeatJalr_sourceEnd] using worldCanonicalParse
  headWithin := worldWithin
  covered := by simpa only [repeatJalr_sourceEnd] using (Nat.le_refl 4)
  room := by rw [repeatJalr_sourceEnd, worldSourceBounds.2.1]; decide
  atPc := by
    intro i
    rw [← worldSourceBounds.2.2.1 i]
    fin_cases i <;> simp [worldSourceIndex, mainOfTable, worldRow0, worldRow2,
      worldRow0Template, worldRow2Template, mainRomRowOf, worldAddProgramRow]
  steps := fun i => transportStep (worldIndexEq i).symm (.jalr (worldClaim i))
  rawDecodes := fun i => transportRaw (worldIndexEq i).symm (.jalr (worldClaim i))
    worldStart (fun _ => 0) repeatJalrRawProgram (worldRawDecode i)

theorem actualWorldSyntax_domain :
    actualWorldSyntax.count = 2 ∧ actualWorldSyntax.endpoint = 4 ∧
      actualWorldSyntax.endpoint ≤ worldTrace.mainTable.table.length ∧
      (∀ i : Fin 2, actualWorldSyntax.index i = worldSourceIndex i) := by
  refine ⟨rfl, repeatJalr_sourceEnd, actualWorldSyntax.room, ?_⟩
  exact worldIndexEq

private theorem actualWorldInstruction (i : Fin 2) :
    sailInstructionOf (actualWorldSyntax.index i) (actualWorldSyntax.steps i) = repeatJalrInstruction := by
  change sailInstructionOf _ (transportStep (worldIndexEq i).symm (.jalr (worldClaim i))) = _
  exact transportInstruction (worldIndexEq i).symm (.jalr (worldClaim i))

private theorem actualWorldStateOne :
    actualWorldSyntax.states repeatJalrInit 1 (by decide) = repeatJalrSecond := by
  change retirePC (sailStepPost
    (sailInstructionOf (actualWorldSyntax.index (0 : Fin 2))
      (actualWorldSyntax.steps (0 : Fin 2))) repeatJalrInit) = _
  rw [actualWorldInstruction, sailStepPost, repeatJalr_first_execution]
  rfl

theorem actualWorldFinalState :
    actualWorldSyntax.states repeatJalrInit 2 (by decide) = repeatJalrFinal := by
  change retirePC (sailStepPost
    (sailInstructionOf (actualWorldSyntax.index (1 : Fin 2))
      (actualWorldSyntax.steps (1 : Fin 2)))
      (actualWorldSyntax.states repeatJalrInit 1 (by decide))) = _
  rw [actualWorldInstruction, actualWorldStateOne, sailStepPost,
    repeatedJalr_actual_sail_execution.2.2.2.1]
  rfl

private theorem actualWorldOwner (r : Fin 4) (i : Fin 2)
    (covered : sourceStart repeatJalrLowerings i ≤ r.val ∧
      r.val < sourceStart repeatJalrLowerings i + 2) :
    actualWorldSyntax.owner r = i := by
  apply (physicalOwner_unique repeatJalrLowerings _ i ?_).symm
  simpa only [repeatJalrLowerings_width] using covered

private theorem worldSecondStart : sourceStart repeatJalrLowerings (1 : Fin 2) = 2 := by
  simpa [worldSourceIndex] using (worldSourceBounds.2.2.1 (1 : Fin 2)).symm

theorem actualWorldOwnerTrace :
    actualWorldSyntax.ownerTrace repeatJalrInit = worldSailTrace := by
  funext r
  fin_cases r
  · have owner := actualWorldOwner (0 : Fin 4) (0 : Fin 2) (by simp [sourceStart, prefix_zero])
    change actualWorldSyntax.states repeatJalrInit (actualWorldSyntax.owner 0).val _ = _
    simp only [owner]
    rfl
  · have owner := actualWorldOwner (1 : Fin 4) (0 : Fin 2) (by simp [sourceStart, prefix_zero])
    change actualWorldSyntax.states repeatJalrInit (actualWorldSyntax.owner 1).val _ = _
    simp only [owner]
    rfl
  · have owner := actualWorldOwner (2 : Fin 4) (1 : Fin 2) (by simp [worldSecondStart])
    change actualWorldSyntax.states repeatJalrInit (actualWorldSyntax.owner 2).val _ = _
    simp only [owner]
    exact actualWorldStateOne
  · have owner := actualWorldOwner (3 : Fin 4) (1 : Fin 2) (by simp [worldSecondStart])
    change actualWorldSyntax.states repeatJalrInit (actualWorldSyntax.owner 3).val _ = _
    simp only [owner]
    exact actualWorldStateOne

private theorem actualWorldAvoiding :
    ∀ i : Fin 2, RowOutsideDefectRegion worldTrace (worldSourceIndex i) (.jalr (worldClaim i)) := by
  rcases worldNonvacuity with ⟨_, _, _, _, _, _, _, _, avoiding⟩
  exact avoiding

/-- Actual new-domain premise constructibility, not a new Root soundness proof.
The memory guard is false because this ACTUAL accepted world has no mutable
memory entries; the architectural/Sail part still has two REAL instructions. -/
noncomputable def actualWorldNewPremises :
    NewPremises worldTrace repeatJalrInit worldStart (fun _ => 0) repeatJalrRawProgram
      actualWorldSyntax := by
  refine {
    inputsAgree := ?_
    pcBoot := ?_
    memoryBoot := ?_
    sbPreserved := ?_
    shPreserved := ?_
    swPreserved := ?_
    regBoot := repeatJalrInit_regBoot
    avoid := ?_ }
  · intro i
    rw [actualWorldOwnerTrace]
    exact transportEvidence (worldIndexEq i).symm (.jalr (worldClaim i))
      (fun j step => InputsAgreeCore worldTrace worldSailTrace j step)
      (worldInputs i).toInputsCore_jalr
  · intro _
    have pc := (worldInputs (0 : Fin 2)).h_pc_bridge
    change ((mainOfTable worldTrace.program worldTrace.mainTable).pc 0).val = 0 at pc
    have pcRead := (worldInputs (0 : Fin 2)).h_input_pc
    change repeatJalrInit.regs.get? Register.PC = some (0#64) at pcRead
    rw [pc, pcRead]
    rfl
  · intro _ present
    exact False.elim (worldWitness_not_mutableMemPresent present)
  · intro i
    rw [actualWorldOwnerTrace]
    apply transportEvidence (worldIndexEq i).symm (.jalr (worldClaim i))
      (SbPreservedAt worldTrace worldSailTrace)
    intro config same
    cases same
  · intro i
    rw [actualWorldOwnerTrace]
    apply transportEvidence (worldIndexEq i).symm (.jalr (worldClaim i))
      (ShPreservedAt worldTrace worldSailTrace)
    intro config same
    cases same
  · intro i
    rw [actualWorldOwnerTrace]
    apply transportEvidence (worldIndexEq i).symm (.jalr (worldClaim i))
      (SwPreservedAt worldTrace worldSailTrace)
    intro config same
    cases same
  · intro i
    exact transportEvidence (worldIndexEq i).symm (.jalr (worldClaim i))
      (RowOutsideDefectRegion worldTrace) (actualWorldAvoiding i)

theorem actualWorldNewPremises_nonempty :
    Nonempty (NewPremises worldTrace repeatJalrInit worldStart (fun _ => 0) repeatJalrRawProgram
      actualWorldSyntax) := ⟨actualWorldNewPremises⟩

end ActualTwoRowWorld

end ZiskFv.Compliance.CanonicalSyntaxBoundary
