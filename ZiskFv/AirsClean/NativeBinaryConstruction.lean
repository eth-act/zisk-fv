import ZiskFv.AirsClean.NativeBinaryInstance

/-!
SUPPLEMENTAL INTERNAL constructibility only. This explicit SourceObject image
has a full native primary-buffer domain, real ordered AIR stage metadata (AIR
`dim` remains zero), and separately stored complete extension/challenge words.
The arbitrary raw scalar includes nonzero and negative values. No equation is
asserted to hold, and no image is claimed to be produced, accepted, authenticated,
balanced, or to have padding_size equal to its physical padding count.

The large raw buffer below is only a symbolic source input for this existence
proof; the instance constructor/projections do not allocate/copy it or enumerate
its rows. Array-size lemmas, not reduction over physical N, discharge coverage.
-/
namespace ZiskFv.AirsClean.NativeBinaryConstruction

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open NativeBinaryInstance

private def airEntry (name : String) (stage : Nat) : PolMap :=
  ⟨name, stage, 0, false, 0, 0, #[], 0, 0, 0⟩

private def challengeEntry (index : Nat) : PolMap :=
  ⟨"", 2, 3, false, 0, index, #[], 0, 0, 0⟩

private def setup : NativeSetup := {
  profile := ⟨false, false, false⟩
  airgroupId := 0
  airId := 22
  nBits := 22
  nBitsExt := 23
  nStages := 2
  nConstants := 1
  nPublics := 0
  cmPolsMap := #[]
  constPolsMap := #[]
  airValuesMap := #[airEntry "Binary.padding_size" 1, airEntry "Binary.im_direct" 2]
  airgroupValuesMap := #[]
  proofValuesMap := #[]
  publicsMap := #[]
  challengesMap := #[challengeEntry 0, challengeEntry 1]
  customCommitsMap := #[]
  customCommits := #[]
  openingPoints := #[0]
  mapSectionsN := ({} : Std.HashMap String Nat).insert "cm1" 39
  mapOffsets := {} }

/-- An explicitly synthetic internal image, NOT an accepted/native-producer
witness. It deliberately imposes no relation between raw p and row contents. -/
private def image (padding : FGL) : SourceObject FGL := {
  globals := ⟨#[], #[], #[2, 3, 4, 5, 6, 7], #[]⟩
  registry := ⟨#[⟨0, 22, false, false, 1, 1⟩], 0, #[0], #[0], #[], #[], #[true]⟩
  slots := #[{
    metadata := ⟨0, 22, 4194304, 4, false, true, 0⟩
    trace := Array.replicate (4194304 * 4) 0
    auxTrace := #[]
    customCommitsFixed := #[]
    airgroupValues := #[]
    airvalues := #[padding, 8, 9, 10]
    challenges := #[]
    evals := #[]
    fixed := #[] }]
  setupRepository := ({} : Std.HashMap (Nat × Nat) NativeSetup).insert (0, 22) setup }

private def resolved (padding : FGL) : ResolvedOccurrence (image padding) :=
  ⟨⟨0, by simp [image]⟩, by simp [image]⟩

private theorem selected_setup (padding : FGL) : (resolved padding).setup? = some setup := by
  simp [ResolvedOccurrence.setup?, SourceObject.setupAt?, ResolvedOccurrence.registryEntry,
    SourceObject.registryEntry, resolved, image]

private theorem selected_params (padding : FGL) :
    (resolved padding).params false = paramsOf (image padding).globals (image padding).slots[0] := rfl

private theorem selected_operands (padding : FGL) :
    NativeBinaryInstance.readOperands? (resolved padding) =
      some (⟨padding, ⟨8, 9, 10⟩, ⟨2, 3, 4⟩, ⟨5, 6, 7⟩⟩ : BinaryPaddingOperations.Operands) := by
  simp [NativeBinaryInstance.readOperands?, selected_setup, setup, airEntry,
    NativeValuesLayout.padding_reads_actual_buffer, ResolvedOccurrence.airValueWords?,
    valueWidth, valueOffset, Mem.Stage2.challenge?, challengeEntry,
    Mem.Stage2.extensionWords?, readBlock?, buffer?, selected_params, image, paramsOf]

private theorem selected_base (padding : FGL) :
    NativeTraceCells.rowBase? .binary (resolved padding) false 0 = some 0 := by
  simp [NativeTraceCells.rowBase?, selected_setup, setup, NativeTraceRules.actual_source_ready,
    NativeSetup.rowCount, NativeTraceCells.profile, NativeTraceCells.nativeStride,
    Extraction.RuntimeMainTraceLayout.binaryProfile,
    Extraction.RuntimeMainTraceLayout.Profile.packedWords,
    Extraction.RuntimeMainTraceLayout.Profile.unpackedWords,
    ResolvedOccurrence.registryEntry, SourceObject.registryEntry,
    ResolvedOccurrence.slotData, ResolvedOccurrence.globalSlot, resolved,
    selected_params, image, paramsOf]

/-- Nonvacuity of the SAME real source-reader/instance constructor, including
all three coefficients and a nonzero-capable raw p. This does NOT supply the
separate native producer/compiled-r.id/PIL/ABI or Accepted/balance law. -/
theorem constructible_for_every_raw_scalar (padding : FGL) :
    ∃ source : SourceObject FGL, ∃ view : NativeBinaryInstance source,
      NativeBinaryInstance.fromResolved? view.resolved = some view ∧
      view.direct.operands.padding = padding ∧
      view.direct.operands.inverse = ⟨8, 9, 10⟩ ∧
      view.direct.operands.alpha = ⟨2, 3, 4⟩ ∧
      view.direct.operands.gamma = ⟨5, 6, 7⟩ := by
  let operands : BinaryPaddingOperations.Operands := ⟨padding, ⟨8, 9, 10⟩, ⟨2, 3, 4⟩, ⟨5, 6, 7⟩⟩
  obtain ⟨cells, hcells⟩ :
      ∃ cells, NativeBinaryInstance.cells? (resolved padding) = some cells := by
    simp [NativeBinaryInstance.cells?, selected_operands]
  let anchor : NativeTraceCells.Row .binary (resolved padding) false 0 :=
    ⟨0, selected_base padding⟩
  have hn : NativeTraceCells.row? .binary (resolved padding) false 0 = some anchor :=
    anchor.constructor_recovers
  have hread := cells.selected
  rw [selected_operands] at hread
  have heq : operands = cells.operands := Option.some.inj hread
  obtain ⟨view, hview⟩ :
      ∃ view, NativeBinaryInstance.fromResolved? (resolved padding) = some view := by
    simp [NativeBinaryInstance.fromResolved?, hn, hcells]
  refine ⟨image padding, view, view.constructor_recovers, ?_⟩
  unfold NativeBinaryInstance.fromResolved? at hview
  simp only [hn] at hview
  dsimp only [Bind.bind, Option.bind] at hview
  simp only [hcells] at hview
  cases Option.some.inj hview
  change cells.operands.padding = padding ∧ cells.operands.inverse = _ ∧
    cells.operands.alpha = _ ∧ cells.operands.gamma = _
  rw [← heq]
  exact ⟨rfl, rfl, rfl, rfl⟩

end ZiskFv.AirsClean.NativeBinaryConstruction
