import ZiskFv.AirsClean.PublicIoSource
import ZiskFv.AirsClean.PublicIoMainNativeTrace

/-! INTERNAL source-owned public verifier, not a new68 Accepted/Root world.
The constructor selects the setup through the SAME resolved registry occurrence,
retains its publicsMap and original Params/global public buffer, and computes the
existing PublicIo.PublicIO vector. No independent vector/equality, zero fallback,
caller success/height promise, new source field or 32-bit limb validator occurs.

Actual ff0e C++ expressions_info.cpp513–520 encodes PublicValue id DIRECTLY;
expressions_pack.hpp356 selects Params.publicInputs, while GLOBAL evaluation
global_constraints.hpp38–51 binds publics at buffer1 and indexes it directly.
publicsMap does not redirect that offset. stark_info.cpp63,113–123 loads nPublics plus the
ordered public names/lengths; only name/lengths are initialized there, so this
consumer deliberately does not constrain the other retained PolMap fields.

This is a computed supported SOURCE-OBJECT view: source bounds/metadata are
checked internally, never added to Accepted. It does NOT prove that the actual
setup/globalInfo JSON producer materializes this supported publicsMap or links
its names/lengths to the compiled PIL public symbols; that exact native setup
and public-opening realization remains missing. In particular metadata labels
are not an authentication certificate or a verifier soundness theorem. -/
namespace ZiskFv.AirsClean.SourcePublicVerifier

open Goldilocks Air.Flat
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource.Native
open ZiskFv.Channels.OperationBus

inductive Unsupported where
  | missingSetup | differentPublicCount | truncatedPublicBuffer
  deriving DecidableEq, Repr

/-- Checked source metadata and bounds ONLY. The68vector is computed below,
not stored as a second freely chosen source image. -/
structure View {source : SourceObject FGL} (resolved : ResolvedOccurrence source) (mode : Bool) where
  setup : NativeSetup
  sameSetup : resolved.setup? = some setup
  sourceCount : setup.nPublics = 68
  inputBound : 68 ≤ (resolved.params mode).publicInputs.size

def construct? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) : Except Unsupported (View resolved mode) :=
  match hs : resolved.setup? with
  | none => .error .missingSetup
  | some setup =>
    if hn : setup.nPublics = 68 then
      if hb : 68 ≤ (resolved.params mode).publicInputs.size then
        .ok ⟨setup, hs, hn, hb⟩
      else .error .truncatedPublicBuffer
    else .error .differentPublicCount

namespace View
variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source} {mode : Bool}

/-- Native public metadata is retained from the exact selected setup. It does
not redirect PublicValue indices; no guessed map length/name/rank validator is
imposed on the source. Its materialization from the setup JSON remains open. -/
theorem selected_public_map (view : View resolved mode) :
    resolved.setup?.map NativeSetup.publicsMap = some view.setup.publicsMap := by
  rw [view.sameSetup]
  rfl

def publicIO (view : View resolved mode) : PublicIo.PublicIO FGL :=
  Vector.ofFn fun index =>
    (resolved.params mode).publicInputs[index.val]'(by have hb := view.inputBound; omega)

/-- Every coordinate agrees with the actual flat PublicValue-id source-buffer
access. Metadata names are not used as authentication or numerical offsets. -/
theorem every_public_value (view : View resolved mode) (index : Fin 68) :
    RawSource.readWord? (resolved.params mode) .publicInput index.val = some (view.publicIO[index.val]) := by
  have hi : index.val < (resolved.params mode).publicInputs.size := by
    have hb := view.inputBound; omega
  simp [RawSource.readWord?, RawSource.buffer?, publicIO, hi]

/-- One shared global vector, including the four ROM-root cells, is retained.
There is no auxiliary ROM-root/public-output vector to identify later. -/
theorem whole_global_projection (view : View resolved mode) (index : Fin 68) :
    view.publicIO[index.val] = source.globals.publicInputs[index.val]'(by
      have hb := view.inputBound
      change 68 ≤ source.globals.publicInputs.size at hb
      omega) := by
  simp only [publicIO, Vector.getElem_ofFn]
  rfl

theorem same_original_buffer (view : View resolved mode) :
    (resolved.params mode).publicInputs = source.globals.publicInputs ∧
    (∀ index : Fin 68, RawSource.readWord? (resolved.params mode) .publicInput index.val =
      some (view.publicIO[index.val])) := ⟨rfl, view.every_public_value⟩

theorem all_rom_and_input_cells (view : View resolved mode) :
    (∀ index : Fin 4, PublicIo.romRootCell view.publicIO index =
      source.globals.publicInputs[index.val]'(by
        have hb := view.inputBound
        change 68 ≤ source.globals.publicInputs.size at hb
        omega)) ∧
    (∀ index : PublicIo.CellIndex, PublicIo.inputCell view.publicIO index =
      source.globals.publicInputs[4 + index.val]'(by
        have hb := view.inputBound
        change 68 ≤ source.globals.publicInputs.size at hb
        omega)) := by
  constructor
  · intro index
    exact view.whole_global_projection ⟨index.val, by omega⟩
  · intro index
    exact view.whole_global_projection ⟨4 + index.val, by omega⟩

/-- The actual verifier component's operations are evaluated on a Clean
fromInput environment formed ONLY from this computed source vector. ProverData
is universally quantified: no unused witness/environment equality is promised. -/
noncomputable def cleanInteractions (view : View resolved mode) (data : ProverData FGL) : List (Interaction FGL) :=
  PublicIo.verifierComponent.operations.interactionValuesWith OpBusChannel.toRaw
    (Environment.fromInput view.publicIO data)

theorem actual_clean_operations (view : View resolved mode) (data : ProverData FGL) :
    view.cleanInteractions data = PublicIo.interactions view.publicIO := by
  rw [cleanInteractions, PublicIo.verifierComponent_interactionValuesWith]
  change PublicIo.interactions (eval (Environment.fromInput view.publicIO data)
    (varFromOffset PublicIo.PublicIO 0)) = PublicIo.interactions view.publicIO
  rw [ProvableType.eval_fromInput_varFromOffset_zero]

/-- All32 source-indexed unit messages in source order, no unconstrained rows. -/
theorem ordered_positive_unit_emissions (view : View resolved mode) (data : ProverData FGL) :
    view.cleanInteractions data = (List.finRange 32).map
      (fun index => PublicIo.interaction 1 (PublicIo.message view.publicIO index)) ∧
    (view.cleanInteractions data).length = 32 ∧
    (view.cleanInteractions data).Nodup ∧
    (∀ interaction ∈ view.cleanInteractions data, interaction.mult = 1) := by
  simp only [view.actual_clean_operations data]
  refine ⟨rfl, PublicIo.interactions_length _, PublicIo.interactions_nodup _, ?_⟩
  intro interaction hmem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hmem
  rfl

/-- Reuse the independent compiled GLOBAL/PIOP source weld, including the
positive omitted-denominator numerator sign and ALL11 actual Clean slots.
No new hand-transcribed public emission equation or stronger limb rule. -/
theorem compiled_source_emission (view : View resolved mode) (index : PublicIo.WordIndex) :
    ((PublicIo.sourceEmission index).slots ++
      List.replicate (Extraction.PublicIo.operationArity - 7) (Extraction.PublicIo.Expr.constant 0)).mapM
        (PublicIo.sourceToClean (ProvableType.const view.publicIO)) =
      some (PublicIo.opBusSlots (PublicIo.messageExpr (ProvableType.const view.publicIO) index)) ∧
    (PublicIo.sourceEmission index).bus = .constant 5000 ∧
    (PublicIo.sourceEmission index).proves = 1 ∧
    (PublicIo.sourceEmission index).multiplicity = .constant 1 ∧
    Extraction.PublicIo.normalize
      (Extraction.PublicIo.sourceDenominators[(PublicIo.sourceEmission index).termIndex]!) =
      .add (Extraction.PublicIo.mix (PublicIo.sourceEmission index).bus (.challenge 2 0)
        (PublicIo.sourceEmission index).slots) (.challenge 2 1) ∧
    Extraction.PublicIo.flattenMul
      (Extraction.PublicIo.sourceTerms[(PublicIo.sourceEmission index).termIndex]!) =
      Extraction.PublicIo.sourceDenominators.eraseIdx (PublicIo.sourceEmission index).termIndex := by
  have shape := PublicIo.source_emission_shape index
  have linked := PublicIo.source_emission_global_link index
  exact ⟨PublicIo.source_slot_interpretation (ProvableType.const view.publicIO) index,
    shape.1, shape.2.2.1, shape.2.2.2.1, linked.1, linked.2⟩

/-- Whole11-slot concrete message from the same original public buffer. All
limbs are arbitrary FGL; there is no hidden32bit source range assumption. -/
theorem concrete_source_slots (view : View resolved mode) (index : PublicIo.WordIndex) :
    PublicIo.opBusSlots (PublicIo.message view.publicIO index) =
      [(48 : FGL), (index.val : FGL), 0,
       view.publicIO[4 + 2 * index.val], view.publicIO[4 + (2 * index.val + 1)],
       view.publicIO[4 + 2 * index.val], view.publicIO[4 + (2 * index.val + 1)],
       0, 0, 0, 0] := rfl

/-- Source-defined finite multiplicity survives equal output words: public
indices, not limb-value distinctness, make the32 tuples noncolliding. -/
theorem exact_source_multiplicity (view : View resolved mode) (index : PublicIo.WordIndex) :
    balanceOf (PublicIo.interactions view.publicIO)
      (PublicIo.interaction 1 (PublicIo.message view.publicIO index)).msg = 1 ∧
    (PublicIo.interactions view.publicIO).length = Extraction.PublicIo.publicEmissions.length :=
  ⟨PublicIo.interactions_balanceOf _ index, (PublicIo.source_emission_count _).1⟩

/-- Both source Params modes select the same globals. These are computed views,
not two public vectors plus a caller-supplied equality certificate. -/
theorem both_modes (cpu : View resolved false) (proof : View resolved true) :
    cpu.publicIO = proof.publicIO := by
  apply Vector.ext
  intro index hindex
  rfl

/-- Joint binding with the ACTUAL shared Main reader: one source, occurrence,
Params mode and public vector; native38, AIR8 and GROUP3 are not sidecars. This
is NOT a theorem that an arbitrary Accepted/Main/Sail witness is that source. -/
theorem joint_main_source (view : View resolved mode) {row : Nat}
    (main : PublicIoMainNativeTrace.View resolved mode row) :
    (∀ index : Fin 68, RawSource.readWord? (resolved.params mode) .publicInput index.val =
      some (view.publicIO[index.val])) ∧
    (∀ column : Fin 38, NativeTraceCells.cell? .main resolved mode row column.val =
      some (main.cell column)) ∧
    NativeValuesLayout.mainWords? (resolved.params mode) = some main.airVector ∧
    NativeValuesLayout.groupWords? .main (resolved.params mode) = some main.groupVector :=
  ⟨view.every_public_value,
   main.all_native_cells, main.actual_air_projection, main.actual_group_projection⟩

end View
end ZiskFv.AirsClean.SourcePublicVerifier
