import ZiskFv.AirsClean.ByteMemoryPhysicalRows
import ZiskFv.AirsClean.ByteMemoryCompiledPadding

/-!
Read-capable byte-memory Direct equations on one source occurrence.

PIL b6327450 mem/pil/mem_align_byte.pil:106–118 supplies AIR0 padding_size,
AIR1/2 im_direct, and stage-2 alpha/gamma. Scalar AIR0 embeds in coefficient
zero; AIR1/2 and both challenges retain all three native coefficients. Cubic
multiplication reuses Mem.Stage2.Ext3, not coordinate-wise multiplication or
an invented Field instance. No total Extraction.Circuit is fabricated.

The actual normal generated source-kind-preserving ASTs are interpreted below.
The result is equated to residuals formed from EVERY payload cell and signed
multiplicity of the ACTUAL compiled instance operations. These are residual
identities, not proofs that equations hold, numeric gsum, balance, accepted
source images or production construction. Metadata matching still does not
prove native compiled r.id/PIL correlation or live snapshot/ABI agreement.
-/
namespace ZiskFv.AirsClean.ByteMemoryDirectSource

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Mem.Stage2 (Ext3 extensionWords? literal?)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- Keep source kind/id and native map addressing distinct. -/
structure Origin where
  kind : FieldBufferKind
  sourceStage : Nat
  sourceIndex : Nat
  nativeMapId : Nat
  metadata : PolMap
  wordOffset : Nat

structure Cell where
  private mk ::
  origin : Origin
  value : Ext3 FGL

/-- Source AIR1/2 are extension inverses in the AIR buffer, not aux/GROUP.
The pinned ff0e `stark_info.cpp:125–150` populates AIR entries with only
name/stage, in order: `PolMap.dim` is NOT source metadata for this map.
`airValueWords?` uses the stage-dependent ordered-prefix native addressing;
`extensionWords?` retains all three bounded words. Compiled operand r.dim
and PIL symbol-rank correlation remain separate, unproved obligations. -/
def inverse? (resolved : ResolvedOccurrence source) (index : Fin 2) : Option Cell := do
  let setup ← resolved.setup?
  let id := index.val + 1
  let entry ← setup.airValuesMap[id]?
  if entry.stage = 2 then
    let value ← extensionWords? (resolved.airValueWords? false id)
    return ⟨⟨.airValue, 2, id, id, entry, valueOffset setup.airValuesMap id⟩, value⟩
  else none

/-- The actual selected map index determines 3*r.id addressing. The source
stage/id match is retained; equality to a native compiled operand is not assumed. -/
def challenge? (resolved : ResolvedOccurrence source) (index : Fin 2) : Option Cell := do
  let setup ← resolved.setup?
  let mapId ← setup.challengesMap.findIdx? fun entry =>
    entry.stage == 2 && entry.stageId == index.val && entry.dim == 3
  let entry ← setup.challengesMap[mapId]?
  if entry.stage = 2 ∧ entry.stageId = index.val ∧ entry.dim = 3 then
    let value ← extensionWords?
      (readBlock? (resolved.params false) .challenge (3 * mapId) 3)
    return ⟨⟨.challenge, 2, index.val, mapId, entry, 3 * mapId⟩, value⟩
  else none

/-- Only the factory constructs this same-source view. Padding is NOT a new
scalar field: it remains the physical descriptor's selected raw AIR0. -/
structure Projection (physical : ByteMemoryPhysicalRows.Rows resolved) where
  private mk ::
  paddingOrigin : Origin
  alignedInverse : Cell
  byteInverse : Cell
  alpha : Cell
  gamma : Cell

/-- All needed extension blocks are read, even when raw padding is zero.
Missing maps/words or incorrect stages fail, rather than supplying a zero cell.
AIR dimensions are not fabricated; challenge stage/id/dim checks are native. -/
def fromPhysical? (physical : ByteMemoryPhysicalRows.Rows resolved) :
    Option (Projection physical) := do
  let entry ← physical.setup.airValuesMap[0]?
  if entry.stage = 1 then
    let aligned ← inverse? resolved 0
    let byte ← inverse? resolved 1
    let alpha ← challenge? resolved 0
    let gamma ← challenge? resolved 1
    return ⟨⟨.airValue, 1, 0, 0, entry, 0⟩, aligned, byte, alpha, gamma⟩
  else none

/-- The actual scalar/extension source kinds and array rank are kept separate. -/
theorem actual_source_value_kinds (air : ByteMemoryPhysicalRows.Air) :
    air.schema.symbols.filter (fun symbol => symbol.kind == .airValue) =
      [⟨some 0, some air.airId, air.schema.airName ++ ".padding_size",
        .airValue, some 1, 0, 0, []⟩,
       ⟨some 0, some air.airId, air.schema.airName ++ ".im_direct",
        .airValue, some 2, 1, 1, [2]⟩] := by
  cases air <;> rfl

/-- This is computed from the owning source projection, never supplied to the
native instance as a separate operand record. -/
def operands {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : ByteMemoryCompiledPadding.DirectEquations.Operands :=
  ⟨physical.padding, view.alignedInverse.value, view.byteInverse.value,
    view.alpha.value, view.gamma.value⟩

private def readOnly : ByteMemoryPhysicalRows.Air → Bool
  | .byte => false
  | .readByte => true

def actualResiduals? {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : Option (Vector (Ext3 FGL) 2) :=
  ByteMemoryCompiledPadding.DirectEquations.actualResiduals? (readOnly physical.air) (operands view)

def compiledResiduals? {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (operations : Operations FGL) (env : Environment FGL) :
    Option (Vector (Ext3 FGL) 2) :=
  ByteMemoryCompiledPadding.DirectEquations.compiledResiduals? (operands view) operations env

/-- Actual generated source polynomials equal mixed expressions over the
ACTUAL compiled operations, using the same selected p and extension buffers. -/
theorem actual_residuals_eq_compiled {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (env : Environment FGL) :
    actualResiduals? view = compiledResiduals? view
      ((ByteMemoryCompiledPadding.byteCircuit (.const physical.padding)).operations 0) env := by
  exact ByteMemoryCompiledPadding.DirectEquations.actual_residuals_eq_compiled
    (readOnly physical.air) (operands view) env

/-- All three coefficients of both actual source equations are retained. -/
theorem actual_compiled_all_coefficients {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (env : Environment FGL) (equation : Fin 2)
    (coefficient : Fin 3) :
    (actualResiduals? view).map (fun values => Ext3.coeff values[equation.val] coefficient) =
      (compiledResiduals? view
        ((ByteMemoryCompiledPadding.byteCircuit (.const physical.padding)).operations 0) env).map
          (fun values => Ext3.coeff values[equation.val] coefficient) := by
  rw [actual_residuals_eq_compiled]

end ZiskFv.AirsClean.ByteMemoryDirectSource
