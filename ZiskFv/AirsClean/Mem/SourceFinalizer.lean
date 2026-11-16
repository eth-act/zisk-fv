import ZiskFv.AirsClean.Mem.SourceFinalizerEquation
import ZiskFv.AirsClean.MemAlignWriteByte.SourceInstance

/-! Same-source native Mem c33 coordinate projection.

All reads use one source-owned ResolvedOccurrence, its registry-selected
post-setup maps and its final slot's Params buffers. No decoded values, source
Context, row equality or validity certificate are additional inputs.

The underlying Native readers currently support CPU/nonextended rows. Missing
slots/maps/words, incompatible dimensions and unsupported profiles remain absent.
This is not live Rust/C++ snapshot authentication, a GPU materialization theorem,
a new accepted-trace validator or a proof that numeric gsum realizes balance.

The metadata-compatible gsum map selection still needs the exact compiled
c33 native operand-id binding and opening-index/rotation binding. Neither
is supplied by a new equality premise. The theorem below proves the source
model's partial coordinate projection, not complete C++ execution equivalence.
-/
namespace ZiskFv.AirsClean.Mem.SourceFinalizer

open Extraction.LookupWiring
open ZiskFv.AirsClean.GsumBoundary (Source)
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

variable {F : Type} {source : SourceObject F}

/-- Extension word width is checked separately from source symbol rank. -/
def extensionWord? (words : Option (Array F)) (coordinate : Fin 3) : Option F := do
  let block ← words
  if block.size = 3 then block[coordinate.val]? else none

def scalarWord? (words : Option (Array F)) : Option F := do
  let block ← words
  if block.size = 1 then block[0]? else none

/-- Every arbitrary three-word block is representable without reducing it to
one field element. This is block constructibility, not c33 satisfaction. -/
theorem extensionWord_constructible (values : Fin 3 → F) (coordinate : Fin 3) :
    extensionWord? (some (Array.ofFn values)) coordinate = some (values coordinate) := by
  simp [extensionWord?, coordinate.isLt]

theorem extensionWord_rejects_scalar (value : F) (coordinate : Fin 3) :
    extensionWord? (some #[value]) coordinate = none := rfl

theorem extensionWord_rejects_missing (coordinate : Fin 3) :
    extensionWord? (none : Option (Array F)) coordinate = none := rfl

/-- Setup selection follows the registry; mutable slot labels are not asserted
identical and registry order is not interpreted as a semantic segment id. -/
def memOccurrence (resolved : ResolvedOccurrence source) : Bool :=
  resolved.registryEntry.airgroupId == 0 && resolved.registryEntry.airId == 14

def airCoordinate? (resolved : ResolvedOccurrence source)
    (index : Nat) (coordinate : Fin 3) : Option F := do
  let setup ← resolved.setup?
  let entry ← setup.airValuesMap[index]?
  if entry.stage = 2 then
    extensionWord? (resolved.airValueWords? false index) coordinate
  else none

def groupCoordinate? (resolved : ResolvedOccurrence source)
    (index : Nat) (coordinate : Fin 3) : Option F := do
  let setup ← resolved.setup?
  let entry ← setup.airgroupValuesMap[index]?
  if entry.stage = 2 then
    extensionWord? (resolved.airGroupValueWords? false index) coordinate
  else none

/-- Resolve a native map entry using the source gsum name/stage/stageId and
extension dimension. Neither source column zero nor map index zero is treated
as a native word offset. The actual selected map's stagePos is retained. -/
def gsumMapId? (setup : NativeSetup) : Option Nat :=
  setup.cmPolsMap.findIdx? fun entry =>
    entry.name == "gsum" && entry.stage == 2 && entry.stageId == 0 && entry.dim == 3

def runningCoordinate? (resolved : ResolvedOccurrence source)
    (row : Nat) (coordinate : Fin 3) : Option F := do
  let setup ← resolved.setup?
  let mapId ← gsumMapId? setup
  extensionWord? (resolved.cmAuxWords? false mapId row 0) coordinate

/-- c33's supported source cells, not a total arbitrary-polynomial decoder.
Every field comes from the SAME resolved occurrence; all other witness cells
stay unsupported instead of receiving invented zero values. -/
def coordinateSource? (resolved : ResolvedOccurrence source)
    (row : Nat) (coordinate : Fin 3) : Option (Source (Option F)) :=
  if memOccurrence resolved then
    some {
      witness := fun stage column offset =>
        if stage = 2 ∧ column = 0 ∧ offset = 0 then
          runningCoordinate? resolved row coordinate
        else none
      fixed := fun column offset =>
        scalarWord? (resolved.fixedWords? false column row offset)
      airValue := fun index => airCoordinate? resolved index coordinate
      airGroupValue := fun index => groupCoordinate? resolved index coordinate }
  else none

variable [Field F]

/-- Evaluation of the ACTUAL normally generated source-kind-preserving c33. -/
def evalCoordinate? (resolved : ResolvedOccurrence source)
    (row : Nat) (coordinate : Fin 3) : Option F := do
  let cells ← coordinateSource? resolved row coordinate
  evalLinearCoordinate? cells constraint_Mem_33

/-- Independently fixed six-term equation on the same native buffers. No
selector, kind, offset or term roster is read back from the generated link. -/
def expectedCoordinate? (resolved : ResolvedOccurrence source)
    (row : Nat) (coordinate : Fin 3) : Option F :=
  if memOccurrence resolved then do
    let selector ← scalarWord? (resolved.fixedWords? false 1 row 1)
    let contribution ← groupCoordinate? resolved 0 coordinate
    let running ← runningCoordinate? resolved row coordinate
    let direct0 ← airCoordinate? resolved 15 coordinate
    let direct1 ← airCoordinate? resolved 16 coordinate
    let direct2 ← airCoordinate? resolved 17 coordinate
    let direct3 ← airCoordinate? resolved 18 coordinate
    let direct4 ← airCoordinate? resolved 19 coordinate
    let direct5 ← airCoordinate? resolved 20 coordinate
    return selector * (contribution - running -
      (((((direct0 + direct1) + direct2) + direct3) + direct4) + direct5))
  else none

theorem native_coordinate_eq_expected (resolved : ResolvedOccurrence source)
    (row : Nat) (coordinate : Fin 3) :
    evalCoordinate? resolved row coordinate = expectedCoordinate? resolved row coordinate := by
  by_cases hmem : memOccurrence resolved = true <;>
    simp [evalCoordinate?, coordinateSource?, expectedCoordinate?, hmem, partial_coordinate_equation]

/-- All three equations, including failed native reads as failure, not zero. -/
def Holds (resolved : ResolvedOccurrence source) (row : Nat) : Prop :=
  ∀ coordinate, evalCoordinate? resolved row coordinate = some 0

theorem native_three_coordinate_iff (resolved : ResolvedOccurrence source) (row : Nat) :
    Holds resolved row ↔
      ∀ coordinate, expectedCoordinate? resolved row coordinate = some 0 := by
  simp only [Holds, native_coordinate_eq_expected]

/-- Shared-slot ownership, not an independent GROUP certificate. -/
theorem same_source_buffers (resolved : ResolvedOccurrence source) :
    (resolved.params false).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params false).airvalues = resolved.slotData.airvalues ∧
    (resolved.params false).auxTrace =
      (if resolved.slotData.auxTrace.isEmpty then none else some resolved.slotData.auxTrace) ∧
    resolved.setup? = source.setupRepository[
      (resolved.registryEntry.airgroupId, resolved.registryEntry.airId)]? :=
  ⟨rfl, rfl, rfl, rfl⟩

end ZiskFv.AirsClean.Mem.SourceFinalizer
