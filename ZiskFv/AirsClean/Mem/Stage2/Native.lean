import ZiskFv.AirsClean.Mem.Stage2.Cubic
import ZiskFv.AirsClean.Mem.Stage2.Equations
import ZiskFv.AirsClean.Mem.SourceFinalizer

/-! Actual polynomial fragment of the remaining Mem stage-2 equations.

Every leaf is read from ONE source-owned ResolvedOccurrence and its selected
post-setup metadata/Params. Base cells embed as (value,0,0); extension cells
retain all three words. Multiplication is the pinned cubic source operation,
not pointwise multiplication and not a postulated Field structure.

This partial model does not bind native compiled operand/opening ids or
machine arithmetic to the metadata match. Packed stage1, GPU/verifier layouts
and live buffer/ABI materialization remain explicit representation gaps, not
Root acceptance exclusions. No existing validator or source-validity caller
premise is added. c33 reuses its frozen linear source equation separately.
-/
namespace ZiskFv.AirsClean.Mem.Stage2

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

variable {source : SourceObject FGL}

/-- Exact source extension block; missing and malformed blocks fail. -/
def extensionWords? (words : Option (Array FGL)) : Option (Ext3 FGL) := do
  let block ← words
  if block.size = 3 then
    return ⟨← block[0]?, ← block[1]?, ← block[2]?⟩
  else none

def baseWords? (words : Option (Array FGL)) : Option (Ext3 FGL) := do
  return Ext3.ofBase (← SourceFinalizer.scalarWord? words)

/-- Same existing general decimal decoder as RawSource, without a whitelist or
zero fallback. Casting is in the base Goldilocks field before embedding. -/
def literal? (text : String) : Option (Ext3 FGL) := do
  return Ext3.ofBase ((← text.toNat?) : FGL)

/-- Native map matching is a bounded model projection, not a theorem that the
compiled expression's r.id selects this entry. gsum shares the frozen match. -/
def witnessMapId? (setup : NativeSetup) (stage column : Nat) : Option Nat :=
  if stage = 2 ∧ column = 0 then SourceFinalizer.gsumMapId? setup
  else setup.cmPolsMap.findIdx? fun entry =>
    entry.stage == stage && entry.stageId == column &&
      entry.dim == (if stage == 1 then 1 else 3)

/-- Phase1 Mem has thirteen scalar columns; phase2 has three extension columns.
The native reader deliberately does not guess how to unpack packed stage1. -/
def witness? (resolved : ResolvedOccurrence source) (row stage column : Nat)
    (rotation : Int) : Option (Ext3 FGL) := do
  if (stage = 1 ∧ column < 13) ∨ (stage = 2 ∧ column < 3) then
    let setup ← resolved.setup?
    let mapId ← witnessMapId? setup stage column
    if stage = 1 then baseWords? (resolved.cmWords? false mapId row rotation)
    else extensionWords? (resolved.cmWords? false mapId row rotation)
  else none

/-- Native fixed operand uses its direct source column id, not a const-map
stagePos. The source Mem fixed roster has SEGMENT_L1 and __L1__. -/
def fixed? (resolved : ResolvedOccurrence source) (row column : Nat)
    (rotation : Int) : Option (Ext3 FGL) :=
  if column < 2 then baseWords? (resolved.fixedWords? false column row rotation)
  else none

/-- Actual AIR15..20 are extension inverses; AIR0..14 remain base scalars.
A metadata stage mismatch is unsupported decoding, never a source-kind cast. -/
def airValue? (resolved : ResolvedOccurrence source) (index : Nat) : Option (Ext3 FGL) := do
  if index < 21 then
    let setup ← resolved.setup?
    let entry ← setup.airValuesMap[index]?
    let stage := if index < 15 then 1 else 2
    if entry.stage = stage then
      if stage = 1 then baseWords? (resolved.airValueWords? false index)
      else extensionWords? (resolved.airValueWords? false index)
    else none
  else none

/-- GROUP result zero is a different buffer and source kind from AIR segment0. -/
def groupValue? (resolved : ResolvedOccurrence source) (index : Nat) : Option (Ext3 FGL) := do
  if index = 0 then
    let setup ← resolved.setup?
    let entry ← setup.airgroupValuesMap[index]?
    if entry.stage = 2 then extensionWords? (resolved.airGroupValueWords? false index)
    else none
  else none

/-- Challenge stage/index is not a guessed word offset. Native C++
expressions_info.cpp545–552 uses 3*r.id in Params.challenges, while
stark_info.cpp103–110 preserves stage/stageId/dim in the actual ordered map.
The compiled r.id/PIL binding is still unproved, just as for witness operands. -/
def challenge? (resolved : ResolvedOccurrence source) (stage index : Nat) :
    Option (Ext3 FGL) := do
  if stage = 2 ∧ index < 2 then
    let setup ← resolved.setup?
    let mapId ← setup.challengesMap.findIdx? fun entry =>
      entry.stage == stage && entry.stageId == index && entry.dim == 3
    extensionWords? (readBlock? (resolved.params false) .challenge (3 * mapId) 3)
  else none

/-- Polynomial syntax only. No inversion, arbitrary callbacks, opaque aliases,
missing-cell defaults or Field structure on Ext3 occur in this evaluator. -/
def polynomial? (resolved : ResolvedOccurrence source) (row : Nat) :
    Expr → Option (Ext3 FGL)
  | .constant text => literal? text
  | .witness stage column rotation => witness? resolved row stage column rotation
  | .fixed column rotation => fixed? resolved row column rotation
  | .challenge stage index => challenge? resolved stage index
  | .airValue index => airValue? resolved index
  | .airGroupValue index => groupValue? resolved index
  | .add left right => return (← polynomial? resolved row left) + (← polynomial? resolved row right)
  | .sub left right => return (← polynomial? resolved row left) - (← polynomial? resolved row right)
  | .mul left right => return (← polynomial? resolved row left) * (← polynomial? resolved row right)
  | .neg value => return -(← polynomial? resolved row value)
  | .opaque _ _ => none

/-- This source-specific circuit is scoped by registry labels, not mutable slot
labels. It does not claim any native capture is already an accepted trace. -/
def evaluate? (resolved : ResolvedOccurrence source) (row : Nat) (expr : Expr) :
    Option (Ext3 FGL) :=
  if SourceFinalizer.memOccurrence resolved then polynomial? resolved row expr else none

/-- Nine actual polynomial equations on all three coefficients. All source
reads are performed; a zero selector is not a missing-cell fallback. -/
def LocalCircuit (resolved : ResolvedOccurrence source) (row : Nat) : Prop :=
  ∀ equation : Fin 9, evaluate? resolved row (actualNonlinear equation) = some 0

def ExpectedCircuit (resolved : ResolvedOccurrence source) (row : Nat) : Prop :=
  ∀ equation : Fin 9, evaluate? resolved row (expectedNonlinear equation) = some 0

theorem native_polynomial_source_correspondence (resolved : ResolvedOccurrence source)
    (row : Nat) (equation : Fin 9) :
    evaluate? resolved row (actualNonlinear equation) =
      evaluate? resolved row (expectedNonlinear equation) := by
  rw [actualNonlinear_eq_expectedNonlinear]

theorem localCircuit_iff_expected (resolved : ResolvedOccurrence source) (row : Nat) :
    LocalCircuit resolved row ↔ ExpectedCircuit resolved row := by
  simp only [LocalCircuit, ExpectedCircuit, native_polynomial_source_correspondence]

/-- Existing c33 remains the already checked linear boundary; this conjunction
is ten equations, not a numeric logUp or provider-composition theorem. -/
def WithFinalizer (resolved : ResolvedOccurrence source) (row : Nat) : Prop :=
  LocalCircuit resolved row ∧ SourceFinalizer.Holds resolved row

theorem source_buffers_are_shared (resolved : ResolvedOccurrence source) :
    (resolved.params false).trace = resolved.slotData.trace ∧
    (resolved.params false).airvalues = resolved.slotData.airvalues ∧
    (resolved.params false).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params false).challenges = source.globals.challenges :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem extensionWords_constructible (value : Ext3 FGL) :
    extensionWords? (some #[value.c0, value.c1, value.c2]) = some value := by
  cases value
  rfl

theorem scalar_is_embedded_only_at_zero (value : FGL) :
    baseWords? (some #[value]) = some ⟨value, 0, 0⟩ := rfl

theorem reject_missing_or_opaque (resolved : ResolvedOccurrence source) (row : Nat) :
    extensionWords? none = none ∧
    polynomial? resolved row (.opaque "unsupported" "payload") = none := ⟨rfl, rfl⟩

end ZiskFv.AirsClean.Mem.Stage2
