import ZiskFv.AirsClean.ByteMemoryPhysicalRows
import ZiskFv.AirsClean.Mem.Stage2.Literals

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

/-- Source AIR1/2 are extension inverses in the AIR buffer, not aux/GROUP. -/
def inverse? (resolved : ResolvedOccurrence source) (index : Fin 2) : Option Cell := do
  let setup ← resolved.setup?
  let id := index.val + 1
  let entry ← setup.airValuesMap[id]?
  if entry.stage = 2 ∧ entry.dim = 3 then
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

/-- All needed extension blocks are read, even when raw padding is zero. A
missing map/word or wrong stage/dim fails rather than supplying a zero cell. -/
def fromPhysical? (physical : ByteMemoryPhysicalRows.Rows resolved) :
    Option (Projection physical) := do
  let entry ← physical.setup.airValuesMap[0]?
  if entry.stage = 1 ∧ entry.dim = 1 then
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

private def b (value : FGL) : Ext3 FGL := Ext3.ofBase value

/-- Five supported source leaves only. This is not the Mem row decoder and
never conflates AIR/GROUP/aux or interprets an unsupported leaf as zero. -/
def evaluate? {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : Expr → Option (Ext3 FGL)
  | .constant text => literal? text
  | .airValue 0 => some (b physical.padding)
  | .airValue 1 => some view.alignedInverse.value
  | .airValue 2 => some view.byteInverse.value
  | .challenge 2 0 => some view.alpha.value
  | .challenge 2 1 => some view.gamma.value
  | .add left right => return (← evaluate? view left) + (← evaluate? view right)
  | .sub left right => return (← evaluate? view left) - (← evaluate? view right)
  | .mul left right => return (← evaluate? view left) * (← evaluate? view right)
  | .neg value => return -(← evaluate? view value)
  | _ => none

/-- Actual generated expressions, not a re-packed Direct-template roster. -/
def actualExpressions (air : ByteMemoryPhysicalRows.Air) : Vector Expr 2 :=
  match air with
  | .byte => #v[constraint_MemAlignByte_13, constraint_MemAlignByte_14]
  | .readByte => #v[constraint_MemAlignReadByte_7, constraint_MemAlignReadByte_8]

def actualResiduals? {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : Option (Vector (Ext3 FGL) 2) := do
  return #v[← evaluate? view (actualExpressions physical.air)[0],
    ← evaluate? view (actualExpressions physical.air)[1]]

/-- Independently fixed op=1, width=8, bus=10, positive raw p. -/
def alignedExpected {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : Ext3 FGL :=
  view.alignedInverse.value *
      (((((b 8 * view.alpha.value) * view.alpha.value) * view.alpha.value + b 1) *
        view.alpha.value + b 10) + view.gamma.value) - b physical.padding

/-- Independently fixed op=1, width=1, bus=10, negative raw p. -/
def byteExpected {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : Ext3 FGL :=
  view.byteInverse.value *
      ((((view.alpha.value * view.alpha.value) * view.alpha.value + b 1) *
        view.alpha.value + b 10) + view.gamma.value) - (b 0 - b physical.padding)

/-- Actual normal AST interpretation, including all three mixed-product
coefficients. No equation-satisfaction hypothesis or conclusion occurs here. -/
theorem actual_residuals_eq_expected {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) :
    actualResiduals? view = some #v[alignedExpected view, byteExpected view] := by
  cases hair : physical.air <;>
    simp [actualResiduals?, actualExpressions, hair, evaluate?,
      constraint_MemAlignByte_13, constraint_MemAlignByte_14,
      constraint_MemAlignReadByte_7, constraint_MemAlignReadByte_8,
      alignedExpected, byteExpected, b]

/-- Horner encoding of ALL six evaluated tuple cells, followed by source bus10.
Channel/arity/length are checked before interpreting the concrete interaction. -/
def interactionResidual? (inverse alpha gamma : Ext3 FGL)
    (interaction : Interaction FGL) : Option (Ext3 FGL) := do
  if interaction.channel.name = "MemoryBus" ∧ interaction.channel.arity = 6 ∧
      interaction.msg.size = 6 then
    let operation ← interaction.msg[0]?
    let pointer ← interaction.msg[1]?
    let timestamp ← interaction.msg[2]?
    let width ← interaction.msg[3]?
    let value0 ← interaction.msg[4]?
    let value1 ← interaction.msg[5]?
    let h0 := b value1 * alpha + b value0
    let h1 := h0 * alpha + b width
    let h2 := h1 * alpha + b timestamp
    let h3 := h2 * alpha + b pointer
    let h4 := h3 * alpha + b operation
    return inverse * ((h4 * alpha + b 10) + gamma) - b interaction.mult
  else none

def batchResiduals? {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) : List (Interaction FGL) → Option (Vector (Ext3 FGL) 2)
  | [aligned, byte] => do
    return #v[← interactionResidual? view.alignedInverse.value view.alpha.value view.gamma.value aligned,
      ← interactionResidual? view.byteInverse.value view.alpha.value view.gamma.value byte]
  | _ => none

/-- Operations are observed, not reconstructed from a caller tuple packet. -/
def compiledResiduals? {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (operations : Operations FGL) (env : Environment FGL) :
    Option (Vector (Ext3 FGL) 2) :=
  batchResiduals? view (operations.interactionValues env)

private theorem block_zero_mul (value : Ext3 FGL) : (0 : Ext3 FGL) * value = 0 := by
  rw [Ext3.mul_eq_convolutionMul]
  apply Ext3.ext <;> simp [Ext3.convolutionMul]

private theorem block_zero_add (value : Ext3 FGL) : (0 : Ext3 FGL) + value = value := by
  cases value
  apply Ext3.ext <;> simp [HAdd.hAdd, Add.add]

private theorem block_add_zero (value : Ext3 FGL) : value + (0 : Ext3 FGL) = value := by
  cases value
  apply Ext3.ext <;> simp [HAdd.hAdd, Add.add]

private theorem block_one_mul (value : Ext3 FGL) : (1 : Ext3 FGL) * value = value := by
  change Ext3.ofBase (1 : FGL) * value = value
  rw [Ext3.ofBase_mul_block]
  cases value
  apply Ext3.ext <;> simp [HSMul.hSMul, SMul.smul]

private theorem block_zero_sub (value : Ext3 FGL) : (0 : Ext3 FGL) - value = -value := by
  cases value
  apply Ext3.ext <;> simp [Sub.sub, Neg.neg]

/-- The residual uses actual compiled message fields and actual signed
multiplicities, not only a parallel independent local tuple definition. -/
theorem compiled_residuals_eq_expected {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (env : Environment FGL) :
    compiledResiduals? view
        ((ByteMemoryCompiledPadding.byteCircuit (.const physical.padding)).operations 0) env =
      some #v[alignedExpected view, byteExpected view] := by
  unfold compiledResiduals?
  change batchResiduals? view (ByteMemoryCompiledPadding.byteValues physical.padding env) = _
  rw [ByteMemoryCompiledPadding.byte_compiled]
  simp [batchResiduals?, interactionResidual?, ByteMemoryCompiledPadding.zeroLoadValue,
    Channel.pushedIfValue, Channel.toRaw, MemBusChannel,
    alignedExpected, byteExpected, b, Ext3.ofBase_zero,
    block_zero_mul, block_zero_add, block_add_zero, block_one_mul, block_zero_sub]

/-- Load-bearing actual-source/actual-compiled residual identity. Environments
are universally quantified observers; no caller environment equality is needed. -/
theorem actual_residuals_eq_compiled {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (env : Environment FGL) :
    actualResiduals? view = compiledResiduals? view
      ((ByteMemoryCompiledPadding.byteCircuit (.const physical.padding)).operations 0) env := by
  rw [actual_residuals_eq_expected, compiled_residuals_eq_expected]

/-- Every coefficient of each actual residual is retained by the linkage. -/
theorem actual_compiled_all_coefficients {physical : ByteMemoryPhysicalRows.Rows resolved}
    (view : Projection physical) (env : Environment FGL) (equation : Fin 2)
    (coefficient : Fin 3) :
    (actualResiduals? view).map (fun values => Ext3.coeff values[equation.val] coefficient) =
      (compiledResiduals? view
        ((ByteMemoryCompiledPadding.byteCircuit (.const physical.padding)).operations 0) env).map
          (fun values => Ext3.coeff values[equation.val] coefficient) := by
  rw [actual_residuals_eq_compiled]

end ZiskFv.AirsClean.ByteMemoryDirectSource
