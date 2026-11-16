import Extraction.LookupWiring

/-! Standalone snapshots of the pinned proofman's raw source objects.

Source: pil2-proofman ff0e33a9, common/src/air_instance.rs and proof_ctx.rs
(add_air_instance and get_air_instance_params), plus distribution_ctx.rs.
This is NOT an AcceptedZiskTrace field, a native-array authentication theorem,
or a construction from the existing Flat witness. Array shape, packing,
custom-commit strides, extension-field decoding and cross-process gathering
are not inferred from merely constructing this raw data type.

Registry indices identify final source occurrences, never semantic segments.
AIR values and AIR-group values retain distinct buffers and symbol kinds.
All partial reads return None on missing/unsupported data; no zero default is
used. Symbol rank/lengths are not confused with native extension word width. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.RawSource

open Extraction.LookupWiring

structure InstanceMeta where
  airgroupId : Nat
  airId : Nat
  numRows : Nat
  nColsTrace : Nat
  sharedBuffer : Bool
  isPacked : Bool
  streamId : UInt64

/-- The actual separate buffers of one final AirInstance image. Trace retains
native UInt64 words before field reduction, including packed/noncanonical bits.
Actual Rust/FFI memory-to-image materialization is not proved by this type. -/
structure Instance (F : Type) where
  metadata : InstanceMeta
  trace : Array UInt64
  auxTrace : Array F
  customCommitsFixed : Array F
  airgroupValues : Array F
  airvalues : Array F
  challenges : Array F
  evals : Array F
  fixed : Array F

structure RegistryEntry where
  airgroupId : Nat
  airId : Nat
  table : Bool
  shared : Bool
  nChunks : Nat
  weight : UInt64

/-- Distribution metadata is retained, not reinterpreted as source chronology.
In particular a local process may not store every globally registered slot. -/
structure Registry where
  instances : Array RegistryEntry
  processId : Nat
  processInstances : Array Nat
  workerInstances : Array Nat
  skippedProcessInstances : Array Nat
  instanceProcess : Array (Int × Nat)
  instancesCalculated : Array Bool

structure Globals (F : Type) where
  publicInputs : Array F
  proofValues : Array F
  challenges : Array F
  globalChallenge : Array F

/-- Compiler/setup metadata is separate from mutable instance buffers.
The generated symbol catalog alone does not prove these stage widths or a
native packed/custom-array address calculation. -/
structure CompiledLayout where
  schema : SourceSchema.Air
  physicalRows : Nat
  witnessStageWidths : Array Nat
  fixedColumns : Nat
  customStageWidths : Array (Array Nat)
  extensionWordWidth : Nat

structure Context (F : Type) where
  globals : Globals F
  registry : Registry
  slots : Array (Instance F)
  compiledLayouts : Array CompiledLayout

abbrev Occurrence (context : Context F) := Fin context.registry.instances.size

structure OccurrenceKey where
  airgroupId : Nat
  airId : Nat
  globalSlot : Nat
  deriving DecidableEq

def occurrenceKey (context : Context F) (index : Occurrence context) : OccurrenceKey :=
  let entry := context.registry.instances[index.val]
  ⟨entry.airgroupId, entry.airId, index.val⟩

def occurrences (context : Context F) : List (Occurrence context) := List.ofFn id

theorem occurrenceKey_injective (context : Context F) :
    Function.Injective (occurrenceKey context) := by
  intro left right h
  exact Fin.ext (congrArg OccurrenceKey.globalSlot h)

theorem occurrenceKeys_nodup (context : Context F) :
    (List.ofFn (occurrenceKey context)).Nodup :=
  List.nodup_ofFn_ofInjective (occurrenceKey_injective context)

/-- A live registry index selects the same global source slot as ProofCtx.
Absent local/remote data stays absent; MAX_INSTANCES capacity is not enumerated. -/
def instanceAt? (context : Context F) (index : Occurrence context) : Option (Instance F) :=
  context.slots[index.val]?

/-- Models add_air_instance's overwrite, not an append-only event history. -/
def overwriteSlot (context : Context F) (index : Fin context.slots.size)
    (slotData : Instance F) : Context F :=
  { context with slots := context.slots.set index.val slotData }

theorem overwriteSlot_registry (context : Context F) (index : Fin context.slots.size)
    (slotData : Instance F) : (overwriteSlot context index slotData).registry = context.registry := rfl

theorem overwriteSlot_key (context : Context F) (slot : Fin context.slots.size)
    (slotData : Instance F) (index : Occurrence context) :
    occurrenceKey (overwriteSlot context slot slotData) index = occurrenceKey context index := rfl

inductive ChallengeOrigin where
  | fromSlot | fromGlobals
  deriving DecidableEq

/-- Snapshot view of StepsParams's pointer sources. None means a null pointer,
not a zero-filled array. Shared globals occur only once in Context.globals. -/
structure Params (F : Type) where
  trace : Array UInt64
  auxTrace : Option (Array F)
  publicInputs : Array F
  proofValues : Array F
  challenges : Array F
  challengeOrigin : ChallengeOrigin
  airgroupValues : Array F
  airvalues : Array F
  evals : Array F
  xdivxsub : Option (Array F)
  constPols : Option (Array F)
  constTree : Option (Array F)
  customCommitsFixed : Array F

def paramsOf (globals : Globals F) (slotData : Instance F) (genProof : Bool) : Params F :=
  { trace := slotData.trace
    auxTrace := if genProof || slotData.auxTrace.isEmpty then none else some slotData.auxTrace
    publicInputs := globals.publicInputs
    proofValues := globals.proofValues
    challenges := if genProof then slotData.challenges else globals.challenges
    challengeOrigin := if genProof then .fromSlot else .fromGlobals
    airgroupValues := slotData.airgroupValues
    airvalues := slotData.airvalues
    evals := slotData.evals
    xdivxsub := none
    constPols := if genProof then none else some slotData.fixed
    constTree := none
    customCommitsFixed := slotData.customCommitsFixed }

def paramsAt? (context : Context F) (index : Occurrence context) (genProof : Bool) :
    Option (Params F) :=
  (instanceAt? context index).map (fun slotData => paramsOf context.globals slotData genProof)

theorem paramsOf_same_instance (globals : Globals F) (slotData : Instance F) (mode : Bool) :
    (paramsOf globals slotData mode).trace = slotData.trace ∧
    (paramsOf globals slotData mode).airvalues = slotData.airvalues ∧
    (paramsOf globals slotData mode).airgroupValues = slotData.airgroupValues ∧
    (paramsOf globals slotData mode).customCommitsFixed = slotData.customCommitsFixed :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem paramsOf_same_globals (globals : Globals F) (slotData : Instance F) (mode : Bool) :
    (paramsOf globals slotData mode).publicInputs = globals.publicInputs ∧
    (paramsOf globals slotData mode).proofValues = globals.proofValues := ⟨rfl, rfl⟩

theorem paramsOf_proof_mode (globals : Globals F) (slotData : Instance F) :
    (paramsOf globals slotData true).auxTrace = none ∧
    (paramsOf globals slotData true).constPols = none ∧
    (paramsOf globals slotData true).challenges = slotData.challenges := ⟨rfl, rfl, rfl⟩

theorem paramsOf_constraint_mode (globals : Globals F) (slotData : Instance F) :
    (paramsOf globals slotData false).auxTrace =
      (if slotData.auxTrace.isEmpty then none else some slotData.auxTrace) ∧
    (paramsOf globals slotData false).constPols = some slotData.fixed ∧
    (paramsOf globals slotData false).challenges = globals.challenges := ⟨rfl, rfl, rfl⟩

/-- Buffers interpreted as mathematical field values. Raw trace words have a
distinct typed accessor; packed data cannot be field-reduced by this selector. -/
inductive FieldBufferKind where
  | auxTrace | customCommitsFixed | airValue | airGroupValue
  | challenge | fixed | evals | publicInput | proofValue | xdivxsub | constTree
  deriving DecidableEq, BEq

def buffer? (params : Params F) : FieldBufferKind → Option (Array F)
  | .auxTrace => params.auxTrace
  | .customCommitsFixed => some params.customCommitsFixed
  | .airValue => some params.airvalues
  | .airGroupValue => some params.airgroupValues
  | .challenge => some params.challenges
  | .fixed => params.constPols
  | .evals => some params.evals
  | .publicInput => some params.publicInputs
  | .proofValue => some params.proofValues
  | .xdivxsub => params.xdivxsub
  | .constTree => params.constTree

def readWord? (params : Params F) (kind : FieldBufferKind) (index : Nat) : Option F := do
  let values ← buffer? params kind
  values[index]?

/-- The SAME original trace word store carried by Params, without canonical
field conversion, cropping to a logical row count, or a decoded sidecar. -/
def traceWord? (params : Params F) (index : Nat) : Option UInt64 :=
  params.trace[index]?

/-- Field-value blocks, not an assumed custom/stage/extension decoding. -/
def readBlock? (params : Params F) (kind : FieldBufferKind) (offset width : Nat) :
    Option (Array F) := do
  if width = 0 then none else do
    let values ← buffer? params kind
    if offset + width ≤ values.size then
      some (values.extract offset (offset + width))
    else none

theorem air_kind_reads_distinct (params : Params F) (index : Nat) :
    readWord? params .airValue index = params.airvalues[index]? ∧
    readWord? params .airGroupValue index = params.airgroupValues[index]? := ⟨rfl, rfl⟩

/-- Exact source scope/kind/stage/rank test for base-field stage1 AIR scalars.
Stage2 extension elements and custom/witness/fixed layouts are not decoded by
pretending that their native blocks are a single stage1 scalar. -/
def stage1Scalar (schema : SourceSchema.Air) (symbol : SourceSchema.Symbol) : Bool :=
  decide (symbol.groupIndex = some schema.groupIndex ∧
    symbol.airIndex = some schema.airIndex ∧ symbol.kind = .airValue ∧
    symbol.stage = some 1 ∧ symbol.dimensions = 0 ∧ symbol.lengths = [])

def stage1ScalarAt? (schema : SourceSchema.Air) (params : Params F) (index : Nat) : Option F :=
  if schema.symbols.any (fun symbol => stage1Scalar schema symbol && decide (symbol.index = index)) then
    readWord? params .airValue index
  else none

/-- A partial evaluator for the actual stage1 Direct selector/constant-tuple
syntax. Unsupported source kinds, malformed literals and missing array cells
return None, never zero. This is not a stage2/custom decoder. -/
def evalDirect? [Field F] (schema : SourceSchema.Air) (params : Params F) : Expr → Option F
  | .constant literal => do return ((← literal.toNat?) : F)
  | .airValue index => stage1ScalarAt? schema params index
  | .add left right => return (← evalDirect? schema params left) + (← evalDirect? schema params right)
  | .sub left right => return (← evalDirect? schema params left) - (← evalDirect? schema params right)
  | .mul left right => return (← evalDirect? schema params left) * (← evalDirect? schema params right)
  | .neg value => return -(← evalDirect? schema params value)
  | _ => none

theorem evalDirect_rejects_stage2_kinds [Field F] (schema : SourceSchema.Air) (params : Params F) :
    evalDirect? schema params (.airGroupValue 0) = none ∧
    evalDirect? schema params (.challenge 2 0) = none ∧
    evalDirect? schema params (.opaque "unsupported" "payload") = none := ⟨rfl, rfl, rfl⟩

end ZiskFv.AirsClean.MemAlignWriteByte.RawSource
