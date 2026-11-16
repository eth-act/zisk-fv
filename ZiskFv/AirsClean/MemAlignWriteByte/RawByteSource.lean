import ZiskFv.AirsClean.MemAlignWriteByte.SourceLiterals
import ZiskFv.Channels.MemoryBus

/-! Source-indexed BYTE-FAMILY projection of a final raw registry snapshot.
This does not claim to enumerate the other AIRs' Direct/global contributions,
to authenticate native arrays, or to derive a snapshot from the old Flat witness.
Every selected occurrence is read from the same final global slot. A missing
slot/cell or unsupported Direct expression makes the projection fail explicitly.
There is no population-count, sign, natural-number, or roster-equality premise. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.RawByteSource
open Goldilocks
open Extraction.LookupWiring
open RawSource
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

inductive ByteAir where
  | readWrite | readOnly | writeOnly
  deriving DecidableEq, BEq

def ByteAir.schema : ByteAir → SourceSchema.Air
  | .readWrite => SourceSchema.air_MemAlignByte
  | .readOnly => SourceSchema.air_MemAlignReadByte
  | .writeOnly => SourceSchema.air_MemAlignWriteByte

def ByteAir.paddingName : ByteAir → String
  | .readWrite => "MemAlignByte.padding_size"
  | .readOnly => "MemAlignReadByte.padding_size"
  | .writeOnly => "MemAlignWriteByte.padding_size"

def ByteAir.paddingSymbols (air : ByteAir) : List SourceSchema.Symbol :=
  air.schema.symbols.filter (fun symbol => decide (symbol.name = air.paddingName))

/-- Independent padding-symbol pins: these are not supplied by the finalizer's
protocol filter, which intentionally selects different source declarations. -/
theorem padding_source_schema :
    ByteAir.readWrite.paddingSymbols =
      [⟨some 0, some 18, "MemAlignByte.padding_size", .airValue, some 1, 0, 0, []⟩] ∧
    ByteAir.readOnly.paddingSymbols =
      [⟨some 0, some 19, "MemAlignReadByte.padding_size", .airValue, some 1, 0, 0, []⟩] ∧
    ByteAir.writeOnly.paddingSymbols =
      [⟨some 0, some 20, "MemAlignWriteByte.padding_size", .airValue, some 1, 0, 0, []⟩] :=
  ⟨rfl, rfl, rfl⟩

def ByteAir.groupResultSymbols (air : ByteAir) : List SourceSchema.Symbol :=
  air.schema.symbols.filter (fun symbol => decide
    (symbol.name = "Zisk.gsum_result" ∧ symbol.kind = .airGroupValue))

theorem group_result_source_schema (air : ByteAir) :
    air.groupResultSymbols =
      [⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩] := by
  cases air <;> rfl

theorem write_direct_array_source_schema :
    ByteAir.writeOnly.schema.symbols.filter
      (fun symbol => decide (symbol.name = "MemAlignWriteByte.im_direct")) =
      [⟨some 0, some 20, "MemAlignWriteByte.im_direct", .airValue, some 2, 1, 1, [3]⟩] := rfl

/-- No byte-family catalog declares a semantic segment identifier. An occurrence
ordinal is therefore not rebranded as such a source cell. -/
theorem no_byte_segment_symbol (air : ByteAir) :
    air.schema.symbols.filter (fun symbol => decide
      (symbol.name = "segment_id" ∨ symbol.name = air.schema.airName ++ ".segment_id")) = [] := by
  cases air <;> rfl

def ByteAir.hints : ByteAir → List HintTuple
  | .readWrite => [hint_MemAlignByte_13_0, hint_MemAlignByte_14_0]
  | .readOnly => [hint_MemAlignReadByte_7_0, hint_MemAlignReadByte_8_0]
  | .writeOnly => [hint_MemAlignWriteByte_11_0, hint_MemAlignWriteByte_12_0,
      hint_MemAlignWriteByte_13_0]

def airForEntry? (entry : RegistryEntry) : Option ByteAir :=
  if entry.airgroupId = SourceSchema.air_MemAlignByte.groupIndex ∧
      entry.airId = SourceSchema.air_MemAlignByte.airIndex then some .readWrite
  else if entry.airgroupId = SourceSchema.air_MemAlignReadByte.groupIndex ∧
      entry.airId = SourceSchema.air_MemAlignReadByte.airIndex then some .readOnly
  else if entry.airgroupId = SourceSchema.air_MemAlignWriteByte.groupIndex ∧
      entry.airId = SourceSchema.air_MemAlignWriteByte.airIndex then some .writeOnly
  else none

/-- The actual source hint determines bus, sign, scalar and all six slots.
There is no handwritten surrogate multiplicity replacing the raw source cell. -/
def lowerDirect? (air : ByteAir) (params : Params FGL) (hint : HintTuple) :
    Option (Interaction FGL) := do
  match hint.piop, hint.busId with
  | "Direct", .constant "10" =>
    let values ← hint.slots.mapM (fun slot => evalDirect? air.schema params slot.value)
    let scalar ← evalDirect? air.schema params hint.multiplicity
    match values with
    | [mem_op, ptr, timestamp, width, value_0, value_1] =>
      return MemBusChannel.pushedIfValue (if hint.proves then scalar else -scalar)
        { mem_op, ptr, timestamp, width, value_0, value_1 }
    | _ => none
  | _, _ => none

/-- The native array view stays partial: this does not decode stage2 extension
blocks as base-field words. The real stage1 padding declaration is selected
separately for each AIR, preserving its actual source scope/kind/stage/rank. -/
def paddingValue? (air : ByteAir) (params : Params FGL) : Option FGL := do
  match air.paddingSymbols with
  | [symbol] =>
    if stage1Scalar air.schema symbol then readWord? params .airValue symbol.index else none
  | _ => none

theorem paddingValue_reads_actual_cells (air : ByteAir) (params : Params FGL) :
    paddingValue? air params = params.airvalues[0]? := by
  cases air <;> rfl

theorem selector_reads_actual_padding (air : ByteAir) (params : Params FGL) :
    evalDirect? air.schema params (.add (.airValue 0) (.constant "0")) = paddingValue? air params := by
  cases air <;>
    simp [evalDirect?, stage1ScalarAt?, ByteAir.schema, SourceSchema.air_MemAlignByte,
      SourceSchema.air_MemAlignReadByte, SourceSchema.air_MemAlignWriteByte,
      stage1Scalar, readWord?, buffer?, paddingValue_reads_actual_cells, SourceLiterals.toNat_zero]

def payloadAt? (context : Context FGL) (index : Occurrence context) (mode : Bool) :
    Option (ByteAir × List (Interaction FGL)) := do
  let air ← airForEntry? context.registry.instances[index.val]
  let params ← paramsAt? context index mode
  let interactions ← air.hints.mapM (lowerDirect? air params)
  return (air, interactions)

structure Packet (context : Context FGL) where
  occurrence : Occurrence context
  air : ByteAir
  interactions : List (Interaction FGL)

def Packet.key {context : Context FGL} (packet : Packet context) : OccurrenceKey :=
  occurrenceKey context packet.occurrence

def packetAt? (context : Context FGL) (index : Occurrence context) (mode : Bool) :
    Option (Packet context) :=
  (payloadAt? context index mode).map (fun payload =>
    { occurrence := index, air := payload.1, interactions := payload.2 })

def byteOccurrences (context : Context FGL) : List (Occurrence context) :=
  (occurrences context).filter
    (fun index => (airForEntry? context.registry.instances[index.val]).isSome)

/-- Canonical successful output is constructed internally, never supplied as a
caller roster certificate. Any malformed selected occurrence returns None. -/
def packets? (context : Context FGL) (mode : Bool) : Option (List (Packet context)) :=
  (byteOccurrences context).mapM (fun index => packetAt? context index mode)

def directRoster? (context : Context FGL) (mode : Bool) : Option (List (Interaction FGL)) :=
  (packets? context mode).map (fun packets => packets.flatMap Packet.interactions)

theorem byteOccurrenceKeys_nodup (context : Context FGL) :
    ((byteOccurrences context).map (occurrenceKey context)).Nodup := by
  apply List.Nodup.map (occurrenceKey_injective context)
  exact (List.nodup_ofFn_ofInjective (fun _ _ h => h)).filter _

private theorem packetAt_occurrence (context : Context FGL) (index : Occurrence context)
    (mode : Bool) (packet : Packet context) (h : packetAt? context index mode = some packet) :
    packet.occurrence = index := by
  unfold packetAt? at h
  cases hp : payloadAt? context index mode with
  | none => simp [hp] at h
  | some payload =>
      simp only [hp, Option.map_some, Option.some.injEq] at h
      cases h
      rfl

private theorem mapPackets_occurrences (context : Context FGL) (mode : Bool)
    (indices : List (Occurrence context)) (packets : List (Packet context))
    (h : indices.mapM (fun index => packetAt? context index mode) = some packets) :
    packets.map Packet.occurrence = indices := by
  induction indices generalizing packets with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      cases h
      rfl
  | cons index rest ih =>
      rw [List.mapM_cons] at h
      cases hp : packetAt? context index mode with
      | none => simp [hp] at h
      | some packet =>
          cases ht : rest.mapM (fun index => packetAt? context index mode) with
          | none => simp [hp, ht] at h
          | some tail =>
              have he : packet :: tail = packets := by simpa [hp, ht] using h
              subst packets
              simp only [List.map_cons]
              exact congrArg₂ List.cons (packetAt_occurrence context index mode packet hp) (ih tail ht)

/-- Each parsed byte-family occurrence appears once, in actual registry order.
This is a theorem about the decoder's computed result, not an accepted-trace
input or a source-to-native-array authentication claim. -/
theorem packets_keys_nodup (context : Context FGL) (mode : Bool)
    (packets : List (Packet context)) (h : packets? context mode = some packets) :
    (packets.map Packet.key).Nodup := by
  have hi := mapPackets_occurrences context mode (byteOccurrences context) packets h
  have hk : ((packets.map Packet.occurrence).map (occurrenceKey context)).Nodup := by
    rw [hi]
    exact byteOccurrenceKeys_nodup context
  simpa only [List.map_map, Packet.key, Function.comp_def] using hk

end ZiskFv.AirsClean.MemAlignWriteByte.RawByteSource
