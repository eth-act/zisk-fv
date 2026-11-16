import ZiskFv.AirsClean.MemAlignWriteByte.NativeRow
import ZiskFv.AirsClean.MemAlignWriteByte.ExtractedWiring
import ZiskFv.AirsClean.MemAlignWriteByte.RawByteSource

/-! Local source tuple boundaries for the source-owned fourteen-cell consumer.
No legacy SourceTrace/otherMain reader is constructed or consumed. Existing
source-slot lowering is reused verbatim on the computed constant local row;
this module does not create a second native/source expression interpreter.

c8 contains value16 range103 and ordered dual-byte88; c9 alignedLOAD pull;
c10 written-byte range107. c7's alignedSTORE pull/selectedSTORE prove are retained
in the full four-interaction constructor, not counted again as Direct messages.
These boundaries do NOT prove native Ext3/std_sum/source-circuit agreement or
source-world bus88 multiplicity/balance transport merely from slot decoding. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeTupleSource

open Goldilocks Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.DualByte (DualByteChannel)
open RawSource
open NativeRow (rowVar)


def Tuple8Boundary (cells : NativeRow.Cells) (padding : FGL) : Prop :=
  decodeSourceSlots (rowVar cells) (.const padding) hint_MemAlignWriteByte_8_0.slots =
    some [(rowVar cells).value_16b] ∧
  decodeSourceSlots (rowVar cells) (.const padding) hint_MemAlignWriteByte_8_1.slots =
    some [(dualByteMessageExpr (rowVar cells)).byte_a,
      (dualByteMessageExpr (rowVar cells)).byte_b]

def Tuple9Boundary (cells : NativeRow.Cells) (padding : FGL) : Prop :=
  decodeSourceSlots (rowVar cells) (.const padding) hint_MemAlignWriteByte_9_0.slots =
    some (memoryMessageTuple (memReadMessageExpr (rowVar cells)))

def Tuple10Boundary (cells : NativeRow.Cells) (padding : FGL) : Prop :=
  decodeSourceSlots (rowVar cells) (.const padding) hint_MemAlignWriteByte_10_0.slots =
    some [(rowVar cells).written_byte_value]

theorem tuple8_from_actual_cells (cells : NativeRow.Cells) (padding : FGL) :
    Tuple8Boundary cells padding :=
  ⟨value16Hint_decode_success (rowVar cells) (.const padding),
    dualByteHint_decode_success (rowVar cells) (.const padding)⟩

theorem tuple9_from_actual_cells (cells : NativeRow.Cells) (padding : FGL) :
    Tuple9Boundary cells padding :=
  alignedLoadHint_decode_success (rowVar cells) (.const padding)

theorem tuple10_from_actual_cells (cells : NativeRow.Cells) (padding : FGL) :
    Tuple10Boundary cells padding :=
  writtenByteHint_decode_success (rowVar cells) (.const padding)

/-- Aligned step+1 STORE pull and selected one-byte STORE prove are the actual
c7 source tuples, not detached surrogate operations or extra padding emissions. -/
theorem tuple7_from_actual_cells (cells : NativeRow.Cells) (padding : FGL) :
    decodeSourceSlots (rowVar cells) (.const padding) hint_MemAlignWriteByte_7_0.slots =
      some (memoryMessageTuple (memWriteMessageExpr (rowVar cells))) ∧
    decodeSourceSlots (rowVar cells) (.const padding) hint_MemAlignWriteByte_7_1.slots =
      some (memoryMessageTuple (memBusMessageExpr (rowVar cells))) :=
  ⟨alignedStoreHint_decode_success (rowVar cells) (.const padding),
    selectedStoreHint_decode_success (rowVar cells) (.const padding)⟩

/-- Source constraint links are the existing actual AST-validated links; these
are not promises supplied with a row. They do not alone transport native std_sum. -/
theorem tuple8_source_constraint :
    templateOf link_MemAlignWriteByte_8.shape link_MemAlignWriteByte_8.alpha
      link_MemAlignWriteByte_8.gamma link_MemAlignWriteByte_8.accumulator
      link_MemAlignWriteByte_8.hints link_MemAlignWriteByte_8.derivedTuples =
      some link_MemAlignWriteByte_8.constraint := constraint8_source_validated

theorem tuple9_source_constraint :
    templateOf link_MemAlignWriteByte_9.shape link_MemAlignWriteByte_9.alpha
      link_MemAlignWriteByte_9.gamma link_MemAlignWriteByte_9.accumulator
      link_MemAlignWriteByte_9.hints link_MemAlignWriteByte_9.derivedTuples =
      some link_MemAlignWriteByte_9.constraint := constraint9_source_validated

theorem tuple10_source_constraint :
    templateOf link_MemAlignWriteByte_10.shape link_MemAlignWriteByte_10.alpha
      link_MemAlignWriteByte_10.gamma link_MemAlignWriteByte_10.accumulator
      link_MemAlignWriteByte_10.hints link_MemAlignWriteByte_10.derivedTuples =
      some link_MemAlignWriteByte_10.constraint := constraint10_source_validated

/-- The seven existing local polynomial operations only. Source lookups and
interactions below are rebuilt from their actual decoded tuple slots. -/
def assertOperations (cells : NativeRow.Cells) (offset : Nat) : Operations FGL :=
  (NativeRow.operations cells offset).filter fun operation =>
    match operation with | .assert _ => true | _ => false

def memorySlots? : List (Expression FGL) → Option (MemBusMessage (Expression FGL))
  | [op, ptr, step, width, lo, hi] => some ⟨op, ptr, step, width, lo, hi⟩
  | _ => none

def lookupOperations (written value16 first second : Expression FGL) (offset : Nat) :
    Operations FGL :=
  ((do
    Circuit.lookup (Table.fromStatic RangeTables.rangeTable8) written
    Circuit.lookup (Table.fromStatic RangeTables.rangeTable16) value16
    Circuit.lookup (Table.fromStatic RangeTables.dualByteTable) #v[first, second]) :
      Circuit FGL Unit).operations offset

/-- Load-bearing source constructor: decoded c8/c9/c10 slots actually determine
the lookup and interaction operands returned, instead of merely being checked
then discarded. c7's two real memory tuples complete the four-message roster. -/
def sourceOperations? (cells : NativeRow.Cells) (padding : FGL) (offset : Nat) :
    Option (Operations FGL) := do
  let row := rowVar cells
  let written ← decodeSourceSlots row (.const padding) hint_MemAlignWriteByte_10_0.slots
  let value16 ← decodeSourceSlots row (.const padding) hint_MemAlignWriteByte_8_0.slots
  let dual ← decodeSourceSlots row (.const padding) hint_MemAlignWriteByte_8_1.slots
  let load ← memorySlots? (← decodeSourceSlots row (.const padding) hint_MemAlignWriteByte_9_0.slots)
  let store ← memorySlots? (← decodeSourceSlots row (.const padding) hint_MemAlignWriteByte_7_0.slots)
  let selected ← memorySlots? (← decodeSourceSlots row (.const padding) hint_MemAlignWriteByte_7_1.slots)
  match written, value16, dual with
  | [written], [value16], [first, second] =>
    return lookupOperations written value16 first second offset ++
      assertOperations cells offset ++
      [Operation.interact (MemBusChannel.pulled load).toRaw,
        Operation.interact (MemBusChannel.pulled store).toRaw,
        Operation.interact (MemBusChannel.pushed selected).toRaw,
        Operation.interact (DualByteChannel.pulled ⟨first, second⟩).toRaw]
  | _, _, _ => none

/-- The actual source-decoded constructor is exactly the existing component
operations: no changed static interface, extra validator or second convention. -/
theorem sourceOperations_eq (cells : NativeRow.Cells) (padding : FGL) (offset : Nat) :
    sourceOperations? cells padding offset = some (NativeRow.operations cells offset) := by
  simp only [sourceOperations?, writtenByteHint_decode_success, value16Hint_decode_success,
    dualByteHint_decode_success, alignedLoadHint_decode_success,
    alignedStoreHint_decode_success, selectedStoreHint_decode_success, memorySlots?,
    memoryMessageTuple]
  congr 1

theorem spec_of_sourceOperations (cells : NativeRow.Cells) (padding : FGL)
    (offset : Nat) (ops : Operations FGL) (env : Environment FGL)
    (hsource : sourceOperations? cells padding offset = some ops)
    (hholds : ConstraintsHold.Soundness env ops) : Spec (NativeRow.ofCells cells) := by
  rw [sourceOperations_eq] at hsource
  cases Option.some.inj hsource
  exact NativeRow.spec_of_operations cells offset env hholds

/-- Once-per-occurrence source Direct roster in exact11/12/13 order, including
raw zero multiplicities. No count-to-Nat conversion or positivity is requested. -/
def directValues? (params : Params FGL) : Option (List (Interaction FGL)) :=
  (RawByteSource.ByteAir.writeOnly.hints).mapM
    (RawByteSource.lowerDirect? .writeOnly params)

def directValues (padding : FGL) : List (Interaction FGL) :=
  [MemBusChannel.pushedIfValue padding (⟨1, 0, 0, 8, 0, 0⟩ : MemBusMessage FGL),
    MemBusChannel.pushedIfValue (-padding) (⟨2, 0, 0, 1, 0, 0⟩ : MemBusMessage FGL),
    MemBusChannel.pushedIfValue padding (⟨2, 0, 1, 8, 0, 0⟩ : MemBusMessage FGL)]

theorem direct_source_order : RawByteSource.ByteAir.writeOnly.hints =
    [hint_MemAlignWriteByte_11_0, hint_MemAlignWriteByte_12_0,
      hint_MemAlignWriteByte_13_0] := rfl

theorem direct_reads_actual_padding (params : Params FGL) :
    directValues? params = params.airvalues[0]?.map directValues := by
  cases hp : params.airvalues[0]? <;>
    simp [directValues?, RawByteSource.ByteAir.hints, RawByteSource.lowerDirect?,
      hint_MemAlignWriteByte_11_0, hint_MemAlignWriteByte_12_0, hint_MemAlignWriteByte_13_0,
      evalDirect?, stage1ScalarAt?, RawByteSource.ByteAir.schema,
      SourceSchema.air_MemAlignWriteByte, stage1Scalar, readWord?, buffer?,
      SourceLiterals.toNat_zero, SourceLiterals.toNat_one, SourceLiterals.toNat_two,
      SourceLiterals.toNat_eight, directValues, hp, bind, pure]

theorem direct_multiplicities (padding : FGL) :
    (directValues padding).map Interaction.mult = [padding, -padding, padding] := rfl

/-- Source zero is still three weighted messages; it is not silently removed. -/
theorem direct_zero_roster : (directValues 0).length = 3 := rfl

/-- The source row and Direct rosters remain distinct, including timestamp0
internal byte/Mem counterpart cases. Nothing is blanketed away or canceled here. -/
def occurrenceValues (cells : NativeRow.Cells) (padding : FGL) : List (Interaction FGL) :=
  NativeRow.interactionValues cells ++ directValues padding

theorem occurrence_values_length (cells : NativeRow.Cells) (padding : FGL) :
    (occurrenceValues cells padding).length = 7 := rfl

end ZiskFv.AirsClean.MemAlignWriteByte.NativeTupleSource
