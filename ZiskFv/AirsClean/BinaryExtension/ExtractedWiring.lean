import Extraction.LookupWiring
import ZiskFv.AirsClean.BinaryExtension.Circuit

/-!
# Source-linked BinaryExtension interactions

The generated lookup ledger exposes the eight bus-124 consumers through
validated links 5, 0, 1, 2, and 3. It exposes the bus-5000 provider through
the source hint attached to the checked zero-tail link for constraint 4. This
module decodes those source tuples into the live table-consumer circuit.

Decoding returns an `Option`. Unsupported generated syntax returns `none`, and every
source binding below proves a concrete `some` result. Thus an unsupported term
cannot make a wiring equality true through `none = none`.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.OperationBus (OpBusChannel OpBusMessage)
open ZiskFv.Channels.BinaryExtensionTable
  (BinaryExtensionTableChannel BinaryExtensionTableMessage)

/-- The 29 committed stage-1 columns in the order emitted by
    `Extraction.BinaryExtension`. -/
@[reducible]
def stage1Expressions (row : Var BinaryExtensionRow FGL) : List (Expression FGL) :=
  [ row.flags.op
  , row.aCols.free_in_a_0
  , row.aCols.free_in_a_1
  , row.aCols.free_in_a_2
  , row.aCols.free_in_a_3
  , row.aCols.free_in_a_4
  , row.aCols.free_in_a_5
  , row.aCols.free_in_a_6
  , row.aCols.free_in_a_7
  , row.flags.free_in_b
  , row.cColsLo.free_in_c_0
  , row.cColsLo.free_in_c_1
  , row.cColsLo.free_in_c_2
  , row.cColsLo.free_in_c_3
  , row.cColsLo.free_in_c_4
  , row.cColsLo.free_in_c_5
  , row.cColsLo.free_in_c_6
  , row.cColsLo.free_in_c_7
  , row.cColsHi.free_in_c_8
  , row.cColsHi.free_in_c_9
  , row.cColsHi.free_in_c_10
  , row.cColsHi.free_in_c_11
  , row.cColsHi.free_in_c_12
  , row.cColsHi.free_in_c_13
  , row.cColsHi.free_in_c_14
  , row.cColsHi.free_in_c_15
  , row.flags.op_is_shift
  , row.flags.b_0
  , row.flags.b_1 ]

/-- Partial interpretation of the generated tuple language used by the live
    BinaryExtension routes. Stage, rotation, column bounds, and literal syntax
    are all checked rather than assigned fallback values. -/
def sourceExprToClean (row : Var BinaryExtensionRow FGL) : Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "2" => some 2
  | .constant "3" => some 3
  | .constant "4" => some 4
  | .constant "5" => some 5
  | .constant "6" => some 6
  | .constant "7" => some 7
  | .constant "256" => some 256
  | .constant "65536" => some 65536
  | .constant "16777216" => some 16777216
  | .witness 1 column 0 => (stage1Expressions row)[column]?
  | .add value (.constant "0") => sourceExprToClean row value
  | .add lhs rhs => return (← sourceExprToClean row lhs) + (← sourceExprToClean row rhs)
  | .sub lhs rhs => return (← sourceExprToClean row lhs) - (← sourceExprToClean row rhs)
  | .mul lhs rhs => return (← sourceExprToClean row lhs) * (← sourceExprToClean row rhs)
  | .neg value => return -(← sourceExprToClean row value)
  | _ => none

def decodeSourceSlots (row : Var BinaryExtensionRow FGL) (slots : List Slot) :
    Option (List (Expression FGL)) :=
  slots.mapM fun slot => sourceExprToClean row slot.value

/-- The physical byte order crosses the generated link clusters as
    `5.0, 0.0, 0.1, 1.0, 1.1, 2.0, 2.1, 3.0`. -/
def byteHint : Fin 8 → HintTuple
  | ⟨0, _⟩ => hint_BinaryExtension_5_0
  | ⟨1, _⟩ => hint_BinaryExtension_0_0
  | ⟨2, _⟩ => hint_BinaryExtension_0_1
  | ⟨3, _⟩ => hint_BinaryExtension_1_0
  | ⟨4, _⟩ => hint_BinaryExtension_1_1
  | ⟨5, _⟩ => hint_BinaryExtension_2_0
  | ⟨6, _⟩ => hint_BinaryExtension_2_1
  | ⟨7, _⟩ => hint_BinaryExtension_3_0

def byteLink : Fin 8 → ValidatedLink
  | ⟨0, _⟩ => link_BinaryExtension_5
  | ⟨1, _⟩ | ⟨2, _⟩ => link_BinaryExtension_0
  | ⟨3, _⟩ | ⟨4, _⟩ => link_BinaryExtension_1
  | ⟨5, _⟩ | ⟨6, _⟩ => link_BinaryExtension_2
  | ⟨7, _⟩ => link_BinaryExtension_3

/-- The corresponding live BinaryExtensionTable message. -/
def byteMessage (row : Var BinaryExtensionRow FGL) : Fin 8 →
    BinaryExtensionTableMessage (Expression FGL)
  | ⟨0, _⟩ => ⟨row.flags.op, 0, row.aCols.free_in_a_0, row.flags.free_in_b,
      row.cColsLo.free_in_c_0, row.cColsLo.free_in_c_1, row.flags.op_is_shift⟩
  | ⟨1, _⟩ => ⟨row.flags.op, 1, row.aCols.free_in_a_1, row.flags.free_in_b,
      row.cColsLo.free_in_c_2, row.cColsLo.free_in_c_3, row.flags.op_is_shift⟩
  | ⟨2, _⟩ => ⟨row.flags.op, 2, row.aCols.free_in_a_2, row.flags.free_in_b,
      row.cColsLo.free_in_c_4, row.cColsLo.free_in_c_5, row.flags.op_is_shift⟩
  | ⟨3, _⟩ => ⟨row.flags.op, 3, row.aCols.free_in_a_3, row.flags.free_in_b,
      row.cColsLo.free_in_c_6, row.cColsLo.free_in_c_7, row.flags.op_is_shift⟩
  | ⟨4, _⟩ => ⟨row.flags.op, 4, row.aCols.free_in_a_4, row.flags.free_in_b,
      row.cColsHi.free_in_c_8, row.cColsHi.free_in_c_9, row.flags.op_is_shift⟩
  | ⟨5, _⟩ => ⟨row.flags.op, 5, row.aCols.free_in_a_5, row.flags.free_in_b,
      row.cColsHi.free_in_c_10, row.cColsHi.free_in_c_11, row.flags.op_is_shift⟩
  | ⟨6, _⟩ => ⟨row.flags.op, 6, row.aCols.free_in_a_6, row.flags.free_in_b,
      row.cColsHi.free_in_c_12, row.cColsHi.free_in_c_13, row.flags.op_is_shift⟩
  | ⟨7, _⟩ => ⟨row.flags.op, 7, row.aCols.free_in_a_7, row.flags.free_in_b,
      row.cColsHi.free_in_c_14, row.cColsHi.free_in_c_15, row.flags.op_is_shift⟩

@[reducible]
def byteMessageTuple (message : BinaryExtensionTableMessage (Expression FGL)) :
    List (Expression FGL) :=
  [message.op, message.byte_index, message.a_byte, message.shift_amount,
    message.c_lo_byte, message.c_hi_byte, message.op_is_shift]

/-- Each selected hint is really carried by its stated validated link. -/
theorem byteHint_mem_link (index : Fin 8) : byteHint index ∈ (byteLink index).hints := by
  fin_cases index <;> simp [byteHint, byteLink, link_BinaryExtension_0,
    link_BinaryExtension_1, link_BinaryExtension_2, link_BinaryExtension_3,
    link_BinaryExtension_5]

/-- Direction, bus, and multiplicity are source metadata, not inferred from
    equality of the decoded payload. `proves = false` and multiplicity `1`
    correspond to the live negative emission. -/
theorem byteHint_metadata (index : Fin 8) :
    (byteHint index).piop = "Lookup" ∧
      (byteHint index).proves = false ∧
      (byteHint index).busId = Expr.constant "124" ∧
      (byteHint index).multiplicity = Expr.constant "1" := by
  fin_cases index <;> simp [byteHint, hint_BinaryExtension_0_0,
    hint_BinaryExtension_0_1, hint_BinaryExtension_1_0,
    hint_BinaryExtension_1_1, hint_BinaryExtension_2_0,
    hint_BinaryExtension_2_1, hint_BinaryExtension_3_0,
    hint_BinaryExtension_5_0]

/-- All eight generated slot lists decode successfully and in the live message
    order. -/
theorem byteHint_decode_success (row : Var BinaryExtensionRow FGL) (index : Fin 8) :
    decodeSourceSlots row (byteHint index).slots =
      some (byteMessageTuple (byteMessage row index)) := by
  fin_cases index <;> rfl

/-- Exact bus-124 interaction list of `mainWithBinaryExtensionTable`. -/
theorem tableConsumer_interactionsWith_binaryExtensionTable :
    tableConsumerComponent.operations.interactionsWith
        BinaryExtensionTableChannel.toRaw =
      [ ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 0)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 1)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 2)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 3)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 4)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 5)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 6)).toRaw)
      , ((BinaryExtensionTableChannel.emitted (-1)
          (byteMessage tableConsumerComponent.rowInputVar 7)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryExtensionTableChannel.toRaw, _⟩ ∈ tableConsumerComponent.exposedChannels
  simp [tableConsumerComponent, tableConsumerCircuit, Component.exposedChannels,
    expose, byteMessage]

/-- The table consumer's actual operations contain each decoded source
    interaction with multiplicity `-1`. -/
theorem byteInteraction_mem_tableConsumer_operations (index : Fin 8) :
    ((BinaryExtensionTableChannel.emitted (-1)
        (byteMessage tableConsumerComponent.rowInputVar index)).toRaw) ∈
      tableConsumerComponent.operations.interactionsWith
        BinaryExtensionTableChannel.toRaw := by
  rw [tableConsumer_interactionsWith_binaryExtensionTable]
  fin_cases index <;> simp [byteMessage]

/-! ## Source-hinted operation provider -/

/-- The operation provider is the exact pilout hint #1220 carried by generated
    c4's checked zero-tail link. -/
theorem operationHint_mem_link :
    hint_BinaryExtension_4_0 ∈ link_BinaryExtension_4.hints := by
  simp [link_BinaryExtension_4]

/-- Pin the source spelling and direction. Pilout calls this route `Lookup`,
    with `proves = true`; the Clean operation is consequently a positive push. -/
theorem operationHint_metadata :
    hint_BinaryExtension_4_0.hintIndex = 1220 ∧
      hint_BinaryExtension_4_0.piop = "Lookup" ∧
      hint_BinaryExtension_4_0.proves = true ∧
      hint_BinaryExtension_4_0.busId = Expr.constant "5000" ∧
      hint_BinaryExtension_4_0.multiplicity = Expr.constant "1" := by
  simp [hint_BinaryExtension_4_0]

/-- The generated link pins c4 to the direct zero-tail shape rather than
    accepting a freely reconstructed polynomial. -/
theorem operationLink_source_constraint :
    link_BinaryExtension_4.air = "BinaryExtension" ∧
      link_BinaryExtension_4.constraintIndex = 4 ∧
      link_BinaryExtension_4.shape = .directZeroTail ∧
      link_BinaryExtension_4.constraint = constraint_BinaryExtension_4 ∧
      link_BinaryExtension_4.template = template_BinaryExtension_4 := by
  simp [link_BinaryExtension_4]

/-- The generated proof field checks that the c4 constraint is exactly the
    selected source-hint template. -/
theorem operationLink_constraintValidated :
    templateOf link_BinaryExtension_4.shape link_BinaryExtension_4.alpha
        link_BinaryExtension_4.gamma link_BinaryExtension_4.accumulator
        link_BinaryExtension_4.hints link_BinaryExtension_4.derivedTuples =
      some link_BinaryExtension_4.constraint :=
  link_BinaryExtension_4.constraintValidated

/-- Pilout supplies all 11 source slots. Its final four slots are explicit
    literal zeros named `0`; they are not padding inferred from c4. -/
theorem operationHint_arity_and_zero_tail :
    hint_BinaryExtension_4_0.slots.length = 11 ∧
      hint_BinaryExtension_4_0.slots.drop 7 =
        [ ⟨"0", Expr.constant "0"⟩
        , ⟨"0", Expr.constant "0"⟩
        , ⟨"0", Expr.constant "0"⟩
        , ⟨"0", Expr.constant "0"⟩ ] := by
  simp [hint_BinaryExtension_4_0]

@[reducible]
def opBusMessageTuple (message : OpBusMessage (Expression FGL)) :
    List (Expression FGL) :=
  [message.op, message.a_lo, message.a_hi, message.b_lo, message.b_hi,
    message.c_lo, message.c_hi, message.flag, message.main_step,
    message.extended_arg, message.extra_args_0]

/-- The source c4 hint slots decode successfully to all 11 live operation-bus
    lanes in their physical order. -/
theorem operationTuple_decode_success (row : Var BinaryExtensionRow FGL) :
    decodeSourceSlots row hint_BinaryExtension_4_0.slots =
      some (opBusMessageTuple (opBusMessageExpr row)) := by
  rfl

/-- The decoded provider is the actual operation pushed by
    `mainWithBinaryExtensionTable`, not merely a structurally similar tuple. -/
theorem operationInteraction_mem_tableConsumer_operations :
    ((OpBusChannel.pushed
        (opBusMessageExpr tableConsumerComponent.rowInputVar)).toRaw) ∈
      tableConsumerComponent.operations.interactionsWith OpBusChannel.toRaw := by
  have h : tableConsumerComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed
        (opBusMessageExpr tableConsumerComponent.rowInputVar)).toRaw)] := by
    apply Component.interactionsWith_of_exposedChannels
    change ⟨OpBusChannel.toRaw, _⟩ ∈ tableConsumerComponent.exposedChannels
    simp [tableConsumerComponent, tableConsumerCircuit, Component.exposedChannels, expose]
  rw [h]
  simp

end ZiskFv.AirsClean.BinaryExtension
