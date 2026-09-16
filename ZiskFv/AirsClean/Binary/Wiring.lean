import Extraction.LookupWiring
import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryTableSlice
import ZiskFv.AirsClean.ExtractionExpr
import Clean.Air.Vm

/-!
# Binary byte lookup wiring

The generated c7--c11 links carry all eight live bus-125 byte tuples. Bytes
0--6 come from gsum hints; c10 has no hint, so byte 7 is reconstructed from
the exact mixed constraint together with its bus-5000 operation tuple. This
module checks the bus ID, direction, multiplicity, link membership, and exact
slot interpretation for every byte.

## Trust note

No axioms. Every generated `ValidatedLink` carries its own kernel equality to
the template computed from its shape and operands. Static BinaryTable
membership remains provider-owned and reaches the consumer only through
finished-channel balance.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.BinaryTable (BinaryTableChannel BinaryTableMessage)

set_option maxRecDepth 4000

/-- Interpret exactly the expression language used by Binary's eight bus-125
tuples. Unsupported constants, columns, stages, offsets, and constructors are
rejected as `none`; there is no default field value. -/
@[reducible]
def lookupExprToCleanCore : Expr → Option (Expression FGL)
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "2" => some 2
  | .constant "4" => some 4
  | .constant "8" => some 8
  | .witness 1 0 0 => some tableConsumerComponent.rowInputVar.chain.b_op
  | .witness 1 1 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_0
  | .witness 1 2 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_1
  | .witness 1 3 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_2
  | .witness 1 4 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_3
  | .witness 1 5 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_4
  | .witness 1 6 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_5
  | .witness 1 7 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_6
  | .witness 1 8 0 => some tableConsumerComponent.rowInputVar.aBytes.free_in_a_7
  | .witness 1 9 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_0
  | .witness 1 10 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_1
  | .witness 1 11 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_2
  | .witness 1 12 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_3
  | .witness 1 13 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_4
  | .witness 1 14 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_5
  | .witness 1 15 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_6
  | .witness 1 16 0 => some tableConsumerComponent.rowInputVar.bBytes.free_in_b_7
  | .witness 1 17 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_0
  | .witness 1 18 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_1
  | .witness 1 19 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_2
  | .witness 1 20 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_3
  | .witness 1 21 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_4
  | .witness 1 22 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_5
  | .witness 1 23 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_6
  | .witness 1 24 0 => some tableConsumerComponent.rowInputVar.cBytes.free_in_c_7
  | .witness 1 25 0 => some tableConsumerComponent.rowInputVar.chain.carry_0
  | .witness 1 26 0 => some tableConsumerComponent.rowInputVar.chain.carry_1
  | .witness 1 27 0 => some tableConsumerComponent.rowInputVar.chain.carry_2
  | .witness 1 28 0 => some tableConsumerComponent.rowInputVar.chain.carry_3
  | .witness 1 29 0 => some tableConsumerComponent.rowInputVar.chain.carry_4
  | .witness 1 30 0 => some tableConsumerComponent.rowInputVar.chain.carry_5
  | .witness 1 31 0 => some tableConsumerComponent.rowInputVar.chain.carry_6
  | .witness 1 32 0 => some tableConsumerComponent.rowInputVar.chain.carry_7
  | .witness 1 33 0 => some tableConsumerComponent.rowInputVar.mode.mode32
  | .witness 1 34 0 => some tableConsumerComponent.rowInputVar.mode.result_is_a
  | .witness 1 35 0 => some tableConsumerComponent.rowInputVar.mode.use_first_byte
  | .witness 1 36 0 => some tableConsumerComponent.rowInputVar.mode.c_is_signed
  | .witness 1 37 0 => some tableConsumerComponent.rowInputVar.chain.b_op_or_sext
  | .witness 1 38 0 => some tableConsumerComponent.rowInputVar.mode.mode32_and_c_is_signed
  | .add lhs rhs => do
      return (← lookupExprToCleanCore lhs) + (← lookupExprToCleanCore rhs)
  | .sub lhs rhs => do
      return (← lookupExprToCleanCore lhs) - (← lookupExprToCleanCore rhs)
  | .mul lhs rhs => do
      return (← lookupExprToCleanCore lhs) * (← lookupExprToCleanCore rhs)
  | _ => none

@[reducible]
def lookupExprToClean (expr : Expr) : Option (Expression FGL) :=
  ZiskFv.AirsClean.translateTrailingAddZero lookupExprToCleanCore expr

@[reducible]
def lookupSlotsToClean : List Slot → Option (List (Expression FGL))
  | [] => some []
  | slot :: slots => do
      return (← lookupExprToClean slot.value) :: (← lookupSlotsToClean slots)

@[reducible]
def lookupMessageTuple (message : BinaryTableMessage (Expression FGL)) :
    List (Expression FGL) :=
  [ message.pos_ind
  , message.op
  , message.a_byte
  , message.b_byte
  , message.cin
  , message.c_byte
  , message.flags ]

@[reducible]
def lookupMessage7Tuple (row : Var BinaryRow FGL) : List (Expression FGL) :=
  lookupMessageTuple (lookupMessage7 row)

/-- A common view of a generated hint tuple or a tuple reconstructed from an
exact mixed constraint. -/
structure BinaryLookupTuple where
  piop : String
  proves : Bool
  busId : Expr
  multiplicity : Expr
  slots : List Slot

@[reducible]
def BinaryLookupTuple.ofHint (tuple : HintTuple) : BinaryLookupTuple :=
  ⟨tuple.piop, tuple.proves, tuple.busId, tuple.multiplicity, tuple.slots⟩

@[reducible]
def BinaryLookupTuple.ofDerived (tuple : DerivedTuple) : BinaryLookupTuple :=
  ⟨tuple.piop, tuple.proves, tuple.busId, tuple.multiplicity, tuple.slots⟩

/-- The raw source value expected in an input/output byte slot.  PIL emits
`x + 0` for bytes 0--6 and a bare witness for the derived terminal tuple. -/
@[reducible]
def expectedByteSlotValue (firstColumn : ℕ) (byte : Fin 8) : Expr :=
  if byte = 7 then
    .witness 1 (firstColumn + byte.val) 0
  else
    .add (.witness 1 (firstColumn + byte.val) 0) (.constant "0")

/-- The 24 generated byte leaves accepted by the exact source-value pins in
`BinaryByteWiring` are pairwise distinct. -/
def expectedByteLeafPatterns : List Expr :=
  [1, 9, 17].flatMap fun firstColumn =>
    List.ofFn fun byte : Fin 8 => expectedByteSlotValue firstColumn byte

theorem expectedByteLeafPatterns_nodup : expectedByteLeafPatterns.Nodup := by
  decide

@[reducible]
def lookupMessageTuples : Vector (List (Expression FGL)) 8 := #v[
  lookupMessageTuple (lookupMessage0 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage1 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage2 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage3 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage4 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage5 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage6 tableConsumerComponent.rowInputVar),
  lookupMessageTuple (lookupMessage7 tableConsumerComponent.rowInputVar)]

@[reducible]
def lookupMessageTupleAt (byte : Fin 8) : List (Expression FGL) :=
  lookupMessageTuples[byte]

/-- Proof-carrying binding of one generated bus-125 tuple to one live Binary
byte lookup. `sourceSplit` prevents an adjacent or invented tuple from being
used with the validated constraint. -/
structure BinaryByteWiring where
  byte : Fin 8
  link : ValidatedLink
  constraintValidated :
    templateOf link.shape link.alpha link.gamma link.accumulator
      link.hints link.derivedTuples = some link.constraint
  source : BinaryLookupTuple
  sourcePrefix : List BinaryLookupTuple
  sourceSuffix : List BinaryLookupTuple
  sourceSplit :
    List.append
      (List.map BinaryLookupTuple.ofHint link.hints)
      (List.map BinaryLookupTuple.ofDerived link.derivedTuples) =
        List.append sourcePrefix (source :: sourceSuffix)
  lookupPiop : source.piop = "Lookup"
  lookupBus : source.busId = Expr.constant "125"
  lookupIsAssumes : source.proves = false
  lookupMultiplicity : source.multiplicity = Expr.constant "1"
  sourceAValue : source.slots[2]?.map (·.value) =
    some (expectedByteSlotValue 1 byte)
  sourceBValue : source.slots[3]?.map (·.value) =
    some (expectedByteSlotValue 9 byte)
  sourceCValue : source.slots[5]?.map (·.value) =
    some (expectedByteSlotValue 17 byte)
  slotInterpretation : lookupSlotsToClean source.slots = some (lookupMessageTupleAt byte)

@[reducible]
def byte0Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_11_0).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 0) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_11_0).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 0) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_11_0).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 0) := by rfl
    exact ⟨0, link_Binary_11, ValidatedLink.constraintValidated link_Binary_11,
      .ofHint hint_Binary_11_0, [], [], rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte1Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_7_0).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 1) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_7_0).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 1) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_7_0).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 1) := by rfl
    exact ⟨1, link_Binary_7, ValidatedLink.constraintValidated link_Binary_7,
      .ofHint hint_Binary_7_0, [], [.ofHint hint_Binary_7_1],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte2Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_7_1).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 2) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_7_1).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 2) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_7_1).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 2) := by rfl
    exact ⟨2, link_Binary_7, ValidatedLink.constraintValidated link_Binary_7,
      .ofHint hint_Binary_7_1, [.ofHint hint_Binary_7_0], [],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte3Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_8_0).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 3) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_8_0).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 3) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_8_0).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 3) := by rfl
    exact ⟨3, link_Binary_8, ValidatedLink.constraintValidated link_Binary_8,
      .ofHint hint_Binary_8_0, [], [.ofHint hint_Binary_8_1],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte4Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_8_1).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 4) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_8_1).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 4) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_8_1).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 4) := by rfl
    exact ⟨4, link_Binary_8, ValidatedLink.constraintValidated link_Binary_8,
      .ofHint hint_Binary_8_1, [.ofHint hint_Binary_8_0], [],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte5Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_9_0).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 5) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_9_0).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 5) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_9_0).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 5) := by rfl
    exact ⟨5, link_Binary_9, ValidatedLink.constraintValidated link_Binary_9,
      .ofHint hint_Binary_9_0, [], [.ofHint hint_Binary_9_1],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte6Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofHint hint_Binary_9_1).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 6) := by rfl
    have hb : (BinaryLookupTuple.ofHint hint_Binary_9_1).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 6) := by rfl
    have hc : (BinaryLookupTuple.ofHint hint_Binary_9_1).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 6) := by rfl
    exact ⟨6, link_Binary_9, ValidatedLink.constraintValidated link_Binary_9,
      .ofHint hint_Binary_9_1, [.ofHint hint_Binary_9_0], [],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byte7Wiring : BinaryByteWiring :=
  by
    have ha : (BinaryLookupTuple.ofDerived derivedTuple_Binary_10_0).slots[2]?.map (·.value) =
        some (expectedByteSlotValue 1 7) := by rfl
    have hb : (BinaryLookupTuple.ofDerived derivedTuple_Binary_10_0).slots[3]?.map (·.value) =
        some (expectedByteSlotValue 9 7) := by rfl
    have hc : (BinaryLookupTuple.ofDerived derivedTuple_Binary_10_0).slots[5]?.map (·.value) =
        some (expectedByteSlotValue 17 7) := by rfl
    exact ⟨7, link_Binary_10, ValidatedLink.constraintValidated link_Binary_10,
      .ofDerived derivedTuple_Binary_10_0, [], [.ofDerived derivedTuple_Binary_10_1],
      rfl, rfl, rfl, rfl, rfl, ha, hb, hc, rfl⟩

@[reducible]
def byteWirings : List BinaryByteWiring :=
  [byte0Wiring, byte1Wiring, byte2Wiring, byte3Wiring,
    byte4Wiring, byte5Wiring, byte6Wiring, byte7Wiring]

/-- The checked packet contains exactly one source binding for every live byte. -/
theorem byteWirings_indices :
    byteWirings.map (·.byte) = [0, 1, 2, 3, 4, 5, 6, 7] := by
  simp [byteWirings]

/-- Unsupported manifest expressions cannot acquire a Clean interpretation. -/
theorem lookupExprToClean_rejects_unsupported :
    lookupExprToClean (.airValue 0) = none ∧
    lookupExprToClean (.witness 1 39 0) = none ∧
    lookupExprToClean (.witness 2 0 0) = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- The terminal BinaryTable connection has the actual Binary negative
consumer component and the exact static-table provider slice before finishing
bus 125. No per-opcode premise or soundness-side `ProverAssumptions` is used. -/
def binaryTableConnectionEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable tableConsumerComponent
        (by simp [circuit_norm, tableConsumerComponent, tableConsumerCircuit])
        (by
          intro channel h_finished
          change channel ∈ ([] : List (RawChannel FGL)) at h_finished
          simp at h_finished)
    |>.addTable ZiskFv.AirsClean.BinaryTableSlice.component
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryTableSlice.component,
          ZiskFv.AirsClean.BinaryTableSlice.circuit])
        (by
          intro channel h_finished
          change channel ∈ ([] : List (RawChannel FGL)) at h_finished
          simp at h_finished)
    |>.addFinishedChannel BinaryTableChannel.toRaw
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          clear h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h | h <;> (rw [h]; trivial))
        (by intro _ _; trivial)

theorem binaryTableConnectionEnsemble_finishes_bus125 :
    BinaryTableChannel.toRaw ∈ binaryTableConnectionEnsemble.ensemble.channels := by
  simp [binaryTableConnectionEnsemble, SoundEnsemble.toFormal,
    SoundEnsemble.addFinishedChannel_channels, SoundEnsemble.addTable_channels]

end ZiskFv.AirsClean.Binary
