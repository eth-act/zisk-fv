import Extraction.LookupWiring
import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryTableSlice
import Clean.Air.Vm

/-!
# Binary c10 lookup wiring

`Binary` constraint c10 has no gsum hint. The generated manifest therefore
records its bus-125 lookup and bus-5000 operation operands as
constraint-derived tuples under the checked `derivedMixed2` template. This
module is the live-model cross-check: its bus-125 tuple is translated to the
actual `lookupMessage7` expression used by the Binary consumer.

## Trust note

No axioms. The generated c10 template is checked by `rfl`, and the source
binding below is another kernel equality. Static BinaryTable membership remains
provider-owned and reaches the consumer only through finished-channel balance.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Air.Flat
open Extraction.LookupWiring
open ZiskFv.Channels.BinaryTable (BinaryTableChannel)

/-- The c10 bus-125 AST uses only these Binary row columns. The fallback is
unreachable for the checked c10 tuple; it keeps this syntax-to-Clean map total
without granting any interpretation to other manifest terms. -/
@[reducible]
def c10LookupExprToClean : Expr → Expression FGL
  | .constant "1" => 1
  | .constant "2" => 2
  | .constant "4" => 4
  | .constant "8" => 8
  | .witness 1 8 0 => tableConsumerComponent.rowInputVar.aBytes.free_in_a_7
  | .witness 1 16 0 => tableConsumerComponent.rowInputVar.bBytes.free_in_b_7
  | .witness 1 24 0 => tableConsumerComponent.rowInputVar.cBytes.free_in_c_7
  | .witness 1 31 0 => tableConsumerComponent.rowInputVar.chain.carry_6
  | .witness 1 32 0 => tableConsumerComponent.rowInputVar.chain.carry_7
  | .witness 1 33 0 => tableConsumerComponent.rowInputVar.mode.mode32
  | .witness 1 34 0 => tableConsumerComponent.rowInputVar.mode.result_is_a
  | .witness 1 35 0 => tableConsumerComponent.rowInputVar.mode.use_first_byte
  | .witness 1 36 0 => tableConsumerComponent.rowInputVar.mode.c_is_signed
  | .witness 1 37 0 => tableConsumerComponent.rowInputVar.chain.b_op_or_sext
  | .add lhs rhs => c10LookupExprToClean lhs + c10LookupExprToClean rhs
  | .sub lhs rhs => c10LookupExprToClean lhs - c10LookupExprToClean rhs
  | .mul lhs rhs => c10LookupExprToClean lhs * c10LookupExprToClean rhs
  | _ => 0

@[reducible]
def c10LookupTupleFromLink : List (Expression FGL) :=
  derivedTuple_Binary_10_0.slots.map (fun slot => c10LookupExprToClean slot.value)

@[reducible]
def lookupMessage7Tuple (row : Var BinaryRow FGL) : List (Expression FGL) :=
  let message := lookupMessage7 row
  [ message.pos_ind
  , message.op
  , message.a_byte
  , message.b_byte
  , message.cin
  , message.c_byte
  , message.flags ]

/-- Proof-carrying source binding for the absent-hint c10 route. -/
structure BinaryC10Wiring where
  link : ValidatedLink
  lookupTuple : DerivedTuple
  operationTuple : DerivedTuple
  c10Link : link = link_Binary_10
  derivedTuples : link.derivedTuples = [lookupTuple, operationTuple]
  lookupBus : lookupTuple.busId = Expr.constant "125"
  lookupIsAssumes : lookupTuple.proves = false
  operationBus : operationTuple.busId = Expr.constant "5000"
  operationIsProves : operationTuple.proves = true
  sourceBinding : c10LookupTupleFromLink =
    lookupMessage7Tuple tableConsumerComponent.rowInputVar

@[reducible]
def c10Wiring : BinaryC10Wiring where
  link := link_Binary_10
  lookupTuple := derivedTuple_Binary_10_0
  operationTuple := derivedTuple_Binary_10_1
  c10Link := rfl
  derivedTuples := rfl
  lookupBus := rfl
  lookupIsAssumes := rfl
  operationBus := rfl
  operationIsProves := rfl
  sourceBinding := rfl

/-- Lean-side acceptance cross-check: the manifest's derived bus-125 tuple is
exactly the live Binary consumer's `lookupMessage7` tuple. -/
theorem c10_lookup_tuple_matches_lookupMessage7 :
    c10LookupTupleFromLink = lookupMessage7Tuple tableConsumerComponent.rowInputVar := by
  exact c10Wiring.sourceBinding

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
