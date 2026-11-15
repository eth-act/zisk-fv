import ZiskFv.AirsClean.MemAlignWriteByte.Circuit
import ZiskFv.AirsClean.MemAlignWriteByte.DirectEquations
import Clean.Air.Balance

/-! Actual source once-per-segment Direct operations accept the unrestricted
source AIR-value scalar. Physical-count relations belong only to the separate
honest Segment constructor and are not soundness or acceptance premises. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

@[reducible]
def paddingLoadMessage : MemBusMessage (Expression FGL) := ⟨1, 0, 0, 8, 0, 0⟩

@[reducible]
def paddingSelectedStoreMessage : MemBusMessage (Expression FGL) := ⟨2, 0, 0, 1, 0, 0⟩

@[reducible]
def paddingAlignedStoreMessage : MemBusMessage (Expression FGL) := ⟨2, 0, 1, 8, 0, 0⟩

/-- Source lines107,114,115, with the actual raw field scalar and signed
multiplicities. No count, positivity or natural-number cast is required. -/
def directInteractions (paddingSize : FGL) : List (ChannelInteraction MemBusChannel) :=
  [ MemBusChannel.emitted (.const paddingSize) paddingLoadMessage
  , MemBusChannel.emitted (-(.const paddingSize)) paddingSelectedStoreMessage
  , MemBusChannel.emitted (.const paddingSize) paddingAlignedStoreMessage ]

def directMain (paddingSize : FGL) : Circuit FGL Unit := do
  MemBusChannel.emit (.const paddingSize) paddingLoadMessage
  MemBusChannel.emit (-(.const paddingSize)) paddingSelectedStoreMessage
  MemBusChannel.emit (.const paddingSize) paddingAlignedStoreMessage

theorem directMain_operations (paddingSize : FGL) (offset : ℕ) :
    (directMain paddingSize).operations offset =
      (directInteractions paddingSize).map (fun interaction => Operation.interact interaction.toRaw) := rfl

open Classical in
noncomputable def memoryCoefficient (env : Environment FGL) (message : MemBusMessage FGL)
    (interactions : List (ChannelInteraction MemBusChannel)) : FGL :=
  (interactions.map fun interaction =>
    if ProvableType.eval env interaction.msg = message then
      Expression.eval env interaction.mult else 0).sum

theorem memoryCoefficient_append (env : Environment FGL) (message : MemBusMessage FGL)
    (left right : List (ChannelInteraction MemBusChannel)) :
    memoryCoefficient env message (left ++ right) =
      memoryCoefficient env message left + memoryCoefficient env message right := by
  simp [memoryCoefficient, List.map_append, List.sum_append]

theorem memoryCoefficient_replicate (env : Environment FGL) (message : MemBusMessage FGL)
    (interactions : List (ChannelInteraction MemBusChannel)) (n : ℕ) :
    memoryCoefficient env message (List.replicate n interactions).flatten =
      (n : FGL) * memoryCoefficient env message interactions := by
  induction n with
  | zero => simp [memoryCoefficient]
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, memoryCoefficient_append, ih,
        Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      ring

/-- Concrete values of the actual once-per-segment Direct operations. -/
def directValues (paddingSize : FGL) (env : Environment FGL) : List (Interaction FGL) :=
  (directInteractions paddingSize).map (fun interaction => interaction.toRaw.eval env)

/-- Exact per-message source contribution for every raw source scalar,
including `0`, `-1` and values with no natural-count interpretation. -/
theorem directValues_balance (paddingSize : FGL) (env : Environment FGL)
    (message : Array FGL) :
    balanceOf (directValues paddingSize env) message =
      (if ((MemBusChannel.emitted (.const paddingSize) paddingLoadMessage).toRaw.eval env).msg =
        message then paddingSize else 0) +
      (if ((MemBusChannel.emitted (-(.const paddingSize)) paddingSelectedStoreMessage).toRaw.eval env).msg =
        message then -paddingSize else 0) +
      (if ((MemBusChannel.emitted (.const paddingSize) paddingAlignedStoreMessage).toRaw.eval env).msg =
        message then paddingSize else 0) := by
  classical
  simp only [directValues, directInteractions, List.map_cons, List.map_nil,
    balanceOf, List.filter_cons]
  split_ifs <;>
    simp_all [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.emitted,
      emitted, Expression.eval] <;> ring

/-- Genuine global balance forces the other actual interactions to supply the
opposite per-message contribution. No Direct term is discarded, and no scalar
is relabeled a count. The ensemble's own `BalancedInteractions` is consumed. -/
theorem direct_counterpart_of_balance (paddingSize : FGL) (env : Environment FGL)
    (others : List (Interaction FGL))
    (hbalance : BalancedInteractions (others ++ directValues paddingSize env))
    (message : Array FGL) :
    balanceOf others message = -balanceOf (directValues paddingSize env) message := by
  have h := hbalance.2 message
  rw [balanceOf_append] at h
  linear_combination h

end ZiskFv.AirsClean.MemAlignWriteByte
