import Clean.Air.Balance
import ZiskFv.Channels.MemoryBus
import ZiskFv.Compliance.EnsembleWitnessBuilder

/-!
# Register MemBus boundary balance for the `add x1,x1,x1` witness

Issue #225's register traffic is a telescoping MemBus argument.  Main's ordinary
row-local register accesses supply the interior push-prev / pull-current pairs;
boot and reload are boundary terms, not normal per-row Main-table emissions.

This file records the checked boundary-shaped register contribution for the
minimal real-register witness `add x1,x1,x1`.  Register x1 has four timeline
messages (boot at step 0, then the two reads and write at steps 1/2/3).  The
other tracked registers x2..x31 are idle and contribute only the boot/reload
zero-value pair.  Every listed message appears once as a pull and once as a push,
so the MemBus contribution balances constructively.

This is intentionally a balance theorem over an explicit list of register MemBus
messages.  It demonstrates the telescoping shape needed by #225, but it does not
yet extract those messages from `fullRv64imEnsemble` rows or construct the full
trace-level `BalancedChannels` witness; that connection is the follow-up handoff
to #219.
-/

open Goldilocks
open ZiskFv.Channels.MemoryBus

namespace ZiskFv.Compliance.RegisterMemBusBalance

/-- The PIL register-memory message `[MEMORY_REG_OP, reg, step, 8, v0, v1]`. -/
def regMsg (reg step value0 value1 : FGL) : MemBusMessage FGL :=
  { mem_op := 3
    ptr := reg
    timestamp := step
    width := 8
    value_0 := value0
    value_1 := value1 }

/-- The all-zero register message used by the no-prelude `add x1,x1,x1` witness. -/
def zeroRegMsg (reg step : FGL) : MemBusMessage FGL :=
  regMsg reg step 0 0

/-- One pull/push pair for the same MemBus message. -/
def pairedInteraction (msg : MemBusMessage FGL) : List (Interaction FGL) :=
  [MemBusChannel.pulledValue msg, MemBusChannel.pushedValue msg]

/-- A list of messages, each emitted once as a pull and once as a push. -/
def pairedInteractions (msgs : List (MemBusMessage FGL)) : List (Interaction FGL) :=
  msgs.flatMap pairedInteraction

theorem pairedInteraction_balanced (msg : MemBusMessage FGL) :
    BalancedInteractions (pairedInteraction msg) := by
  refine Air.Flat.balancedInteractions_of_present ?_
    [(ProvableType.toElements msg).toArray] ?_ ?_
  · left
    simp [pairedInteraction]
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro i hi
    simp [pairedInteraction] at hi ⊢
    rcases hi with rfl | rfl
    · rfl
    · rfl
  · intro presentMsg h_present
    simp only [List.mem_singleton] at h_present
    subst presentMsg
    simp [pairedInteraction, balanceOf, Channel.pulledValue, Channel.pushedValue]

theorem balancedInteractions_append_of_balanced
    {left right : List (Interaction FGL)}
    (h_left : BalancedInteractions left)
    (h_right : BalancedInteractions right)
    (h_len : (left ++ right).length < ringChar FGL ∨ ringChar FGL = 0) :
    BalancedInteractions (left ++ right) := by
  refine ⟨h_len, ?_⟩
  intro msg
  rw [balanceOf_append, h_left.2 msg, h_right.2 msg, add_zero]

theorem pairedInteractions_balanced
    (msgs : List (MemBusMessage FGL))
    (h_len : (pairedInteractions msgs).length < ringChar FGL ∨ ringChar FGL = 0) :
    BalancedInteractions (pairedInteractions msgs) := by
  induction msgs with
  | nil =>
      refine ⟨h_len, ?_⟩
      intro msg
      simp [pairedInteractions, balanceOf]
  | cons msg rest ih =>
      have h_rest_len :
          (pairedInteractions rest).length < ringChar FGL ∨ ringChar FGL = 0 := by
        rcases h_len with h_len | h_zero
        · left
          have h_le :
              (pairedInteractions rest).length ≤
                (pairedInteraction msg ++ pairedInteractions rest).length := by
            simp
          exact lt_of_le_of_lt h_le h_len
        · exact Or.inr h_zero
      exact balancedInteractions_append_of_balanced
        (pairedInteraction_balanced msg) (ih h_rest_len) (by simpa [pairedInteractions] using h_len)

/-- The x1 register timeline for `add x1,x1,x1`:
    boot at 0, read-a at 1, read-b at 2, store-c at 3. -/
def addX1TimelineMessages : List (MemBusMessage FGL) :=
  [ zeroRegMsg 1 0
  , zeroRegMsg 1 1
  , zeroRegMsg 1 2
  , zeroRegMsg 1 3 ]

/-- Idle tracked registers x2..x31, each at the zero boot/reload point. -/
def idleRegisterMessages : List (MemBusMessage FGL) :=
  (List.range 30).map fun i => zeroRegMsg ((i + 2 : Nat) : FGL) 0

/-- The faithful register message set for the no-prelude `add x1,x1,x1` target.

`add x0,x0,x0` is intentionally not used here: ZisK decodes x0 register operands
as immediate/no-op register accesses, so it emits no register `mem_op = 3` traffic.
-/
def addX1X1X1RegisterMessages : List (MemBusMessage FGL) :=
  addX1TimelineMessages ++ idleRegisterMessages

/-- Concrete explicit-message MemBus balance for the register contribution of
    `add x1,x1,x1`: each boot/current message is paired with the corresponding
    push-prev/reload message, and the idle registers have boot/reload zero pairs.
    This theorem does not claim extraction from the real ensemble rows. -/
theorem addX1X1X1_registerMemBus_balanced :
    BalancedInteractions (pairedInteractions addX1X1X1RegisterMessages) := by
  apply pairedInteractions_balanced
  left
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  decide

end ZiskFv.Compliance.RegisterMemBusBalance
