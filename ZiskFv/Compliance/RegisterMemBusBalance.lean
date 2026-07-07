import Clean.Air.Balance
import ZiskFv.Channels.MemoryBus
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.AirsClean.RegisterBoundary

/-!
# Register MemBus balance for the `add x1,x1,x1` witness (from real component emissions)

Issue #225's register traffic is a telescoping MemBus argument.  For a register-register
instruction Main emits, per operand, a `MEMORY_REG_OP` (`mem_op = 3`) push-prev (the previous
register access) and a pull-current (the current access); the two chain-closing boundary terms —
boot (`global_init_mem`) and reload (`reg_pre_load`) — are emitted by the RegisterBoundary
component (`ZiskFv/AirsClean/RegisterBoundary.lean`).  All of these are now real composed-table
emissions in `fullRv64imEnsemble` (see `AirsClean/FullEnsemble.lean`).

This file proves that the register (`mem_op = 3`) partition of those emissions **telescopes to
zero** for the minimal no-prelude real-register witness `add x1,x1,x1`.  Unlike the earlier
shape-demo, the balanced messages here are the **real component emission definitions**
(`aRegPreMessage`/`aMemMessage`/… from `Main/Bridge.lean`, `bootMessage`/`reloadMessage` from
RegisterBoundary) instantiated at a concrete `add x1,x1,x1` `MainRowWithRom`, not hand-authored
literals.  Their multiplicities are the emissions' own selectors: for `add x1,x1,x1` the push-prev
selectors `a_src_reg`/`b_src_reg`/`store_reg` are `1` and the pull selectors
`-(…_mem + … + …_reg)` are `-1`, matching `pushedValue` / `pulledValue`.

**Scope.** This is the register-partition balance (`BalancedInteractions` over the `mem_op = 3`
messages), the object #219 consumes.  It does **not** build the whole-channel
`witness.BalancedChannels` or the constraint-satisfying accepted trace — those stay #219.  The
balance is conditional on the previous-step timestamp chain (`a_reg_prev_mem_step = 0`,
`b_reg_prev_mem_step = 1`, `store_reg_prev_mem_step = 2`, reload at `3`), which ZisK's ordering/range
checks enforce (the #169/#19 axis, `main.pil:447`), pinned here in the concrete row.  `x0` is not
used: ZisK decodes `x0` operands as immediate/no-op register accesses emitting no `mem_op = 3`
traffic, so `x1,x1,x1` is the minimal real-register witness.

## Trust note

No axioms.  `pulledValue` / `pushedValue` are Clean's `-1` / `+1` value-level channel interactions.
-/

open Goldilocks
open ZiskFv.Channels.MemoryBus
open ZiskFv.AirsClean.Main (MainRowWithRom aRegPreMessage aMemMessage bRegPreMessage bMemMessage
  cRegPreMessage cMemMessage)
open ZiskFv.AirsClean.RegisterBoundary (RegisterBoundaryRow bootMessage reloadMessage)

namespace ZiskFv.Compliance.RegisterMemBusBalance

/-! ## Paired-interaction balance infrastructure (message-agnostic) -/

/-- One pull/push pair for the same MemBus message balances. -/
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

/-! ## The concrete `add x1,x1,x1` row and boundary rows -/

/-- The concrete register-register `add x1,x1,x1` Main row.  Register operands x1: the six MemBus
    pointers (`a_offset_imm0`/`b_offset_imm0`/`store_offset` and `addr0`/`addr1`/`addr2`) are `1`;
    the three register selectors are `1` and the memory selectors `0`; the previous-step chain is
    `0/1/2`; all values `0`; `store_pc = 0` collapses the c-value to `c_0 = 0`. -/
def addX1Row : MainRowWithRom FGL :=
  { core :=
      { a_0 := 0, a_1 := 0, b_0 := 0, b_1 := 0, c_0 := 0, c_1 := 0,
        flag := 0, pc := 0, is_external_op := 1, op := 0, m32 := 0,
        ind_width := 8, set_pc := 0, jmp_offset1 := 0, jmp_offset2 := 0,
        store_pc := 0, im_high_degree_2 := 0, segment_l1 := 1 }
    rom :=
      { a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 1, b_imm1 := 0,
        store_offset := 1, a_src_imm := 0, a_src_mem := 0, is_precompiled := 0,
        b_src_imm := 0, b_src_mem := 0, store_mem := 0, store_ind := 0,
        b_src_ind := 0, a_src_reg := 1, b_src_reg := 1, store_reg := 1,
        addr0 := 1, addr1 := 1, addr2 := 1, main_step := 0,
        a_reg_prev_mem_step := 0, b_reg_prev_mem_step := 1,
        store_reg_prev_mem_step := 2, store_reg_prev_value_0 := 0,
        store_reg_prev_value_1 := 0 } }

/-- Boundary row for register x1: reload closes the chain at the last access (ts 3), value 0. -/
def boundaryRowX1 : RegisterBoundaryRow FGL :=
  { reg := 1, reloadTimestamp := 3, reloadValue_0 := 0, reloadValue_1 := 0 }

/-- Boundary row for an idle tracked register `r`: boot and reload both at ts 0, value 0. -/
def boundaryRowIdle (r : FGL) : RegisterBoundaryRow FGL :=
  { reg := r, reloadTimestamp := 0, reloadValue_0 := 0, reloadValue_1 := 0 }

/-! ## The real-emission register interaction list for `add x1,x1,x1` -/

/-- Main's six register `mem_op=3` emissions for `add x1,x1,x1`, as value-level interactions with
    the emissions' own multiplicities: push-prev (selector `1`) as `pushedValue`, pull-current
    (selector `-1`) as `pulledValue`.  The messages are the real `Main/Bridge.lean` emission
    definitions instantiated at `addX1Row`. -/
def mainRegisterInteractions : List (Interaction FGL) :=
  [ MemBusChannel.pushedValue (aRegPreMessage addX1Row)
  , MemBusChannel.pulledValue (aMemMessage addX1Row)
  , MemBusChannel.pushedValue (bRegPreMessage addX1Row)
  , MemBusChannel.pulledValue (bMemMessage addX1Row)
  , MemBusChannel.pushedValue (cRegPreMessage addX1Row)
  , MemBusChannel.pulledValue (cMemMessage addX1Row) ]

/-- One register's boundary contribution: boot pull + reload push (real RegisterBoundary emission
    definitions), as value-level interactions. -/
def boundaryInteractions (row : RegisterBoundaryRow FGL) : List (Interaction FGL) :=
  [ MemBusChannel.pulledValue (bootMessage row)
  , MemBusChannel.pushedValue (reloadMessage row) ]

/-- Idle tracked registers x2..x31, each contributing a self-balancing boot/reload zero pair. -/
def idleBoundaryInteractions : List (Interaction FGL) :=
  (List.range 30).flatMap fun i => boundaryInteractions (boundaryRowIdle ((i + 2 : Nat) : FGL))

/-- The full register (`mem_op=3`) MemBus interaction list for `add x1,x1,x1`: Main's six emissions,
    x1's boot/reload, and the idle registers' boot/reload pairs. -/
def addX1X1X1RegisterInteractions : List (Interaction FGL) :=
  mainRegisterInteractions ++ boundaryInteractions boundaryRowX1 ++ idleBoundaryInteractions

/-! ## The register consistency equalities (the telescoping content)

Each Main emission message equals the boundary/adjacent emission it cancels against, because the
previous-step chain lines the timestamps up.  These are `rfl` at the concrete `addX1Row`. -/

theorem aRegPre_eq_boot : aRegPreMessage addX1Row = bootMessage boundaryRowX1 := rfl
theorem aMem_eq_bRegPre : aMemMessage addX1Row = bRegPreMessage addX1Row := rfl
theorem bMem_eq_cRegPre : bMemMessage addX1Row = cRegPreMessage addX1Row := rfl
theorem cMem_eq_reload : cMemMessage addX1Row = reloadMessage boundaryRowX1 := rfl

/-! ## The balance -/

/-- The register (`mem_op=3`) partition of the ensemble's MemBus emissions telescopes to zero for
    `add x1,x1,x1`, from the real component emission definitions: every distinct register message
    appears once as a pull and once as a push. -/
theorem addX1X1X1_registerMemBus_balanced :
    BalancedInteractions addX1X1X1RegisterInteractions := by
  -- Order-agnostic: over the messages actually present, every register message's ±1
  -- pull/push multiplicities sum to zero (the aRegPre↔boot, aMem↔bRegPre, bMem↔cRegPre,
  -- cMem↔reload chain plus the idle boot↔reload pairs — see the consistency equalities above).
  refine Air.Flat.balancedInteractions_of_present ?_
    (addX1X1X1RegisterInteractions.map (·.msg)) ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro i hi
    exact List.mem_map_of_mem hi
  · -- bounded quantifier over the concrete message list — decidable
    decide

end ZiskFv.Compliance.RegisterMemBusBalance
