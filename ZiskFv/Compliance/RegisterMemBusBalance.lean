import Clean.Air.Balance
import ZiskFv.Channels.MemoryBus
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.Compliance.Instantiation.ConcreteRowReductions
import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.AirsClean.RegisterBoundary
import ZiskFv.RowShape.Contract

/-!
# Register MemBus balance for the `add x1,x1,x1` witness (from real component emissions)

Issue #225's register traffic is a telescoping MemBus argument.  For a register-register
instruction Main emits, per operand, a `MEMORY_REG_OP` (`mem_op = 3`) push-prev (the previous
register access) and a pull-current (the current access); the two chain-closing boundary terms —
boot (`global_init_mem`) and reload (`reg_pre_load`) — are emitted by the RegisterBoundary
component (`ZiskFv/AirsClean/RegisterBoundary.lean`).  All of these are now real composed-table
emissions in `fullRv64imEnsemble` (see `AirsClean/FullEnsemble.lean`).

This file proves that the normalized register (`mem_op = 3`) partition of those emissions
**telescopes to zero** for the minimal no-prelude real-register witness `add x1,x1,x1`.  Unlike the
earlier shape-demo, the balanced messages here are the **real component emission definitions**
(`aRegPreMessage`/`aMemMessage`/… from `Main/Bridge.lean`, `bootMessage`/`reloadMessage` from
RegisterBoundary) instantiated at a concrete `add x1,x1,x1` `MainRowWithRom`, not hand-authored
literals.  Their multiplicities are the emissions' own selectors: for `add x1,x1,x1` the push-prev
selectors `a_src_reg`/`b_src_reg`/`store_reg` are `1` and the pull selectors
`-(…_mem + … + …_reg)` are `-1`.

**Scope.** This is the register-partition balance (`BalancedInteractions` over the `mem_op = 3`
messages), the object #219 consumes.  It does **not** build the whole-channel
`witness.BalancedChannels` or the constraint-satisfying accepted trace — those stay #219.  The
concrete witness materializes the predecessor chain from the boot/access history; the resulting
timestamps are `0/1/2` with reload at `3`.  `x0` is not used: ZisK decodes `x0` operands as
immediate/no-op register accesses emitting no `mem_op = 3` traffic, so `x1,x1,x1` is the minimal
real-register witness.

This file also exposes the actual table interaction reductions for the concrete Main row and
RegisterBoundary rows.  The remaining #219 bridge is the projection from Main's evaluated
`interactionsWith` list to the normalized six-interaction list below.

## Trust note

No axioms. The local `emittedPulledValue` and Clean's `pushedValue` reproduce actual emitted
`-1` / `+1` value-level channel interactions, including their guarantee metadata.
-/

open Goldilocks
open ZiskFv.Channels.MemoryBus
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.Main (MainRowWithRom aRegPreMessage aMemMessage bRegPreMessage bMemMessage
  cRegPreMessage cMemMessage aRegPreMessageExpr aMemMessageExpr bRegPreMessageExpr
  bMemMessageExpr cRegPreMessageExpr cMemMessageExpr MainRomFreeCols)
open ZiskFv.AirsClean.RegisterBoundary (RegisterBoundaryRow bootMessage reloadMessage)
open ZiskFv.Compliance.Instantiation

namespace ZiskFv.Compliance.RegisterMemBusBalance

/-! ## Paired-interaction balance infrastructure (message-agnostic) -/

/-- A concrete negative MemBus emission. Unlike `Channel.pulledValue`, actual component emissions
    do not assume the channel guarantees, so this constructor keeps `assumeGuarantees := false`. -/
def emittedPulledValue (msg : MemBusMessage FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := -1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

/-- One pull/push pair for the same MemBus message balances. -/
def pairedInteraction (msg : MemBusMessage FGL) : List (Interaction FGL) :=
  [emittedPulledValue msg, MemBusChannel.pushedValue msg]

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
    simp [pairedInteraction, emittedPulledValue, balanceOf, Channel.pushedValue]

theorem balancedInteractions_append_of_balanced
    {left right : List (Interaction FGL)}
    (h_left : BalancedInteractions left)
    (h_right : BalancedInteractions right)
    (h_len : (left ++ right).length < ringChar FGL ∨ ringChar FGL = 0) :
    BalancedInteractions (left ++ right) := by
  refine ⟨h_len, ?_⟩
  intro msg
  rw [balanceOf_append, h_left.2 msg, h_right.2 msg, add_zero]

/-- A finite interaction list whose selectors are all zero is balanced. -/
theorem zeroInteractions_balanced
    (interactions : List (Interaction FGL))
    (h_zero : ∀ interaction ∈ interactions, interaction.mult = 0)
    (h_len : interactions.length < ringChar FGL ∨ ringChar FGL = 0) :
    BalancedInteractions interactions := by
  refine ⟨h_len, ?_⟩
  intro msg
  rw [balanceOf_eq_of_const_mult' h_zero]
  simp

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

/-! ## Register-access telescoping -/

/-- The real-emission order for successive accesses to one register. The boundary component emits
    the initial pull and final push first; every Main access then pushes its previous state and
    pulls its current state. -/
def registerAccessChain (previous : MemBusMessage FGL) :
    List (MemBusMessage FGL) → List (Interaction FGL)
  | [] => []
  | current :: rest =>
      [MemBusChannel.pushedValue previous, emittedPulledValue current] ++
        registerAccessChain current rest

/-- The last state in a nonempty register history represented by its first state and tail. -/
def registerLastMessage (first : MemBusMessage FGL) :
    List (MemBusMessage FGL) → MemBusMessage FGL
  | [] => first
  | current :: rest => registerLastMessage current rest

/-- Boundary emissions followed by the Main access chain for one register. -/
def registerTelescopingInteractions
    (first : MemBusMessage FGL) (rest : List (MemBusMessage FGL)) :
  List (Interaction FGL) :=
  [emittedPulledValue first,
    MemBusChannel.pushedValue (registerLastMessage first rest)] ++
      registerAccessChain first rest

/-- A register history contains one pull and one push of every state, independently of the
    boundary-first real-emission order. -/
theorem registerTelescopingInteractions_perm
    (first : MemBusMessage FGL) (rest : List (MemBusMessage FGL)) :
    List.Perm (registerTelescopingInteractions first rest)
      (pairedInteractions (first :: rest)) := by
  induction rest generalizing first with
  | nil =>
      rfl
  | cons current rest ih =>
      have h_rotate :
          List.Perm (registerTelescopingInteractions first (current :: rest))
            (pairedInteraction first ++ registerTelescopingInteractions current rest) := by
        simp only [registerTelescopingInteractions, registerLastMessage, registerAccessChain,
          pairedInteraction]
        exact List.Perm.cons _ <|
          (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ _))
      have h_tail :
          List.Perm (pairedInteraction first ++ registerTelescopingInteractions current rest)
            (pairedInteraction first ++ pairedInteractions (current :: rest)) :=
        List.Perm.append (List.Perm.refl _) (ih current)
      exact h_rotate.trans h_tail

/-- The N-access register telescope balances once its finite interaction count fits in the field. -/
theorem registerTelescopingInteractions_balanced
    (first : MemBusMessage FGL) (rest : List (MemBusMessage FGL))
    (h_len :
      (registerTelescopingInteractions first rest).length < ringChar FGL ∨
        ringChar FGL = 0) :
    BalancedInteractions (registerTelescopingInteractions first rest) := by
  have h_perm := registerTelescopingInteractions_perm first rest
  have h_paired_len :
      (pairedInteractions (first :: rest)).length < ringChar FGL ∨ ringChar FGL = 0 := by
    rw [← h_perm.length_eq]
    exact h_len
  exact balancedInteractions_of_perm
    (pairedInteractions_balanced (first :: rest) h_paired_len) h_perm.symm

/-! ## Register-access row materialization -/

/-- The Main register-access slots in the same predecessor/current order used by
    `registerAccessChain`. -/
inductive MainRegisterAccess
  | a
  | b
  | store

/-- The current message emitted by one Main register-access slot. -/
@[reducible]
def mainRegisterCurrentMessage (access : MainRegisterAccess)
    (row : MainRowWithRom FGL) : MemBusMessage FGL :=
  match access with
  | .a => aMemMessage row
  | .b => bMemMessage row
  | .store => cMemMessage row

/-- Fill one Main register-access predecessor from the preceding access message. -/
@[reducible]
def withMainRegisterPrevious (access : MainRegisterAccess)
    (previous : MemBusMessage FGL) (row : MainRowWithRom FGL) : MainRowWithRom FGL :=
  match access with
  | .a =>
      { row with rom := { row.rom with a_reg_prev_mem_step := previous.timestamp } }
  | .b =>
      { row with rom := { row.rom with b_reg_prev_mem_step := previous.timestamp } }
  | .store =>
      { row with rom :=
          { row.rom with
            store_reg_prev_mem_step := previous.timestamp
            store_reg_prev_value_0 := previous.value_0
            store_reg_prev_value_1 := previous.value_1 } }

/-- Materialize a row's active register predecessors by the same history walk as
    `registerAccessChain`. This is only a data construction: it introduces no trace assertion. -/
@[reducible]
def materializeMainRegisterAccesses
    (previous : MemBusMessage FGL) (row : MainRowWithRom FGL) :
    List MainRegisterAccess → MemBusMessage FGL × MainRowWithRom FGL
  | [] => (previous, row)
  | access :: rest =>
      let row := withMainRegisterPrevious access previous row
      materializeMainRegisterAccesses (mainRegisterCurrentMessage access row) row rest

/-- Build a concrete Main row and its final register state from an access history. -/
@[reducible]
def materializeMainRegisterRow (previous : MemBusMessage FGL) (row : MainRowWithRom FGL)
    (accesses : List MainRegisterAccess) : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterAccesses previous row accesses

/-- Set the register-predecessor free columns from an already materialized history state. -/
@[reducible]
def mainRomFreeColsWithRegisterPrevious (free : MainRomFreeCols)
    (previous : MemBusMessage FGL) : MainRomFreeCols :=
  { free with
    a_reg_prev_mem_step := previous.timestamp
    b_reg_prev_mem_step := previous.timestamp
    store_reg_prev_mem_step := previous.timestamp
    store_reg_prev_value_0 := previous.value_0
    store_reg_prev_value_1 := previous.value_1 }

/-- Recover the free Main columns from a materialized ROM-backed row. -/
@[reducible]
def mainRomFreeColsOfRow (row : MainRowWithRom FGL) : MainRomFreeCols :=
  { a_0 := row.core.a_0
    a_1 := row.core.a_1
    b_0 := row.core.b_0
    b_1 := row.core.b_1
    im_high_degree_2 := row.core.im_high_degree_2
    segment_l1 := row.core.segment_l1
    main_step := row.rom.main_step
    a_reg_prev_mem_step := row.rom.a_reg_prev_mem_step
    b_reg_prev_mem_step := row.rom.b_reg_prev_mem_step
    store_reg_prev_mem_step := row.rom.store_reg_prev_mem_step
    store_reg_prev_value_0 := row.rom.store_reg_prev_value_0
    store_reg_prev_value_1 := row.rom.store_reg_prev_value_1 }

/-- Reload data derived from the last access in a concrete register history. -/
@[reducible]
def registerBoundaryRowFromLast (reg : FGL) (last : MemBusMessage FGL) :
    RegisterBoundaryRow FGL :=
  { reg := reg
    reloadTimestamp := last.timestamp
    reloadValue_0 := last.value_0
    reloadValue_1 := last.value_1 }

/-! ## The concrete `add x1,x1,x1` row and boundary rows -/

/-! Register operands x1 use the six MemBus pointers
    (`a_offset_imm0`/`b_offset_imm0`/`store_offset` and `addr0`/`addr1`/`addr2`) at `1`;
    the three register selectors are `1` and the memory selectors `0`; the previous-step chain is
    materialized from the boot/access history; all values `0`; `store_pc = 0` collapses the c-value
    to `c_0 = 0`. -/
/-- Boundary row for an idle tracked register `r`: boot and reload both at ts 0, value 0. -/
def boundaryRowIdle (r : FGL) : RegisterBoundaryRow FGL :=
  { reg := r, reloadTimestamp := 0, reloadValue_0 := 0, reloadValue_1 := 0 }

/-- Initial x1 state for the concrete ADD access history. -/
@[reducible]
def addX1RegisterInitial : MemBusMessage FGL :=
  bootMessage (boundaryRowIdle 1)

/-- The ADD row before its active register predecessors are materialized. -/
@[reducible]
def addX1RowTemplate : MainRowWithRom FGL :=
  { core :=
      { a_0 := 0, a_1 := 0, b_0 := 0, b_1 := 0, c_0 := 0, c_1 := 0,
        flag := 0, pc := 0, is_external_op := 1, op := ZiskFv.Trusted.OP_ADD, m32 := 0,
        ind_width := 8, set_pc := 0, jmp_offset1 := 4, jmp_offset2 := 4,
        store_pc := 0, im_high_degree_2 := 0, segment_l1 := 1 }
    rom :=
      { a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 1, b_imm1 := 0,
        store_offset := 1, a_src_imm := 0, a_src_mem := 0, is_precompiled := 0,
        b_src_imm := 0, b_src_mem := 0, store_mem := 0, store_ind := 0,
        b_src_ind := 0, a_src_reg := 1, b_src_reg := 1, store_reg := 1,
        addr0 := 1, addr1 := 1, addr2 := 1, main_step := 0,
        a_reg_prev_mem_step := addX1RegisterInitial.timestamp,
        b_reg_prev_mem_step := addX1RegisterInitial.timestamp,
        store_reg_prev_mem_step := addX1RegisterInitial.timestamp,
        store_reg_prev_value_0 := addX1RegisterInitial.value_0,
        store_reg_prev_value_1 := addX1RegisterInitial.value_1 } }

/-- The final x1 state and ADD row produced by the concrete access history. -/
@[reducible]
def addX1RowWithLast : MemBusMessage FGL × MainRowWithRom FGL :=
  materializeMainRegisterRow addX1RegisterInitial addX1RowTemplate
    [MainRegisterAccess.a, MainRegisterAccess.b, MainRegisterAccess.store]

/-- The concrete register-register `add x1,x1,x1` Main row. -/
def addX1Row : MainRowWithRom FGL := addX1RowWithLast.2

/-- The ROM row matching `addX1Row`'s decoded selector pins. -/
def addX1ProgramRow : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 1, a_imm1 := 0, b_offset_imm0 := 1, b_imm1 := 0,
    ind_width := 8, op := ZiskFv.Trusted.OP_ADD, store_offset := 1, jmp_offset1 := 4,
    jmp_offset2 := 4, flags := 57409 }

/-- A one-instruction concrete program for the `add x1,x1,x1` witness. -/
def addX1Program : Program 1 := fun _ => addX1ProgramRow

/-- Boundary row for register x1, whose reload closes the materialized access history. -/
def boundaryRowX1 : RegisterBoundaryRow FGL :=
  registerBoundaryRowFromLast 1 addX1RowWithLast.1

/-! ## The real-emission register interaction list for `add x1,x1,x1` -/

/-- Main's six register `mem_op=3` emissions for `add x1,x1,x1`, extracted from the actual
    one-row Main table interaction reduction. -/
def mainRegisterInteractionsFromTable : List (Interaction FGL) :=
  mainMemBusInteractions 1 addX1Program addX1Row

/-- Main's six register `mem_op=3` emissions for `add x1,x1,x1`, extracted from the actual
    emission definitions and normalized to value-level interactions. -/
def mainRegisterInteractions : List (Interaction FGL) :=
  [ mainARegPreInteraction addX1Row
  , mainAMemInteraction addX1Row
  , mainBRegPreInteraction addX1Row
  , mainBMemInteraction addX1Row
  , mainCRegPreInteraction addX1Row
  , mainCMemInteraction addX1Row ]

/-- One register's boundary contribution extracted from the actual RegisterBoundary one-row table
    interaction reduction. -/
def boundaryInteractions (row : RegisterBoundaryRow FGL) : List (Interaction FGL) :=
  registerBoundaryMemBusInteractions row

/-- The concrete RegisterBoundary emissions in value-level interaction form. -/
theorem boundaryInteractions_eq_messages (row : RegisterBoundaryRow FGL) :
    boundaryInteractions row =
      [emittedPulledValue (bootMessage row), MemBusChannel.pushedValue (reloadMessage row)] := by
  rfl

/-- Idle tracked registers x2..x31, each contributing a self-balancing boot/reload zero pair. -/
def idleBoundaryInteractions : List (Interaction FGL) :=
  (List.range 30).flatMap fun i => boundaryInteractions (boundaryRowIdle ((i + 2 : Nat) : FGL))

/-- The full register (`mem_op=3`) MemBus interaction list for `add x1,x1,x1`: Main's six emissions,
    x1's boot/reload, and the idle registers' boot/reload pairs. -/
def addX1X1X1RegisterInteractions : List (Interaction FGL) :=
  mainRegisterInteractions ++ boundaryInteractions boundaryRowX1 ++ idleBoundaryInteractions

def addX1X1X1RegisterInteractionsFromTable : List (Interaction FGL) :=
  mainRegisterInteractionsFromTable ++ boundaryInteractions boundaryRowX1 ++
    idleBoundaryInteractions

theorem addX1Row_main_interactionsWith_memBus_eq_mainRegisterInteractionsFromTable :
    (mainSingleRowTable 1 addX1Program addX1Row).interactionsWith MemBusChannel.toRaw =
      mainRegisterInteractionsFromTable := by
  rw [mainSingleRowTable_interactionsWith_memBus]
  rfl

private def addX1MainEnv : Environment FGL :=
  mainSingleRowTableEnvironment 1 addX1Program addX1Row

private def addX1MainRowVar : Var MainRowWithRom FGL :=
  (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 1 addX1Program).rowInputVar

private theorem addX1MainRowVar_eval : eval addX1MainEnv addX1MainRowVar = addX1Row := by
  dsimp [addX1MainEnv, addX1MainRowVar]
  exact mainSingleRowTable_eval_rowInputVar 1 addX1Program addX1Row (by rfl) (by rfl)

private theorem addX1MainRom_eval :
    eval addX1MainEnv addX1MainRowVar.rom = addX1Row.rom := by
  rw [mainRowWithRom_eval_rom]
  exact congrArg MainRowWithRom.rom addX1MainRowVar_eval

private theorem addX1Main_a_src_reg_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.a_src_reg =
      addX1Row.rom.a_src_reg := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.a_src_reg =
        (eval addX1MainEnv addX1MainRowVar.rom).a_src_reg :=
      mainRomRow_eval_a_src_reg addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.a_src_reg := by rw [addX1MainRom_eval]

private theorem addX1Main_a_src_mem_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.a_src_mem =
      addX1Row.rom.a_src_mem := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.a_src_mem =
        (eval addX1MainEnv addX1MainRowVar.rom).a_src_mem :=
      mainRomRow_eval_a_src_mem addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.a_src_mem := by rw [addX1MainRom_eval]

private theorem addX1Main_b_src_reg_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.b_src_reg =
      addX1Row.rom.b_src_reg := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.b_src_reg =
        (eval addX1MainEnv addX1MainRowVar.rom).b_src_reg :=
      mainRomRow_eval_b_src_reg addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.b_src_reg := by rw [addX1MainRom_eval]

private theorem addX1Main_b_src_mem_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.b_src_mem =
      addX1Row.rom.b_src_mem := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.b_src_mem =
        (eval addX1MainEnv addX1MainRowVar.rom).b_src_mem :=
      mainRomRow_eval_b_src_mem addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.b_src_mem := by rw [addX1MainRom_eval]

private theorem addX1Main_b_src_ind_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.b_src_ind =
      addX1Row.rom.b_src_ind := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.b_src_ind =
        (eval addX1MainEnv addX1MainRowVar.rom).b_src_ind :=
      mainRomRow_eval_b_src_ind addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.b_src_ind := by rw [addX1MainRom_eval]

private theorem addX1Main_store_reg_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.store_reg =
      addX1Row.rom.store_reg := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.store_reg =
        (eval addX1MainEnv addX1MainRowVar.rom).store_reg :=
      mainRomRow_eval_store_reg addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.store_reg := by rw [addX1MainRom_eval]

private theorem addX1Main_store_mem_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.store_mem =
      addX1Row.rom.store_mem := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.store_mem =
        (eval addX1MainEnv addX1MainRowVar.rom).store_mem :=
      mainRomRow_eval_store_mem addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.store_mem := by rw [addX1MainRom_eval]

private theorem addX1Main_store_ind_eval :
    Expression.eval addX1MainEnv addX1MainRowVar.rom.store_ind =
      addX1Row.rom.store_ind := by
  calc
    Expression.eval addX1MainEnv addX1MainRowVar.rom.store_ind =
        (eval addX1MainEnv addX1MainRowVar.rom).store_ind :=
      mainRomRow_eval_store_ind addX1MainEnv addX1MainRowVar.rom
    _ = addX1Row.rom.store_ind := by rw [addX1MainRom_eval]

private theorem addX1MainARegPreMessage_eval :
    eval addX1MainEnv (aRegPreMessageExpr addX1MainRowVar) =
      aRegPreMessage addX1Row := by
  rw [ZiskFv.AirsClean.Main.eval_aRegPreMessageExpr, addX1MainRowVar_eval]

private theorem addX1MainAMemMessage_eval :
    eval addX1MainEnv (aMemMessageExpr addX1MainRowVar) =
      aMemMessage addX1Row := by
  rw [ZiskFv.AirsClean.Main.eval_aMemMessageExpr, addX1MainRowVar_eval]

private theorem addX1MainBRegPreMessage_eval :
    eval addX1MainEnv (bRegPreMessageExpr addX1MainRowVar) =
      bRegPreMessage addX1Row := by
  rw [ZiskFv.AirsClean.Main.eval_bRegPreMessageExpr, addX1MainRowVar_eval]

private theorem addX1MainBMemMessage_eval :
    eval addX1MainEnv (bMemMessageExpr addX1MainRowVar) =
      bMemMessage addX1Row := by
  rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr, addX1MainRowVar_eval]

private theorem addX1MainCRegPreMessage_eval :
    eval addX1MainEnv (cRegPreMessageExpr addX1MainRowVar) =
      cRegPreMessage addX1Row := by
  rw [ZiskFv.AirsClean.Main.eval_cRegPreMessageExpr, addX1MainRowVar_eval]

private theorem addX1MainCMemMessage_eval :
    eval addX1MainEnv (cMemMessageExpr addX1MainRowVar) =
      cMemMessage addX1Row := by
  rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr, addX1MainRowVar_eval]

private theorem addX1MainARegPreInteraction_eval :
    (((MemBusChannel.emitted addX1MainRowVar.rom.a_src_reg
        (aRegPreMessageExpr addX1MainRowVar)).toRaw).eval addX1MainEnv) =
      mainARegPreInteraction addX1Row := by
  simp [mainARegPreInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  constructor
  · exact addX1Main_a_src_reg_eval
  · rw [toElements_eval_toArray, addX1MainARegPreMessage_eval]

private theorem addX1MainAMemInteraction_eval :
    (((MemBusChannel.emitted (-(addX1MainRowVar.rom.a_src_mem +
        addX1MainRowVar.rom.a_src_reg))
        (aMemMessageExpr addX1MainRowVar)).toRaw).eval addX1MainEnv) =
      mainAMemInteraction addX1Row := by
  simp [mainAMemInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  constructor
  · simp [Expression.eval, addX1Main_a_src_mem_eval, addX1Main_a_src_reg_eval]
  · rw [toElements_eval_toArray, addX1MainAMemMessage_eval]

private theorem addX1MainBRegPreInteraction_eval :
    (((MemBusChannel.emitted addX1MainRowVar.rom.b_src_reg
        (bRegPreMessageExpr addX1MainRowVar)).toRaw).eval addX1MainEnv) =
      mainBRegPreInteraction addX1Row := by
  simp [mainBRegPreInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  constructor
  · exact addX1Main_b_src_reg_eval
  · rw [toElements_eval_toArray, addX1MainBRegPreMessage_eval]

private theorem addX1MainBMemInteraction_eval :
    (((MemBusChannel.emitted (-(addX1MainRowVar.rom.b_src_mem +
        addX1MainRowVar.rom.b_src_ind + addX1MainRowVar.rom.b_src_reg))
        (bMemMessageExpr addX1MainRowVar)).toRaw).eval addX1MainEnv) =
      mainBMemInteraction addX1Row := by
  simp [mainBMemInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  constructor
  · simp [Expression.eval, addX1Main_b_src_mem_eval, addX1Main_b_src_ind_eval,
      addX1Main_b_src_reg_eval]
  · rw [toElements_eval_toArray, addX1MainBMemMessage_eval]

private theorem addX1MainCRegPreInteraction_eval :
    (((MemBusChannel.emitted addX1MainRowVar.rom.store_reg
        (cRegPreMessageExpr addX1MainRowVar)).toRaw).eval addX1MainEnv) =
      mainCRegPreInteraction addX1Row := by
  simp [mainCRegPreInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  constructor
  · exact addX1Main_store_reg_eval
  · rw [toElements_eval_toArray, addX1MainCRegPreMessage_eval]

private theorem addX1MainCMemInteraction_eval :
    (((MemBusChannel.emitted (-(addX1MainRowVar.rom.store_mem +
        addX1MainRowVar.rom.store_ind + addX1MainRowVar.rom.store_reg))
        (cMemMessageExpr addX1MainRowVar)).toRaw).eval addX1MainEnv) =
      mainCMemInteraction addX1Row := by
  simp [mainCMemInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  constructor
  · simp [Expression.eval, addX1Main_store_mem_eval, addX1Main_store_ind_eval,
      addX1Main_store_reg_eval]
  · rw [toElements_eval_toArray, addX1MainCMemMessage_eval]

theorem mainRegisterInteractionsFromTable_eq_mainRegisterInteractions :
    mainRegisterInteractionsFromTable = mainRegisterInteractions := by
  change mainMemBusInteractions 1 addX1Program addX1Row =
    [ mainARegPreInteraction addX1Row
    , mainAMemInteraction addX1Row
    , mainBRegPreInteraction addX1Row
    , mainBMemInteraction addX1Row
    , mainCRegPreInteraction addX1Row
    , mainCMemInteraction addX1Row ]
  unfold mainMemBusInteractions
  simp only [List.cons.injEq, and_true]
  exact ⟨addX1MainARegPreInteraction_eval, addX1MainAMemInteraction_eval,
    addX1MainBRegPreInteraction_eval, addX1MainBMemInteraction_eval,
    addX1MainCRegPreInteraction_eval, addX1MainCMemInteraction_eval⟩

theorem registerBoundary_interactionsWith_memBus_eq_boundaryInteractions
    (row : RegisterBoundaryRow FGL) :
    (registerBoundarySingleRowTable row).interactionsWith MemBusChannel.toRaw =
      boundaryInteractions row := by
  rw [registerBoundarySingleRowTable_interactionsWith_memBus]
  rfl

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

theorem addX1X1X1_registerMemBus_fromTable_balanced :
    BalancedInteractions addX1X1X1RegisterInteractionsFromTable := by
  simpa [addX1X1X1RegisterInteractionsFromTable, addX1X1X1RegisterInteractions,
    mainRegisterInteractionsFromTable_eq_mainRegisterInteractions] using
      addX1X1X1_registerMemBus_balanced

end ZiskFv.Compliance.RegisterMemBusBalance
