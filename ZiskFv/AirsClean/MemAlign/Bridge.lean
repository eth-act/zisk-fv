import ZiskFv.AirsClean.MemAlign.Circuit
import ZiskFv.Airs.MemAlign
import Extraction.LookupWiring

/-!
# `Valid_MemAlign` ↔ `MemAlignRow` compatibility

Connects the existing named-column `Valid_MemAlign` interface to the Clean
`MemAlignRow` representation, matching the bridge shape already used for
`MemAlignByte` and `MemAlignReadByte`.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.MemoryBus

/-- Generator acceptance check for the linked h998 compression constraint.
The structured tuple bridge below is intentionally checked alongside the
manifest's exact rfl identity rather than re-parsing an adjacent rendering. -/
example : Extraction.LookupWiring.constraint_MemAlign_36 =
    Extraction.LookupWiring.template_MemAlign_36 := by rfl

/-- Interpret the exact h998 slot AST in the two-row source model. The
fallback is unreachable for `hint_MemAlign_36_1`; it makes this syntax map
total without assigning any meaning to unrelated manifest terms. In
particular, witness `(1, 4, 1)` is deliberately the successor PC, not a
row-local cell. -/
@[reducible]
def h998ExprToField (current successor : MemAlignRow FGL) : Expr → FGL
  | .constant "0" => 0
  | .constant "1" => 1
  | .constant "2" => 2
  | .constant "4" => 4
  | .constant "8" => 8
  | .constant "16" => 16
  | .constant "32" => 32
  | .constant "64" => 64
  | .constant "128" => 128
  | .constant "256" => 256
  | .constant "512" => 512
  | .constant "1024" => 1024
  | .constant "2048" => 2048
  | .witness 1 1 0 => current.offset
  | .witness 1 2 0 => current.width
  | .witness 1 3 0 => current.wr
  | .witness 1 4 0 => current.pc
  | .witness 1 4 1 => successor.pc
  | .witness 1 5 0 => current.reset
  | .witness 1 6 0 => current.sel_up_to_down
  | .witness 1 7 0 => current.sel_down_to_up
  | .witness 1 16 0 => current.sel_0
  | .witness 1 17 0 => current.sel_1
  | .witness 1 18 0 => current.sel_2
  | .witness 1 19 0 => current.sel_3
  | .witness 1 20 0 => current.sel_4
  | .witness 1 21 0 => current.sel_5
  | .witness 1 22 0 => current.sel_6
  | .witness 1 23 0 => current.sel_7
  | .witness 1 25 0 => current.delta_addr
  | .add (.witness 1 1 0) (.constant "0") => current.offset
  | .add (.witness 1 2 0) (.constant "0") => current.width
  | .add (.witness 1 4 0) (.constant "0") => current.pc
  | .add (.witness 1 25 0) (.constant "0") => current.delta_addr
  | .add lhs rhs => h998ExprToField current successor lhs + h998ExprToField current successor rhs
  | .sub lhs rhs => h998ExprToField current successor lhs - h998ExprToField current successor rhs
  | .mul lhs rhs => h998ExprToField current successor lhs * h998ExprToField current successor rhs
  | _ => 0

/-- Project a legacy `Valid_MemAlign` row plus an explicitly preserved
`delta_pc` cell into the Clean row structure. The legacy record predates h998
and therefore has no column for this source-linked cell. -/
@[reducible]
def rowAtWithDelta (v : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ) (delta_pc : FGL) :
    MemAlignRow FGL where
  addr := v.addr r
  offset := v.offset r
  width := v.width r
  wr := v.wr r
  pc := v.pc r
  reset := v.reset r
  sel_up_to_down := v.sel_up_to_down r
  sel_down_to_up := v.sel_down_to_up r
  reg_0 := v.reg_0 r
  reg_1 := v.reg_1 r
  reg_2 := v.reg_2 r
  reg_3 := v.reg_3 r
  reg_4 := v.reg_4 r
  reg_5 := v.reg_5 r
  reg_6 := v.reg_6 r
  reg_7 := v.reg_7 r
  sel_0 := v.sel_0 r
  sel_1 := v.sel_1 r
  step := v.step r
  sel_2 := v.sel_2 r
  sel_3 := v.sel_3 r
  sel_4 := v.sel_4 r
  sel_5 := v.sel_5 r
  sel_6 := v.sel_6 r
  sel_7 := v.sel_7 r
  sel_prove := v.sel_prove r
  preL1 := v.preL1 r
  delta_addr := v.delta_addr r
  delta_pc := delta_pc
  value_0 := v.value_0 r
  value_1 := v.value_1 r

/-- The pre-h998 legacy projection has no `DELTA_PC` source, so its explicit
compatibility view is zero only. It is not used as the bus-133 soundness
source; that route uses `rowAtWithDelta` plus D3. -/
@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ) :
    MemAlignRow FGL :=
  rowAtWithDelta v r 0

/-- Constant-row legacy view of one Clean `MemAlignRow`. -/
@[reducible]
def validOfRow (row : MemAlignRow FGL) :
    ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL where
  addr := fun _ => row.addr
  offset := fun _ => row.offset
  width := fun _ => row.width
  wr := fun _ => row.wr
  pc := fun _ => row.pc
  reset := fun _ => row.reset
  sel_up_to_down := fun _ => row.sel_up_to_down
  sel_down_to_up := fun _ => row.sel_down_to_up
  reg_0 := fun _ => row.reg_0
  reg_1 := fun _ => row.reg_1
  reg_2 := fun _ => row.reg_2
  reg_3 := fun _ => row.reg_3
  reg_4 := fun _ => row.reg_4
  reg_5 := fun _ => row.reg_5
  reg_6 := fun _ => row.reg_6
  reg_7 := fun _ => row.reg_7
  sel_0 := fun _ => row.sel_0
  sel_1 := fun _ => row.sel_1
  sel_2 := fun _ => row.sel_2
  sel_3 := fun _ => row.sel_3
  sel_4 := fun _ => row.sel_4
  sel_5 := fun _ => row.sel_5
  sel_6 := fun _ => row.sel_6
  sel_7 := fun _ => row.sel_7
  step := fun _ => row.step
  delta_addr := fun _ => row.delta_addr
  sel_prove := fun _ => row.sel_prove
  value_0 := fun _ => row.value_0
  value_1 := fun _ => row.value_1
  preL1 := fun _ => row.preL1

/-- Concrete MemAlign memory-bus message:
`[wr + 1, addr * 8 + offset, step, width, value_0, value_1]`. -/
@[reducible]
def memBusMessage (row : MemAlignRow FGL) : MemBusMessage FGL :=
  { mem_op := row.wr + 1
    ptr := row.addr * 8 + row.offset
    timestamp := row.step
    width := row.width
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- Concrete bus-133 h998 tuple.  D3, rather than this row-local projection,
    establishes that `deltaPc` is the cyclic successor-PC difference. -/
@[reducible]
def memAlignRomMessage (row : MemAlignRow FGL) : ZiskFv.Channels.MemAlignRom.MemAlignRomMessage FGL :=
  { pc := row.pc
    deltaPc := row.delta_pc
    deltaAddr := row.delta_addr
    offset := row.offset
    width := row.width
    flags := row.sel_0 + row.sel_1 * 2 + row.sel_2 * 4 + row.sel_3 * 8 + row.sel_4 * 16 +
      row.sel_5 * 32 + row.sel_6 * 64 + row.sel_7 * 128 +
        (row.wr * 256 + row.reset * 512 + row.sel_up_to_down * 1024 +
          row.sel_down_to_up * 2048) }

/-- The h998 tuple expressed directly through the cyclic successor row.  This
is the source-linked form from `mem_align.pil:139-143`; its second slot is not
a caller-provided next-PC fact. -/
@[reducible]
def memAlignRomSuccessorMessage
    (current successor : MemAlignRow FGL) : ZiskFv.Channels.MemAlignRom.MemAlignRomMessage FGL :=
  { pc := current.pc
    deltaPc := successor.pc - current.pc
    deltaAddr := current.delta_addr
    offset := current.offset
    width := current.width
    flags := current.sel_0 + current.sel_1 * 2 + current.sel_2 * 4 + current.sel_3 * 8 +
      current.sel_4 * 16 + current.sel_5 * 32 + current.sel_6 * 64 + current.sel_7 * 128 +
        (current.wr * 256 + current.reset * 512 + current.sel_up_to_down * 1024 +
          current.sel_down_to_up * 2048) }

/-- The actual generated h998 slots, translated with its rotated PC witness
read through the successor row. -/
@[reducible]
def h998TupleFromLink (current successor : MemAlignRow FGL) : List FGL :=
  hint_MemAlign_36_1.slots.map (fun slot => h998ExprToField current successor slot.value)

/-- Field-list view of the live successor-indexed bus-133 model. -/
@[reducible]
def memAlignRomSuccessorTuple (current successor : MemAlignRow FGL) : List FGL :=
  let message := memAlignRomSuccessorMessage current successor
  [message.pc, message.deltaPc, message.deltaAddr, message.offset, message.width, message.flags]

/-- Proof-carrying acceptance binding for MemAlign's h998 lookup. `link` and
`romHint` identify the generated constraint-linked tuple, while
`sourceBinding` proves that its rotated witness slot is exactly the live D3
successor-row model. -/
structure MemAlignRomWiring where
  link : ValidatedLink
  rangeHint : HintTuple
  romHint : HintTuple
  memAlignLink : link = link_MemAlign_36
  linkedHints : link.hints = [rangeHint, romHint]
  romHintIndex : romHint.hintIndex = 998
  romBus : romHint.busId = Expr.constant "133"
  romIsAssumes : romHint.proves = false
  romMultiplicity : romHint.multiplicity = Expr.constant "1"
  sourceBinding : ∀ current successor,
    h998TupleFromLink current successor = memAlignRomSuccessorTuple current successor

@[reducible]
def h998Wiring : MemAlignRomWiring where
  link := link_MemAlign_36
  rangeHint := hint_MemAlign_36_0
  romHint := hint_MemAlign_36_1
  memAlignLink := rfl
  linkedHints := rfl
  romHintIndex := rfl
  romBus := rfl
  romIsAssumes := rfl
  romMultiplicity := rfl
  sourceBinding := by
    intro current successor
    rfl

/-- Lean-side acceptance cross-check: h998's actual generated six-slot tuple
is the live current/successor MemAlign model. D3 subsequently identifies this
model with the emitted row-local `delta_pc` tuple. -/
theorem h998_tuple_matches_successor_message
    (current successor : MemAlignRow FGL) :
    h998TupleFromLink current successor = memAlignRomSuccessorTuple current successor := by
  exact h998Wiring.sourceBinding current successor

/-- D3 turns the row-local consumer tuple into the exact successor-indexed
h998 tuple, including the intrinsic final-row-to-row-zero instance. -/
theorem memAlignRomMessage_eq_successorMessage_of_delta_pc_eq
    (current successor : MemAlignRow FGL)
    (h_delta_pc : current.delta_pc = successor.pc - current.pc) :
    memAlignRomMessage current = memAlignRomSuccessorMessage current successor := by
  rw [ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.mk.injEq]
  simp [h_delta_pc]

theorem eval_memBusMessageExpr
    (env : Environment FGL) (row : Var MemAlignRow FGL) :
    eval env (memBusMessageExpr row) = memBusMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [memBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

/-- Lean-side h998 tuple cross-check: the consumer expression is precisely
    the concrete `[pc, deltaPc, deltaAddr, offset, width, flags]` model. -/
theorem eval_memAlignRomMessageExpr
    (env : Environment FGL) (row : Var MemAlignRow FGL) :
    eval env (memAlignRomMessageExpr row) = memAlignRomMessage (eval env row) := by
  rw [ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.mk.injEq]
  simp only [memAlignRomMessageExpr, memAlignRomFlagsExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

end ZiskFv.AirsClean.MemAlign
