import ZiskFv.AirsClean.MemAlign.Circuit
import ZiskFv.Airs.MemAlign

/-!
# `Valid_MemAlign` ↔ `MemAlignRow` compatibility

Connects the existing named-column `Valid_MemAlign` interface to the Clean
`MemAlignRow` representation, matching the bridge shape already used for
`MemAlignByte` and `MemAlignReadByte`.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open ZiskFv.Channels.MemoryBus

/-- Project a legacy `Valid_MemAlign` row into the Clean row structure. -/
@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ) :
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
  value_0 := v.value_0 r
  value_1 := v.value_1 r

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

end ZiskFv.AirsClean.MemAlign
