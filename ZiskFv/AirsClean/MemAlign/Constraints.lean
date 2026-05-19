import ZiskFv.AirsClean.MemAlign.Spec
import Clean.Circuit.Basic

/-!
# MemAlign circuit operations (Phase A4 partial)

The 14 per-row F-typed constraints captured here. The remaining
constraints (value_0/1 reconstruction, cross-row register/addr
continuity, delta_addr definition) are tracked as Phase A4.1.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  assertZero (row.wr * (1 - row.wr))
  assertZero (row.reset * (1 - row.reset))
  assertZero (row.sel_up_to_down * (1 - row.sel_up_to_down))
  assertZero (row.sel_down_to_up * (1 - row.sel_down_to_up))
  assertZero (row.sel_0 * (1 - row.sel_0))
  assertZero (row.sel_1 * (1 - row.sel_1))
  assertZero (row.sel_2 * (1 - row.sel_2))
  assertZero (row.sel_3 * (1 - row.sel_3))
  assertZero (row.sel_4 * (1 - row.sel_4))
  assertZero (row.sel_5 * (1 - row.sel_5))
  assertZero (row.sel_6 * (1 - row.sel_6))
  assertZero (row.sel_7 * (1 - row.sel_7))
  assertZero (row.preL1 * row.pc)
  assertZero (row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up))

end ZiskFv.AirsClean.MemAlign
