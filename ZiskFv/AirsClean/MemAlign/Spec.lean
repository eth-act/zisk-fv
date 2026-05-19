import ZiskFv.AirsClean.MemAlign.Row

/-!
# MemAlign Spec + Assumptions (boolean invariants only)

MemAlign has 25 F-typed constraints covering memory-alignment
multiplexers and the register-byte chain. Capturing the full Spec
(byte-aligned memory access semantics) requires substantial
algebraic specification. The Spec below covers just the boolean
invariants on the selector columns — the algebraic content is
follow-up work.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

def Assumptions (row : MemAlignRow FGL) : Prop :=
  row.wr.val < 2 ∧ row.reset.val < 2
  ∧ row.sel_up_to_down.val < 2 ∧ row.sel_down_to_up.val < 2
  ∧ row.sel_0.val < 2 ∧ row.sel_1.val < 2

/-- Per-row boolean invariants — the F-typed constraints' simplest
    clauses (selectors / write / reset are booleans). -/
def Spec (row : MemAlignRow FGL) : Prop :=
  row.wr * (1 - row.wr) = 0
  ∧ row.reset * (1 - row.reset) = 0
  ∧ row.sel_up_to_down * (1 - row.sel_up_to_down) = 0
  ∧ row.sel_down_to_up * (1 - row.sel_down_to_up) = 0
  ∧ row.sel_0 * (1 - row.sel_0) = 0
  ∧ row.sel_1 * (1 - row.sel_1) = 0

end ZiskFv.AirsClean.MemAlign
