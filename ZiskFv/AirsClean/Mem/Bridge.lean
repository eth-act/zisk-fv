import ZiskFv.AirsClean.Mem.Soundness
import ZiskFv.Airs.Mem

/-!
# `Valid_Mem` ↔ `MemRow` compatibility
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL) (r : ℕ) : MemRow FGL where
  addr := v.addr r
  step := v.step r
  sel := v.sel r
  addr_changes := v.addr_changes r
  step_dual := v.step_dual r
  sel_dual := v.sel_dual r
  value_0 := v.value_0 r
  value_1 := v.value_1 r
  wr := v.wr r
  previous_step := v.previous_step r
  increment_0 := v.increment_0 r
  increment_1 := v.increment_1 r
  read_same_addr := v.read_same_addr r

end ZiskFv.AirsClean.Mem
