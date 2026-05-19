import ZiskFv.AirsClean.MemAlign.Soundness
import ZiskFv.Airs.MemAlign

/-!
# `Valid_MemAlign` ↔ `MemAlignRow` compatibility
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL) (r : ℕ) :
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

end ZiskFv.AirsClean.MemAlign
