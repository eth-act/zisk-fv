import Extraction.Arith
import Extraction.LookupWiring

/-!
# Arith operation-result extraction pins

Small source-syntax pins that must elaborate before the larger semantic
operation-bus translation in `ArithMul.Wiring`.
-/

namespace ZiskFv.AirsClean.ArithMul

open Extraction.LookupWiring

/-- Source-shaped value of the c61 `bus_res0` slot. Rounds 38 and 46
exchange one pair of 16-bit limbs in this expression. -/
def arithBusRes0Expr : Expr :=
  .add
    (.add
      (.add
        (.mul
          (.sub (.sub (.constant "1") (.witness 1 34 0)) (.witness 1 33 0))
          (.add (.witness 1 19 0) (.mul (.witness 1 20 0) (.constant "65536"))))
        (.mul
          (.witness 1 34 0)
          (.add (.witness 1 15 0) (.mul (.witness 1 16 0) (.constant "65536")))))
      (.mul
        (.witness 1 33 0)
        (.add (.witness 1 7 0) (.mul (.witness 1 8 0) (.constant "65536")))))
    (.constant "0")

/-- The generated c61 operation result is pinned before the larger semantic
slot translation is elaborated. -/
theorem arithBusRes0SlotPinned :
    hint_Arith_61_0.slots[5]? =
      some { name := "bus_res0", value := arithBusRes0Expr } := by
  rfl

end ZiskFv.AirsClean.ArithMul
