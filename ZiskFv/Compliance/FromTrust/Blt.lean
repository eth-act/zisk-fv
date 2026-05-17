import Mathlib

import ZiskFv.Equivalence.BranchLessThan
import ZiskFv.Equivalence.Promises.BranchHelpers
import ZiskFv.SailSpec.blt
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_BLT` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BLT`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_BLT`.** Pure pass-through to the
    canonical `equiv_BLT` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BLT_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        imm r1 r2 exec_row) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2 :=
  ZiskFv.Equivalence.BranchLessThan.equiv_BLT
    state blt_input imm r1 r2 misa_val exec_row promises

end ZiskFv.Compliance
