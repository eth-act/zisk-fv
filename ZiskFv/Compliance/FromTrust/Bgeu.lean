import Mathlib

import ZiskFv.Equivalence.BranchGreaterEqualUnsigned
import ZiskFv.Equivalence.Promises.BranchHelpers
import ZiskFv.SailSpec.bgeu
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_BGEU` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BGEU`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_BGEU`.** Pure pass-through to the
    canonical `equiv_BGEU` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BGEU_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        imm r1 r2 exec_row) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = (bus_effect exec_row [] state).2 :=
  ZiskFv.Equivalence.BranchGreaterEqualUnsigned.equiv_BGEU
    state bgeu_input imm r1 r2 misa_val exec_row promises

end ZiskFv.Compliance
