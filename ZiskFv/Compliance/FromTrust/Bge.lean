import Mathlib

import ZiskFv.Equivalence.BranchGreaterEqual
import ZiskFv.Equivalence.Promises.BranchHelpers
import ZiskFv.SailSpec.bge
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_BGE` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BGE`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_BGE`.** Pure pass-through to the
    canonical `equiv_BGE` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BGE_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        imm r1 r2 exec_row) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) state
      = (bus_effect exec_row [] state).2 :=
  ZiskFv.Equivalence.BranchGreaterEqual.equiv_BGE
    state bge_input imm r1 r2 misa_val exec_row promises

end ZiskFv.Compliance
