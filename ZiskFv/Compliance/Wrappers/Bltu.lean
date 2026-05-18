import Mathlib

import ZiskFv.Equivalence.BranchLessThanUnsigned
import ZiskFv.Equivalence.Promises.BranchHelpers
import ZiskFv.SailSpec.bltu
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_BLTU` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BLTU`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_BLTU`.** Pure pass-through to the
    canonical `equiv_BLTU` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLTU)) state
      = (bus_effect ops.exec_row [] state).2 :=
  ZiskFv.Equivalence.BranchLessThanUnsigned.equiv_BLTU
    state bltu_input ops promises

end ZiskFv.Compliance
