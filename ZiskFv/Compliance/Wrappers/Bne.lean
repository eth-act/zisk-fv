import Mathlib

import ZiskFv.Equivalence.BranchNotEqual
import ZiskFv.Equivalence.Promises.BranchHelpers
import ZiskFv.SailSpec.bne
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_BNE` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BNE`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_BNE`.** Pure pass-through to the
    canonical `equiv_BNE` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BNE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BNE)) state
      = (bus_effect ops.exec_row [] state).2 :=
  ZiskFv.Equivalence.BranchNotEqual.equiv_BNE
    state bne_input ops promises

end ZiskFv.Compliance
