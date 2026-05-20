import Mathlib

import ZiskFv.Equivalence_v1.Blt
import ZiskFv.Equivalence_v1.Promises.BranchHelpers
import ZiskFv.SailSpec.blt
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_BLT` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BLT`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main


/-- **Compliance wrapper for `equiv_BLT`.** Pure pass-through to the
    canonical `equiv_BLT` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BLT
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence_v1.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLT)) state
      = (bus_effect ops.exec_row [] state).2 :=
  ZiskFv.Equivalence_v1.Blt.equiv_BLT
    state blt_input ops promises

end ZiskFv.Compliance
