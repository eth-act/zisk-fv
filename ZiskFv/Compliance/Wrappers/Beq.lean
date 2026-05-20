import Mathlib

import ZiskFv.EquivCore.Beq
import ZiskFv.EquivCore.Promises.BranchHelpers
import ZiskFv.SailSpec.beq
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_BEQ` trust-discharge wrapper — ControlFlow branches shape exemplar

This wrapper is now a pure pass-through. The previous internal derivation of
`(not_throws, success)` from `h_target_aligned` (via the private theorem
`beq_pure_no_exception_of_aligned`) has been hoisted into
`Equivalence/Promises/BranchHelpers.lean` as
`BranchPromises.of_aligned_BEQ`. Callers that previously supplied
`h_target_aligned` should now use that helper to construct a full
`BranchPromises` bundle and pass it here.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

/-- **Trust-discharged wrapper for `equiv_BEQ`.** Pure pass-through to
    the canonical `equiv_BEQ` over a fully-constructed `BranchPromises`
    bundle. -/
theorem equiv_BEQ
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BEQ)) state
      = (bus_effect ops.exec_row [] state).2 :=
  ZiskFv.EquivCore.Beq.equiv_BEQ
    state beq_input ops promises

end ZiskFv.Compliance
