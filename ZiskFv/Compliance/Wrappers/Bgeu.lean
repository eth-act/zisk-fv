import Mathlib

import ZiskFv.EquivCore.Bgeu
import ZiskFv.EquivCore.Promises.BranchHelpers
import ZiskFv.SailSpec.bgeu
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_BGEU` Compliance wrapper — ControlFlow branches

Pure pass-through. The previous internal derivation lives in
`Equivalence/Promises/BranchHelpers.lean` (`BranchPromises.of_aligned_BGEU`).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main


/-- **Compliance wrapper for `equiv_BGEU`.** Pure pass-through to the
    canonical `equiv_BGEU` over a fully-constructed `BranchPromises`
    bundle. -/
lemma equiv_BGEU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGEU)) state
      = (bus_effect ops.exec_row [] state).2 :=
  ZiskFv.EquivCore.Bgeu.equiv_BGEU
    state bgeu_input ops promises

end ZiskFv.Compliance
