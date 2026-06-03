import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `FencePromises` — degenerate bundle for FENCE

Single-opcode bundle covering FENCE's 6 structural binders. FENCE is
the only RV64IM opcode with no memory-bus interaction; the bundle
exists for uniformity with the other shapes (so the canonical
theorem reads `equiv_FENCE (promises : FencePromises ...)` like the
others).
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- 6-field bundle for FENCE. -/
structure FencePromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_pc : BitVec 64) (pure_nextPC : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) where
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  input_priv_eq : state.regs.get? Register.cur_privilege = .some Privilege.Machine
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC

end ZiskFv.EquivCore.Promises
