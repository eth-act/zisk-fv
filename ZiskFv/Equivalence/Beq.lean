import ZiskFv.Vm.Probe_Branch

/-!
# `equiv_BEQ` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for BEQ. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_BEQ_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/Beq.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_BEQ_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Compliance (BranchInstrOperands)

namespace ZiskFv.Equivalence.Beq


theorem equiv_BEQ
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (ops : BranchInstrOperands)
    (promises : ZiskFv.Equivalence_v1.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row)
    : execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BEQ)) state
      = state_effect_via_channels ⟨ops.exec_row, []⟩ state :=
  ZiskFv.Vm.Probe.equiv_BEQ_v2 state beq_input ops promises

end ZiskFv.Equivalence.Beq
