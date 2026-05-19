import ZiskFv.Vm.Probe_Branch

/-!
# `equiv_BGE_v2` per-opcode alias

Re-exports `equiv_BGE_v2` from `ZiskFv/Vm/Probe_Branch.lean` under the
canonical per-opcode layout that mirrors `ZiskFv/Equivalence/Bge.lean`.
The Phase 6 cutover renames this directory to `ZiskFv/Equivalence/`.

## Trust note

No axioms. Pure alias of `ZiskFv.Vm.Probe.equiv_BGE_v2`.
-/

namespace ZiskFv.Equivalence_v2

@[reducible] def equiv_BGE_v2 := @ZiskFv.Vm.Probe.equiv_BGE_v2

end ZiskFv.Equivalence_v2
