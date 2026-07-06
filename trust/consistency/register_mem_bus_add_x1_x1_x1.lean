import ZiskFv.Compliance.RegisterMemBusBalance

/-!
# Register MemBus balance witness for `add x1,x1,x1`

Gate-discovered wrapper for issue #225's checked register-memory-bus balance
artifact.  The theorem lives in main Lake under
`ZiskFv.Compliance.RegisterMemBusBalance`; this file keeps its axiom closure
visible to the semantic trust gate.
-/

namespace ZiskFv.TrustConsistency

open ZiskFv.Compliance.RegisterMemBusBalance

theorem register_mem_bus_add_x1_x1_x1_witness :
    BalancedInteractions (pairedInteractions addX1X1X1RegisterMessages) :=
  addX1X1X1_registerMemBus_balanced

#print axioms register_mem_bus_add_x1_x1_x1_witness

end ZiskFv.TrustConsistency
