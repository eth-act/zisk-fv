import ZiskFv.Compliance.RegisterWalk

/-!
# Register walk acyclicity (issue #342)

Keeps the axiom closure of the #342 payoff theorems visible to the semantic trust gate.

`main.pil:333-335`'s bus-102 range check bounds each Main row's register-step distance. Modelling it
(PR #345) supplies the descent; these theorems consume it. Together they say that on an accepted
trace the register supply relation strictly increases the memory-bus read timestamp, so the pairing
that `channels_balanced` certifies cannot contain a cycle among Main rows — the exact configuration
`#342` exhibits as a counterexample to the unmodelled circuit.

Every premise is discharged from `AcceptedZiskTrace`:

* the branch split from `channels_balanced`;
* the supplying row's slot activity from its counterpart multiplicity plus Main's own selector
  booleanity;
* the descent from the bus-102 provider slice;
* the no-wrap bound from the Main table's fixed-column capacity (`mainFixedCapacity = 2^22`), not
  from an assumption about segment length.
-/

namespace ZiskFv.TrustConsistency

open ZiskFv.Compliance
open ZiskFv.Compliance.Instantiation (RegSlot RegSupplies RegWalkStep)

/-- #342's concrete two-row witness is impossible on an accepted trace. -/
theorem register_walk_no_two_cycle
    {n : Nat} (trace : AcceptedZiskTrace n) (p q : Fin n × RegSlot)
    (h_active_p : p.2.selector (traceWalkStep trace p).1 = 1)
    (h_active_q : q.2.selector (traceWalkStep trace q).1 = 1)
    (h_pq : (traceWalkStep trace p).Supplies (traceWalkStep trace q))
    (h_qp : (traceWalkStep trace q).Supplies (traceWalkStep trace p)) : False :=
  not_traceWalkStep_two_cycle trace p q h_active_p h_active_q h_pq h_qp

/-- The register walk on an accepted trace visits no read timestamp twice, so it has no cycle of
    any length. -/
theorem register_walk_timestamps_nodup
    {n : Nat} (trace : AcceptedZiskTrace n) (steps : List (Fin n × RegSlot))
    (h_active : ∀ p ∈ steps, p.2.selector (traceWalkStep trace p).1 = 1)
    (h_chain : List.IsChain RegWalkStep.Supplies (steps.map (traceWalkStep trace))) :
    ((steps.map (traceWalkStep trace)).map RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup_of_trace trace steps h_active h_chain

#print axioms register_walk_no_two_cycle
#print axioms register_walk_timestamps_nodup
#print axioms ZiskFv.Compliance.registerRead_counterpart_of_trace
#print axioms ZiskFv.Compliance.registerRead_supplied_by_boundary_or_strictly_later_row
#print axioms ZiskFv.Compliance.regSlot_descent_of_trace
#print axioms ZiskFv.Compliance.regSlot_timestamp_bound_of_trace

end ZiskFv.TrustConsistency
