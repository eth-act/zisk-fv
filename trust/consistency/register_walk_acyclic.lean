import ZiskFv.Compliance.RegisterWalk
import ZiskFv.Compliance.MemBusSlotSeparation

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
open Air.Flat

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

/-- Non-vacuity: the supply relation holds on a checked witness's real Main row, so the
    implications above are not empty. -/
theorem register_walk_non_vacuous :
    List.IsChain RegWalkStep.Supplies
      [(ZiskFv.Compliance.RegisterMemBusBalance.addX1Row, RegSlot.a),
       (ZiskFv.Compliance.RegisterMemBusBalance.addX1Row, RegSlot.b),
       (ZiskFv.Compliance.RegisterMemBusBalance.addX1Row, RegSlot.c)] :=
  addX1Row_walk_isChain

/-- The chain result stated over exactly the rows the counterpart classification produces —
    every Main row of the witness, not only the executed prefix. -/
theorem register_walk_timestamps_nodup_on_witness_rows
    {n : Nat} (trace : AcceptedZiskTrace n) (steps : List RegWalkStep)
    (h_sites : ∀ p ∈ steps, IsActiveWitnessMainRow trace p)
    (h_chain : List.IsChain RegWalkStep.Supplies steps) :
    (steps.map RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup_of_witnessRows trace steps h_sites h_chain

/-- Termination: from any witness site the walk reaches a site whose register read is supplied by
    the `RegisterBoundary`. -/
theorem register_walk_terminates_at_boundary
    {n : Nat} (trace : AcceptedZiskTrace n) (multiplicity as : FGL)
    {table : Air.Flat.Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.programLength trace.program).rowInputVar) = 1) :
    BoundarySuppliedSite trace multiplicity as :=
  exists_boundarySuppliedSite trace multiplicity as h_table h_component h_row s h_sel

/-- Source exclusivity, the fact termination rests on: every Main register access is a `-1` pull. -/
theorem register_access_is_a_pull
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Air.Flat.Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar) = 1) :
    (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
      (s.memMult (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar)
      (s.memMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar)).toRaw).eval (table.environment row)).mult = -1
    ∧ (eval (table.environment row)
        (s.memMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).mem_op = 3 :=
  regSlot_mem_pull_of_selector h_balanced h_constraints h_specs h_table h_component h_row s h_sel

#print axioms register_walk_terminates_at_boundary
#print axioms register_access_is_a_pull
#print axioms register_walk_timestamps_nodup_on_witness_rows
#print axioms register_walk_no_two_cycle
#print axioms register_walk_timestamps_nodup
#print axioms register_walk_non_vacuous
#print axioms ZiskFv.Compliance.addX1Row_walk_timestamps_nodup
#print axioms ZiskFv.Compliance.registerRead_counterpart_of_witnessTable
#print axioms ZiskFv.Compliance.registerRead_supplied_by_boundary_or_strictly_later_row
#print axioms ZiskFv.Compliance.regSlot_descent_of_trace
#print axioms ZiskFv.Compliance.regSlot_timestamp_bound_of_trace

end ZiskFv.TrustConsistency
