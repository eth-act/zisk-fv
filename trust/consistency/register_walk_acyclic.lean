import ZiskFv.Compliance.RegisterWalk
import ZiskFv.Compliance.MemBusSlotSeparation
import ZiskFv.Compliance.RegisterBoundaryAnchor

/-!
# Register walk acyclicity (issue #342)

Pins the axiom closure of the #342 payoff theorems. V2 check 19 runs this file and *asserts* that
every `#print axioms` report below stays inside `{propext, Classical.choice, Quot.sound}`; it does
not merely print them.

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
    (h_pq : (traceWalkStep trace p).SuppliedBy (traceWalkStep trace q))
    (h_qp : (traceWalkStep trace q).SuppliedBy (traceWalkStep trace p)) : False :=
  not_traceWalkStep_two_cycle trace p q h_active_p h_active_q h_pq h_qp

/-- The register walk on an accepted trace visits no read timestamp twice, so it has no cycle of
    any length. -/
theorem register_walk_timestamps_nodup
    {n : Nat} (trace : AcceptedZiskTrace n) (steps : List (Fin n × RegSlot))
    (h_active : ∀ p ∈ steps, p.2.selector (traceWalkStep trace p).1 = 1)
    (h_chain : List.IsChain RegWalkStep.SuppliedBy (steps.map (traceWalkStep trace))) :
    ((steps.map (traceWalkStep trace)).map RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup_of_trace trace steps h_active h_chain

/-- Non-vacuity: the supply relation holds on a checked witness's real Main row, so the
    implications above are not empty. -/
theorem register_walk_non_vacuous :
    List.IsChain RegWalkStep.SuppliedBy
      [(ZiskFv.Compliance.RegisterMemBusBalance.addX1Row, RegSlot.a),
       (ZiskFv.Compliance.RegisterMemBusBalance.addX1Row, RegSlot.b),
       (ZiskFv.Compliance.RegisterMemBusBalance.addX1Row, RegSlot.c)] :=
  addX1Row_walk_isChain

/-- The chain result stated over exactly the rows the counterpart classification produces —
    every Main row of the witness, not only the executed prefix. -/
theorem register_walk_timestamps_nodup_on_witness_rows
    {n : Nat} (trace : AcceptedZiskTrace n) (steps : List RegWalkStep)
    (h_sites : ∀ p ∈ steps, IsActiveWitnessMainRow trace p)
    (h_chain : List.IsChain RegWalkStep.SuppliedBy steps) :
    (steps.map RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup_of_witnessRows trace steps h_sites h_chain

/-- Termination: from any witness site the walk reaches a site whose register read is supplied by
    the `RegisterBoundary`, and the chain that gets there is part of the statement — it starts at
    the site you asked about, every step of it is a witness site, and each step is supplied by the
    next. -/
theorem register_walk_terminates_at_boundary
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Air.Flat.Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.programLength trace.program).rowInputVar) = 1) :
    ∃ path : List RegWalkStep, ∃ last : RegWalkStep,
      path.head? = some
          (eval (table.environment row)
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar, s)
        ∧ path.getLast? = some last
        ∧ (∀ q ∈ path, IsActiveWitnessMainRow trace q)
        ∧ List.IsChain RegWalkStep.SuppliedBy path
        ∧ BoundarySuppliedAt trace last :=
  exists_boundaryWalk trace h_table h_component h_row s h_sel

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

/-- The walk lands on the reload, and that reload timestamp is a real read timestamp — so the
    boundary cannot answer its own boot pull. -/
theorem register_walk_boundary_is_reload
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          (eval (boundaryTable.environment boundaryRow)
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadTimestamp ≠ 0 :=
  boundary_reload_ne_boot trace h

/-- Non-vacuity for `BoundarySuppliedAt`'s payload: the reload of a register that *is* read carries
    that read's values, which is the fact the value telescope consumes. -/
theorem register_walk_boundary_carries_values
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          (eval (boundaryTable.environment boundaryRow)
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadValue_0
              = (p.2.readMessage p.1).value_0
            ∧ (eval (boundaryTable.environment boundaryRow)
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadValue_1
              = (p.2.readMessage p.1).value_1 :=
  boundarySuppliedAt_reload_values trace h

#print axioms register_walk_boundary_carries_values
#print axioms register_walk_boundary_is_reload
#print axioms register_walk_terminates_at_boundary
#print axioms register_access_is_a_pull
#print axioms register_walk_timestamps_nodup_on_witness_rows
#print axioms register_walk_no_two_cycle
#print axioms register_walk_timestamps_nodup
#print axioms register_walk_non_vacuous
#print axioms ZiskFv.Compliance.addX1Row_walk_timestamps_nodup
#print axioms ZiskFv.Compliance.registerRead_counterpart_of_witnessTable
#print axioms ZiskFv.Compliance.site_step
#print axioms ZiskFv.Compliance.exists_boundaryWalk
#print axioms ZiskFv.Compliance.boundaryWalk_timestamps_nodup
#print axioms ZiskFv.Compliance.regSlot_descent_of_trace
#print axioms ZiskFv.Compliance.regSlot_timestamp_bound_of_trace

end ZiskFv.TrustConsistency
