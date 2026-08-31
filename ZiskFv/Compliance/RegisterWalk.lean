import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.Compliance.AcceptedZiskTrace.MemProviders
import ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridges
import ZiskFv.Compliance.Instantiation.ConcreteRowReductions
import ZiskFv.Compliance.RegisterMemBusBalance

/-!
# The register walk on an accepted trace

`ZiskFv/Compliance/Instantiation/ConcreteRowReductions.lean` states the supply relation on Main
rows and proves that one supply step moves strictly later in time, given that step's bus-102
descent and a no-wrap bound on the consumer's read timestamp. Both of those are hypotheses there.

This module discharges them from an `AcceptedZiskTrace` and nothing else:

* the **descent** comes from `rangeTable24_spec_distance_of_active`, which reads it off the
  witness's channel balance (`main.pil:333-335`, bus 102);
* the **no-wrap bound** comes from the Main table's own fixed-column capacity. `main_step` is
  indexed fixed data of capacity `mainFixedCapacity = 2^22`
  (`ZiskFv/AirsClean/Main/Circuit.lean:787`), so every read timestamp is below `2^24`. It is
  **not** a premise about segment length.

The result is `regSupplies_chain_timestamps_nodup_of_trace`: on an accepted trace, a chain of
register supply steps visits no read timestamp twice. This is the Main-side half of #342. It rules
out the disjoint cycle that balance alone permits.

`ZiskFv/Compliance/MemBusSlotSeparation.lean` then walks the chain to the `RegisterBoundary`. What
neither file does is pin *which* boundary message the chain lands on: that is `main.pil:447`, which
`ZiskFv/AirsClean/RegisterBoundary.lean` still omits (#348).
-/

namespace ZiskFv.Compliance

open Air.Flat (Table)
open ZiskFv.AirsClean.FullEnsemble (mainTableRowAtOrZero mainTableRowAtOrZero_get)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Compliance.Instantiation (RegSlot RegSupplies RegWalkStep
  rangeTable24_spec_distance_of_active readTimestamp_lt_of_regSupplies not_regSupplies_self
  not_regSupplies_two_cycle regSupplies_chain_timestamps_nodup)

variable {n : Nat}

/-- Any in-range Main row index is below the component's fixed-column capacity.

    This is `Table.index_lt_fixed_capacity` specialized to Main's indexed fixed schema. The bound is
    intrinsic to the table carrier, so it costs no premise. -/
theorem main_index_lt_mainFixedCapacity
    {length : Nat} {program : Program length} {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {index : Nat} (h_index : index < table.table.length) :
    index < ZiskFv.AirsClean.Main.mainFixedCapacity := by
  cases table with
  | mk component rawRows data raw_uniform_width fixed_domain =>
    change component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program at h_component
    subst component
    let table : Table FGL :=
      { component := ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
        rawRows := rawRows
        data := data
        raw_uniform_width := raw_uniform_width
        fixed_domain := fixed_domain }
    change index < table.table.length at h_index
    have h_columns :
        table.component.fixedColumns = some ZiskFv.AirsClean.Main.mainFixedColumns := by
      rfl
    have h_raw_index : index < table.length := by
      simpa only [Table.table_length] using h_index
    have h_capacity : index < ZiskFv.AirsClean.Main.mainFixedColumns.capacity :=
      Table.index_lt_fixed_capacity table ZiskFv.AirsClean.Main.mainFixedColumns h_columns
        ⟨index, h_raw_index⟩
    simpa [ZiskFv.AirsClean.Main.mainFixedColumns] using h_capacity

/-- **Every register read timestamp is far below the field's wrap point.**

    `main_step` is the row index, and the Main component's fixed schema caps the index at
    `mainFixedCapacity = 2^22`, so `k + main_step * 4 < 2^24` for `k ∈ {1, 2, 3}`. The `2^40` form
    is what `prev_val_lt_of_registerStepSpec` consumes. -/
theorem readTimestamp_val_lt_of_main_step_eq_index
    {row : ZiskFv.AirsClean.Main.MainRowWithRom FGL} {index : Nat}
    (h_step : row.rom.main_step = (index : FGL))
    (h_index : index < ZiskFv.AirsClean.Main.mainFixedCapacity)
    (s : RegSlot) :
    (s.readTimestamp row).val < 2 ^ 40 := by
  have h_capacity : index < 4194304 := by
    simpa [ZiskFv.AirsClean.Main.mainFixedCapacity] using h_index
  have h_prime : GL_prime = 18446744069414584321 := rfl
  have h_cast : ((index : FGL)).val = index := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h_mul : ((index : FGL) * 4).val = index * 4 := by
    rw [Fin.val_mul, h_cast]
    exact Nat.mod_eq_of_lt (by omega)
  cases s <;>
    simp only [RegSlot.readTimestamp, h_step, Fin.val_add, h_mul] <;>
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega

/-- The bus-102 descent for one slot of one executed step, read off the trace's channel balance. -/
theorem regSlot_descent_of_trace
    (trace : AcceptedZiskTrace n) (i : Fin n) (s : RegSlot)
    (h_active :
      s.selector (mainTableRowAtOrZero trace.program trace.mainTable i.val) = 1) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec
      (s.distance (mainTableRowAtOrZero trace.program trace.mainTable i.val)) := by
  have h_index : i.val < trace.mainTable.table.length := trace.mainTable_index i
  refine rangeTable24_spec_distance_of_active trace.channels_balanced trace.spec_holds
    trace.constraints_hold trace.mainTable_mem
    (List.get_mem trace.mainTable.table ⟨i.val, h_index⟩)
    ((mainTableRowAtOrZero_get trace.program trace.mainTable ⟨i.val, h_index⟩).symm)
    trace.mainTable_component s h_active

/-- **The no-wrap bound for any in-range Main row**, not only the executed steps.

    The walk's providers come out of `witness.allTables` and need not be indexed by `Fin n` — a
    padding row can carry a register-pre push exactly as an executed row can. So the bound has to
    cover every row of a Main-component table, and it does: `main_step` is indexed fixed data and
    the table's own `fixed_domain` caps the index at `mainFixedCapacity = 2^22`. -/
theorem regSlot_timestamp_bound_of_mainTable
    {length : Nat} {program : Program length} {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {index : Nat} (h_index : index < table.table.length) (s : RegSlot) :
    (s.readTimestamp (mainTableRowAtOrZero program table index)).val < 2 ^ 40 :=
  readTimestamp_val_lt_of_main_step_eq_index
    ((mainStepIndexFixedFacts_of_component_fixedColumns
      (numInstructions := table.table.length) program table h_component
      (fun i => i.isLt)).main_step_eq_index ⟨index, h_index⟩)
    (main_index_lt_mainFixedCapacity h_component h_index) s

/-- The no-wrap bound at an executed step, the special case the trace-indexed results use. -/
theorem regSlot_timestamp_bound_of_trace
    (trace : AcceptedZiskTrace n) (i : Fin n) (s : RegSlot) :
    (s.readTimestamp (mainTableRowAtOrZero trace.program trace.mainTable i.val)).val < 2 ^ 40 :=
  regSlot_timestamp_bound_of_mainTable trace.mainTable_component (trace.mainTable_index i) s

/-- **A walk step that really occurs in the witness**: some Main-component table of the witness, an
    in-range row of it, and a slot whose register selector is set.

    This is the shape the counterpart classification below *produces*, so it is the shape the chain
    results must consume. Indexing walk steps by `Fin n` would only cover executed steps, while a
    provider may be any row of the table — including a padding row past the executed prefix. -/
def IsActiveWitnessMainRow (trace : AcceptedZiskTrace n) (p : RegWalkStep) : Prop :=
  ∃ table ∈ trace.witness.allTables,
    table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program
      ∧ ∃ index, ∃ _h : index < table.table.length,
          p.1 = mainTableRowAtOrZero trace.program table index ∧ p.2.selector p.1 = 1

/-- A walk step named by an executed step index and a register slot. -/
noncomputable def traceWalkStep (trace : AcceptedZiskTrace n) (p : Fin n × RegSlot) :
    RegWalkStep :=
  (mainTableRowAtOrZero trace.program trace.mainTable p.1.val, p.2)

/-- **#342's concrete witness is impossible on an accepted trace.** Two Main rows whose register-pre
    pushes carry each other's read timestamps cannot both occur, for any pair of slots. -/
theorem not_traceWalkStep_two_cycle
    (trace : AcceptedZiskTrace n) (p q : Fin n × RegSlot)
    (h_active_p : p.2.selector (traceWalkStep trace p).1 = 1)
    (h_active_q : q.2.selector (traceWalkStep trace q).1 = 1)
    (h_pq : (traceWalkStep trace p).SuppliedBy (traceWalkStep trace q))
    (h_qp : (traceWalkStep trace q).SuppliedBy (traceWalkStep trace p)) : False :=
  not_regSupplies_two_cycle
    (regSlot_descent_of_trace trace p.1 p.2 h_active_p)
    (regSlot_descent_of_trace trace q.1 q.2 h_active_q)
    (regSlot_timestamp_bound_of_trace trace p.1 p.2)
    (regSlot_timestamp_bound_of_trace trace q.1 q.2)
    h_pq h_qp

/-- **The register walk on an accepted trace has no cycle of any length.**

    Quantified over the trace: every hypothesis except the chain itself and the per-step selector is
    discharged from `AcceptedZiskTrace`. A chain of supply steps visits no read timestamp twice, so
    the pairing that channel balance certifies cannot decompose into the boundary path plus a
    disjoint cycle *among Main rows*.

    **What this does not do.** It bounds the chain from below, not from above: nothing here forces
    the chain to reach `RegisterBoundary.bootMessage`. That anchor is `main.pil:447`, which the
    modeled `RegisterBoundary` still omits. -/
theorem regSupplies_chain_timestamps_nodup_of_trace
    (trace : AcceptedZiskTrace n) (steps : List (Fin n × RegSlot))
    (h_active : ∀ p ∈ steps, p.2.selector (traceWalkStep trace p).1 = 1)
    (h_chain : List.IsChain RegWalkStep.SuppliedBy (steps.map (traceWalkStep trace))) :
    ((steps.map (traceWalkStep trace)).map RegWalkStep.timestamp).Nodup := by
  refine regSupplies_chain_timestamps_nodup _ ?_ ?_ h_chain
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact regSlot_descent_of_trace trace p.1 p.2 (h_active p hp)
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact regSlot_timestamp_bound_of_trace trace p.1 p.2

/-- The descent for any active in-range row of any Main-component table of the witness. -/
theorem regSlot_descent_of_witnessMainRow
    (trace : AcceptedZiskTrace n) {p : RegWalkStep} (h_site : IsActiveWitnessMainRow trace p) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec p.distance := by
  obtain ⟨table, h_table, h_component, index, h_index, h_row, h_active⟩ := h_site
  show ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (p.2.distance p.1)
  rw [h_row] at h_active ⊢
  exact rangeTable24_spec_distance_of_active trace.channels_balanced trace.spec_holds
    trace.constraints_hold h_table (List.get_mem table.table ⟨index, h_index⟩)
    ((mainTableRowAtOrZero_get trace.program table ⟨index, h_index⟩).symm)
    h_component p.2 h_active

/-- The no-wrap bound for any in-range row of any Main-component table of the witness. -/
theorem regSlot_timestamp_bound_of_witnessMainRow
    (trace : AcceptedZiskTrace n) {p : RegWalkStep} (h_site : IsActiveWitnessMainRow trace p) :
    p.timestamp.val < 2 ^ 40 := by
  obtain ⟨table, h_table, h_component, index, h_index, h_row, h_active⟩ := h_site
  show (p.2.readTimestamp p.1).val < 2 ^ 40
  rw [h_row]
  exact regSlot_timestamp_bound_of_mainTable h_component h_index p.2

/-! ## From balance to the supply relation

Everything above takes the supply relation as given. This section derives it: on an accepted trace,
the counterpart of a Main register read is *either* the `RegisterBoundary` (boot or reload) *or*
another Main row's register-pre push, whose slot is itself active.

The read's `-1`-pull shape is still a hypothesis here. `ZiskFv/Compliance/MemBusSlotSeparation.lean`
discharges it from source exclusivity and assembles the walk (`site_step`, `exists_boundaryWalk`). -/

open ZiskFv.AirsClean.FullEnsemble (ActiveMainRegisterBoundaryProviderRowMatchSpec
  activeMainRegisterProviderRowMatchSpec_of_main_mem_op_three
  selfMemProvider_registerPre_active_of_mem_op_three)
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- A member row of a Main-component table is that table's `mainTableRowAtOrZero` at some in-range
    index. The classification returns rows by membership; `IsActiveWitnessMainRow` names them by
    index, and this is the bridge. -/
theorem exists_index_of_mem_mainTable
    {length : Nat} {program : Program length} {table : Table FGL}
    (_h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ∃ index, ∃ _h : index < table.table.length,
      eval (table.environment row)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar
        = mainTableRowAtOrZero program table index := by
  obtain ⟨⟨index, h_index⟩, h_get⟩ := List.get_of_mem h_row
  refine ⟨index, h_index, ?_⟩
  rw [mainTableRowAtOrZero_get program table ⟨index, h_index⟩, h_get]

/-- **The counterpart of a register read, classified.** From `channels_balanced` alone: a Main
    memory-bus pull at `mem_op = 3` is supplied either by the `RegisterBoundary` or by another Main
    row, and in the second case the supplying row's slot is *active* and its free
    `<slot>_reg_prev_mem_step` column holds this read's timestamp.

    The activity conjunct is what makes the second branch usable — it is exactly the premise the
    bus-102 descent needs. -/
theorem registerRead_counterpart_of_witnessTable
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainTable : Table FGL} (h_mainTable : mainTable ∈ trace.witness.allTables)
    {mainRow : Array FGL} (h_mainRow : mainRow ∈ mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_pull : mainInteraction.mult = -1)
    (h_mem_op : (eval (mainTable.environment mainRow) mainMsg).mem_op = 3)
    {multiplicity as : FGL} :
    ActiveMainRegisterBoundaryProviderRowMatchSpec trace.program trace.witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ∃ p : RegWalkStep, IsActiveWitnessMainRow trace p
          ∧ p.2.prevStep p.1 = (eval (mainTable.environment mainRow) mainMsg).timestamp := by
  have h_match :=
    (ZiskFv.AirsClean.FullEnsemble.activeMainMemProviderRowMatchSpec_of_active_main_eval
      trace.witness trace.channels_balanced trace.spec_holds h_mainTable h_mainRow
      h_mainInteraction h_mainEval h_pull (multiplicity := multiplicity) (as := as)).2
  rcases activeMainRegisterProviderRowMatchSpec_of_main_mem_op_three
      h_mainEval h_mem_op h_match with h_self | h_boundary
  · refine Or.inr ?_
    obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow, h_providerComponent,
      h_branch⟩ :=
      selfMemProvider_registerPre_active_of_mem_op_three h_mainEval h_mem_op
        trace.constraints_hold h_self
    obtain ⟨index, h_index, h_rowAt⟩ :=
      exists_index_of_mem_mainTable h_providerComponent h_providerRow
    refine
      match h_branch with
      | Or.inl ⟨h_sel, h_ts⟩ =>
          ⟨(_, RegSlot.a), ⟨providerTable, h_providerTable, h_providerComponent, index, h_index,
            h_rowAt, h_sel⟩, h_ts⟩
      | Or.inr (Or.inl ⟨h_sel, h_ts⟩) =>
          ⟨(_, RegSlot.b), ⟨providerTable, h_providerTable, h_providerComponent, index, h_index,
            h_rowAt, h_sel⟩, h_ts⟩
      | Or.inr (Or.inr ⟨h_sel, h_ts⟩) =>
          ⟨(_, RegSlot.c), ⟨providerTable, h_providerTable, h_providerComponent, index, h_index,
            h_rowAt, h_sel⟩, h_ts⟩
  · exact Or.inl h_boundary

/-- A row given by membership, with its slot selector set, is a walk site. The counterpart
    classification hands rows back by membership while `IsActiveWitnessMainRow` names them by index;
    this is that direction of `exists_index_of_mem_mainTable`. -/
theorem isActiveWitnessMainRow_of_mem
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.programLength trace.program).rowInputVar) = 1) :
    IsActiveWitnessMainRow trace
      (eval (table.environment row)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar, s) := by
  obtain ⟨index, h_index, h_rowAt⟩ := exists_index_of_mem_mainTable h_component h_row
  exact ⟨table, h_table, h_component, index, h_index, h_rowAt, h_sel⟩

/-! ## The chain result, on the rows the classification actually produces

`regSupplies_chain_timestamps_nodup_of_trace` above is indexed by `Fin n`, so it only speaks about
executed steps. `registerRead_counterpart_of_witnessTable` produces providers out of
`witness.allTables`, which may be padding rows past the executed prefix. This section states the
chain result over `IsActiveWitnessMainRow`, the shape the classification returns, so the two
compose. -/

/-- **No cycle, over exactly the rows the counterpart classification produces.**

    Both hypotheses of the row-local no-cycle theorem are discharged from the trace, and the walk
    steps range over every Main row of the witness rather than only the executed prefix. This is the
    form that consumes the path `exists_boundaryWalk` builds. -/
theorem regSupplies_chain_timestamps_nodup_of_witnessRows
    (trace : AcceptedZiskTrace n) (steps : List RegWalkStep)
    (h_sites : ∀ p ∈ steps, IsActiveWitnessMainRow trace p)
    (h_chain : List.IsChain RegWalkStep.SuppliedBy steps) :
    (steps.map RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup steps
    (fun p hp => regSlot_descent_of_witnessMainRow trace (h_sites p hp))
    (fun p hp => regSlot_timestamp_bound_of_witnessMainRow trace (h_sites p hp))
    h_chain

/-! ## Non-vacuity

The supply relation is inhabited, and by a row of a checked witness rather than a hand-built one.
On the `add x1,x1,x1` row all three register slots are active and the accesses run at timestamps
`1`, `2`, `3`, so within that single row the b-slot supplies the a-slot's read and the store-slot
supplies the b-slot's read. That is a legal configuration, not a cycle: it is exactly the
strictly-increasing walk the theorems above describe, and the same row is what
`singleAddWitness`'s bus-102 provider list `[0, 0, 0]` records.

This matters because every result in this file is an implication out of `RegSupplies`. If the
relation were empty the implications would hold vacuously and prove nothing about ZisK. -/

open ZiskFv.Compliance.RegisterMemBusBalance (addX1Row)

/-- The `add x1,x1,x1` row's b-slot supplies its own a-slot register read: `b_reg_prev_mem_step`
    is `1`, which is the a-slot's read timestamp. -/
theorem addX1Row_regSupplies_a_b : RegSupplies RegSlot.a RegSlot.b addX1Row addX1Row := by
  show addX1Row.rom.b_reg_prev_mem_step = 1 + addX1Row.rom.main_step * 4
  decide

/-- The `add x1,x1,x1` row's store-slot supplies its own b-slot register read. -/
theorem addX1Row_regSupplies_b_c : RegSupplies RegSlot.b RegSlot.c addX1Row addX1Row := by
  show addX1Row.rom.store_reg_prev_mem_step = 2 + addX1Row.rom.main_step * 4
  decide

/-- The three slots of the `add x1,x1,x1` row form a genuine supply chain. -/
theorem addX1Row_walk_isChain :
    List.IsChain RegWalkStep.SuppliedBy
      [(addX1Row, RegSlot.a), (addX1Row, RegSlot.b), (addX1Row, RegSlot.c)] := by
  rw [List.isChain_cons_cons]
  refine ⟨addX1Row_regSupplies_a_b, ?_⟩
  rw [List.isChain_cons_cons]
  exact ⟨addX1Row_regSupplies_b_c, List.isChain_singleton _⟩

/-- The `add x1,x1,x1` row's three bus-102 distances are all `0`, so each is in `rangeTable24`. -/
theorem addX1Row_descent (s : RegSlot) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (s.distance addX1Row) := by
  cases s
  · show (RegSlot.a.distance addX1Row).val < 2 ^ 24; decide
  · show (RegSlot.b.distance addX1Row).val < 2 ^ 24; decide
  · show (RegSlot.c.distance addX1Row).val < 2 ^ 24; decide

/-- The `add x1,x1,x1` row's three read timestamps are `1`, `2`, `3`. -/
theorem addX1Row_timestamp_bound (s : RegSlot) : (s.readTimestamp addX1Row).val < 2 ^ 40 := by
  cases s
  · show (RegSlot.a.readTimestamp addX1Row).val < 2 ^ 40; decide
  · show (RegSlot.b.readTimestamp addX1Row).val < 2 ^ 40; decide
  · show (RegSlot.c.readTimestamp addX1Row).val < 2 ^ 40; decide

/-- The general no-cycle theorem, applied to that chain: its read timestamps are `1`, `2`, `3` and
    they do not repeat. Non-vacuous instantiation of `regSupplies_chain_timestamps_nodup`. -/
theorem addX1Row_walk_timestamps_nodup :
    ([(addX1Row, RegSlot.a), (addX1Row, RegSlot.b), (addX1Row, RegSlot.c)].map
      RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup _
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact addX1Row_descent RegSlot.a
      rcases List.mem_cons.mp hp with rfl | hp
      · exact addX1Row_descent RegSlot.b
      rcases List.mem_cons.mp hp with rfl | hp
      · exact addX1Row_descent RegSlot.c
      · exact absurd hp (by simp))
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact addX1Row_timestamp_bound RegSlot.a
      rcases List.mem_cons.mp hp with rfl | hp
      · exact addX1Row_timestamp_bound RegSlot.b
      rcases List.mem_cons.mp hp with rfl | hp
      · exact addX1Row_timestamp_bound RegSlot.c
      · exact absurd hp (by simp))
    addX1Row_walk_isChain

end ZiskFv.Compliance
