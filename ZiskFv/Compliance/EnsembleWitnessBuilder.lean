import Clean.Air.FlatEnsemble

/-!
# Forward `EnsembleWitness` builder + channel-balance combinator

Reusable, ZisK-agnostic machinery for constructing an `Air.Flat.EnsembleWitness`
from a position-indexed row assignment, together with a lemma-driven
`BalancedInteractions` combinator and the generic verifier-empty reductions of
`Constraints` / `BalancedChannels` to per-`tables` obligations.

This is the foundation for instantiating `ZiskFv.Compliance.root_soundness` on a
concrete accepted trace (eth-act/zisk-fv#217, feeding #218/#219). Nothing here is
ZisK-specific: everything is stated over an abstract `Air.Flat.Ensemble`.

The tree previously had no forward `EnsembleWitness` construction and no forward
`BalancedChannels` proof — every balance lemma ran the reverse direction
(projecting the hypothesis out). These are the first forward pieces.
-/

namespace Air.Flat

variable {F : Type} [Field F]

/-- **Channel-balance combinator.** To show an interaction list `L` is balanced it
    suffices to (a) bound its length below the field characteristic and (b) verify
    balance only for the messages that actually occur (`present`). A message absent
    from `L` balances automatically because its filter is empty.

    `Air.Flat.Interaction` has no `DecidableEq` (its `RawChannel` carries
    `Prop`-valued fields), so `BalancedInteractions` cannot be discharged by
    `decide`; this lemma is the finite-check replacement. The degenerate n=0 witness
    uses `present := []`; #219 will use the singleton shared message of a ±1
    push/pull pair (via `balanceOf_append`). -/
theorem balancedInteractions_of_present [DecidableEq F] {L : List (Interaction F)}
    (hlen : L.length < ringChar F ∨ ringChar F = 0)
    (present : List (Array F))
    (hmsg : ∀ i ∈ L, i.msg ∈ present)
    (hbal : ∀ msg ∈ present, balanceOf L msg = 0) :
    BalancedInteractions L := by
  refine ⟨hlen, fun msg => ?_⟩
  by_cases hp : msg ∈ present
  · exact hbal msg hp
  · have hfilter : L.filter (·.msg = msg) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi hpi
      simp only [decide_eq_true_eq] at hpi
      exact hp (hpi ▸ hmsg i hi)
    simp only [balanceOf, hfilter, List.map_nil, List.sum_nil]

namespace EnsembleWitness

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The `i`-th table of the builder: `ens.tables[i]` as its component, carrying the
    caller's `rows i`. Keeping this named (rather than an inline structure literal)
    keeps the projection/membership lemmas below clean `rfl`s. -/
def tableAt (ens : Ensemble F PublicIO) (data : ProverData F)
    (rows : Fin ens.tables.length → List (Array F))
    (huniform : ∀ i : Fin ens.tables.length,
        ∀ row ∈ rows i, row.size = (ens.tables[i.val]'i.isLt).width)
    (i : Fin ens.tables.length) : Table F where
  component := ens.tables[i.val]'i.isLt
  width := (ens.tables[i.val]'i.isLt).width
  table := rows i
  data := data
  uniform_width := huniform i

@[simp] lemma tableAt_component (ens : Ensemble F PublicIO) (data : ProverData F)
    (rows : Fin ens.tables.length → List (Array F)) (huniform) (i) :
    (tableAt ens data rows huniform i).component = ens.tables[i.val]'i.isLt := rfl

@[simp] lemma tableAt_table (ens : Ensemble F PublicIO) (data : ProverData F)
    (rows : Fin ens.tables.length → List (Array F)) (huniform) (i) :
    (tableAt ens data rows huniform i).table = rows i := rfl

@[simp] lemma tableAt_data (ens : Ensemble F PublicIO) (data : ProverData F)
    (rows : Fin ens.tables.length → List (Array F)) (huniform) (i) :
    (tableAt ens data rows huniform i).data = data := rfl

/-- Build an `EnsembleWitness ens` from a position-indexed row assignment. The
    `tables` list is `List.ofFn` over `Fin ens.tables.length`, so every built
    table's component is definitionally `ens.tables[i]` — making the three `same_*`
    obligations one-liners. Callers supply `rows` (per-table row lists) and a
    per-table `uniform_width` proof; #218/#219 supply non-empty `rows`, the
    degenerate #217 witness supplies `fun _ => []`. -/
def ofRows (ens : Ensemble F PublicIO) (data : ProverData F) (publicInput : PublicIO F)
    (rows : Fin ens.tables.length → List (Array F))
    (huniform : ∀ i : Fin ens.tables.length,
        ∀ row ∈ rows i, row.size = (ens.tables[i.val]'i.isLt).width) :
    EnsembleWitness ens where
  tables := List.ofFn (tableAt ens data rows huniform)
  data := data
  publicInput := publicInput
  same_length := by rw [List.length_ofFn]
  same_circuits := by intro i hi; simp only [List.getElem_ofFn, tableAt_component]
  same_data := by
    intro t h; rw [List.mem_ofFn] at h; obtain ⟨i, rfl⟩ := h; rfl

@[simp] lemma ofRows_tables (ens : Ensemble F PublicIO) (data : ProverData F)
    (publicInput : PublicIO F) (rows : Fin ens.tables.length → List (Array F)) (huniform) :
    (ofRows ens data publicInput rows huniform).tables =
      List.ofFn (tableAt ens data rows huniform) := rfl

@[simp] lemma ofRows_data (ens : Ensemble F PublicIO) (data : ProverData F)
    (publicInput : PublicIO F) (rows : Fin ens.tables.length → List (Array F)) (huniform) :
    (ofRows ens data publicInput rows huniform).data = data := rfl

@[simp] lemma ofRows_publicInput (ens : Ensemble F PublicIO) (data : ProverData F)
    (publicInput : PublicIO F) (rows : Fin ens.tables.length → List (Array F)) (huniform) :
    (ofRows ens data publicInput rows huniform).publicInput = publicInput := rfl

/-- With an empty verifier, `witness.Constraints` reduces to the per-`tables`
    obligation (the verifier table's own constraints are discharged by
    `verifierTable_constraints_of_verifier_empty`). -/
theorem constraints_of_tables {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (h_verifier : ens.verifier = .empty F PublicIO)
    (h : ∀ table ∈ witness.tables, table.Constraints) : witness.Constraints := by
  simp only [EnsembleWitness.Constraints, forall_mem_allTables_iff]
  exact ⟨verifierTable_constraints_of_verifier_empty h_verifier, h⟩

/-- With an empty verifier, `witness.BalancedChannels` reduces to per-channel balance
    of the `tables`-only interaction list (the verifier contributes none). -/
theorem balancedChannels_of_tables [DecidableEq F] {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (h_verifier : ens.verifier = .empty F PublicIO)
    (h : ∀ channel ∈ ens.channels,
        BalancedInteractions (witness.tables.flatMap (·.interactionsWith channel))) :
    witness.BalancedChannels := by
  simp only [EnsembleWitness.BalancedChannels, EnsembleWitness.BalancedChannel]
  intro channel h_mem
  rw [EnsembleWitness.interactionsWith_allTablesWitness,
      EnsembleWitness.interactionsWith_of_verifier_empty h_verifier]
  exact h channel h_mem

end EnsembleWitness
end Air.Flat
