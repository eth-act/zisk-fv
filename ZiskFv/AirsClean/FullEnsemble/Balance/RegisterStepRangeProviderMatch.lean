import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction

/-!
# Full-ensemble bus-102 provider match

The bus-102 channel (`main.pil:333-335`, 24-bit) carries the **register-step descent**: for each
active register slot a Main row pulls `<slot>_mem_step - <slot>_reg_prev_mem_step - 1`, and the
`RegisterStepRangeSlice` provider pushes the same distance under its own `Spec`, which is
`rangeTable24.Spec`.

This file is the bus-102 twin of `RangeProviderMatch.lean`: balance turns a Main pull into a
same-message provider push, and the provider's `Spec` turns that push into the concrete 24-bit
membership fact. That fact is what rules out the register-telescope cycles described in #342 --
without it `a_reg_prev_mem_step` is a free witness column and two rows can point at each other's
timestamps.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges
  (SpecifiedRangeMessage SpecifiedRangesSliceChannel RegisterStepRangeChannel registerStepMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

private theorem registerStepRangeChannel_ne_memBus :
    RegisterStepRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "MemoryBus" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_opBus :
    RegisterStepRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "OperationBus" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_memAlignRom :
    RegisterStepRangeChannel.toRaw ≠ MemAlignRomChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "MemAlignRom133" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_specifiedRanges :
    RegisterStepRangeChannel.toRaw ≠ SpecifiedRangesSliceChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "SpecifiedRangesSlice103" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_memAlignRange :
    RegisterStepRangeChannel.toRaw ≠ ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "MemAlignRange107" at h_name
  simp at h_name

/-- The bus-102 interactions of an accepted witness balance, because the channel is one of the
six the ensemble finishes. -/
theorem registerStepRange_balanced_of_witness
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith RegisterStepRangeChannel.toRaw) := by
  have h := h_balanced RegisterStepRangeChannel.toRaw (by
    change RegisterStepRangeChannel.toRaw ∈
      [RegisterStepRangeChannel.toRaw,
        ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw,
        MemBusChannel.toRaw, OpBusChannel.toRaw, MemAlignRomChannel.toRaw,
        SpecifiedRangesSliceChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Every bus-102 interaction of the provider slice is a single push carrying that row's value. -/
theorem exists_registerStepRangeSlice_provider_row_of_interaction
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component)
    {interaction : Interaction FGL}
    (h_interaction : interaction ∈ table.interactionsWith RegisterStepRangeChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((RegisterStepRangeChannel.pushed
          (registerStepMessage
            ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  have h_singleton :
      table.component.operations.interactionsWith RegisterStepRangeChannel.toRaw =
        [((RegisterStepRangeChannel.pushed
          (registerStepMessage
            ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.RegisterStepRangeSlice.component_interactionsWith_rangeChannel
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_interaction
  exact h_interaction

/-- **The descent fact.** A bus-102 provider push carrying `value` forces
`rangeTable24.Spec value`: the provider's `Spec` is exactly 24-bit static-table membership, and
an accepted witness satisfies every table's `Spec`. -/
theorem rangeTable24_spec_of_registerStepRange_provider_interaction
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_specs : witness.Spec)
    {providerTable : Table FGL}
    (h_providerTable : providerTable ∈ witness.allTables)
    (h_providerComponent :
      providerTable.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component)
    {providerInteraction : Interaction FGL}
    (h_providerInteraction :
      providerInteraction ∈ providerTable.interactionsWith RegisterStepRangeChannel.toRaw)
    {value : FGL}
    (h_message : providerInteraction.msg = (toElements (registerStepMessage value)).toArray) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec value := by
  obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
    exists_registerStepRangeSlice_provider_row_of_interaction
      h_providerComponent h_providerInteraction
  have h_spec := h_specs providerTable h_providerTable providerRow h_providerRow
  rw [h_providerComponent] at h_spec
  rw [h_providerEval] at h_message
  have h_eval_message (env : Environment FGL) (value : Expression FGL) :
      Eval.eval env (registerStepMessage value) =
        registerStepMessage (Expression.eval env value) := by
    rw [SpecifiedRangeMessage.mk.injEq]
    simp only [registerStepMessage, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
      Expression.eval]
    repeat constructor
  rw [Channel.eval_pushed, h_eval_message] at h_message
  have h_value := congrArg (fun elements : Array FGL => elements[1]!) h_message
  have h_value' : valueFromOffset field 0 (providerTable.environment providerRow) = value := by
    simpa [Channel.pushedValue, registerStepMessage,
      ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
      ProvableStruct.components, ProvableStruct.toComponents,
      ProvableStruct.componentsToElements,
      ZiskFv.AirsClean.RegisterStepRangeSlice.component, Component.rowInputVar,
      ProvableType.varFromOffset] using h_value
  have h_providerSpec : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec
      (valueFromOffset field 0 (providerTable.environment providerRow)) := by
    simpa [Component.Spec, Component.rowInput,
      ZiskFv.AirsClean.RegisterStepRangeSlice.component,
      ZiskFv.AirsClean.RegisterStepRangeSlice.circuit,
      Component.rowInputVar] using h_spec
  simpa [h_value'] using h_providerSpec

/-- A field element satisfying `x * (1 - x) = 0` is `0` or `1`. -/
private theorem eq_zero_or_one_of_boolean {x : FGL} (h : x * (1 - x) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.mp h').symm

/-- The multiplicity of an evaluated bus-102 emission is its multiplicity expression, evaluated. -/
private theorem registerStepRange_emitted_eval_mult
    (env : Environment FGL) (m : Expression FGL) (msg : SpecifiedRangeMessage (Expression FGL)) :
    (((RegisterStepRangeChannel.emitted m msg).toRaw).eval env).mult = Expression.eval env m :=
  rfl

/-- **Main's bus-102 multiplicities are two-valued.** Every emission is `-<selector>`, and the
selectors are boolean by Main's own constraints, so a Main pull sits at `-1` or `0` -- never at the
`mult ∉ {0, -1}` a provider push would need. This is what lets `exists_push_of_pull` exclude Main
as its own counterpart, so the hypothesis no longer has to be assumed by the caller. -/
theorem main_registerStepRange_mult_cases
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_constraints : table.Constraints)
    {interaction : Interaction FGL}
    (h_interaction : interaction ∈ table.interactionsWith RegisterStepRangeChannel.toRaw) :
    interaction.mult = -1 ∨ interaction.mult = 0 := by
  rw [Table.interactionsWith] at h_interaction
  rcases List.mem_flatMap.mp h_interaction with ⟨row, h_row, h_mem⟩
  set env := table.environment row with h_env
  have h_holds :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).operations.ConstraintsHold
        env := by
    have := h_constraints row h_row
    rwa [h_component] at this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h_a, h_b, h_c⟩ :=
    ZiskFv.AirsClean.Main.romBoolSpec_of_componentWithRomMemAndOpBus_constraints
      length program env h_holds
  rw [h_component, Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_registerStepRange] at h_mem
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  -- each selector is boolean, so its negation is `0` or `-1`
  have step : ∀ x : Expression FGL, Expression.eval env (x * (1 - x)) = 0 →
      Expression.eval env (-x) = -1 ∨ Expression.eval env (-x) = 0 := by
    intro x hx
    have hx' : Expression.eval env x * (1 - Expression.eval env x) = 0 := by
      simpa [Expression.eval, sub_eq_add_neg] using hx
    rcases eq_zero_or_one_of_boolean hx' with h | h
    · exact Or.inr (by simp [Expression.eval, h])
    · exact Or.inl (by simp [Expression.eval, h])
  rcases h_mem with rfl | rfl | rfl
  · rw [registerStepRange_emitted_eval_mult]; exact step _ h_a
  · rw [registerStepRange_emitted_eval_mult]; exact step _ h_b
  · rw [registerStepRange_emitted_eval_mult]; exact step _ h_c

/-- **The descent, at the level of natural numbers.** `rangeTable24.Spec (memStep - prev - 1)` is a
statement about field elements, and field subtraction wraps; on its own it does not order the two
timestamps. Once the *predecessor* timestamp is small enough that `prev + d + 1` cannot wrap the
modulus, the range fact becomes a strict inequality: `prev.val < memStep.val`.

`2 ^ 40` is the bound stated here, with room to spare: `config.pil:1,3` set `MAIN_STEP_BITS = 36`
and `MEM_STEP_BITS = MAIN_STEP_BITS + 2`, so a real memory timestamp reaches `2 ^ 38`. An earlier
version of this lemma said `2 ^ 32`, which is below that ceiling and would have been unsatisfiable
for a full-length segment; it held only because the model currently pins the segment away.

Only the predecessor needs bounding — `memStep` is *derived* here, not assumed, so no hypothesis
about it is required.

This is the bridge from the bus-102 guarantee to a well-founded order, i.e. the reason the register
telescope terminates instead of admitting the 2-cycle in #342. -/
theorem prev_val_lt_of_registerStepSpec
    {memStep prev : FGL}
    (h_spec : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (memStep - prev - 1))
    (h_prev : prev.val < 2 ^ 40) :
    prev.val < memStep.val := by
  have h_d : (memStep - prev - 1 : FGL).val < 2 ^ 24 := h_spec
  have h_eq : memStep = (memStep - prev - 1) + prev + 1 := by ring
  have h_val : memStep.val
      = ((memStep - prev - 1).val + prev.val + 1) % GL_prime := by
    conv_lhs => rw [h_eq]
    simp [Fin.val_add, Nat.add_mod, Nat.mod_mod_of_dvd]
  have h_small : (memStep - prev - 1).val + prev.val + 1 < GL_prime := by
    have : GL_prime = 18446744069414584321 := rfl
    omega
  rw [Nat.mod_eq_of_lt h_small] at h_val
  omega

/-- A register chain linked by the bus-102 descent has strictly increasing timestamps.

Each counterpart step carries the earlier access's timestamp into the next row's
`<slot>_reg_prev_mem_step`, and that row's own bus-102 guarantee bounds
`<slot>_mem_step - <slot>_reg_prev_mem_step - 1`, so the step moves strictly forward in time. -/
theorem registerChain_strictMono_of_descent
    (timestamps : List FGL)
    (h_bounds : ∀ t ∈ timestamps, t.val < 2 ^ 40)
    (h_chain : List.IsChain (fun a b =>
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (b - a - 1)) timestamps) :
    List.IsChain (fun a b => a.val < b.val) timestamps := by
  induction timestamps with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          rw [List.isChain_cons_cons] at h_chain
          rw [List.isChain_cons_cons]
          exact ⟨prev_val_lt_of_registerStepSpec h_chain.1 (h_bounds a (by simp)),
            ih (fun t ht => h_bounds t (by simp [ht])) h_chain.2⟩

/-- A list of timestamps linked by the bus-102 descent has no repeats, because strictly increasing
values cannot return to their start.

**Scope, stated precisely.** This quantifies over an arbitrary `List FGL` and assumes both the
chain relation and the bounds. Nothing here builds such a list out of a witness, so this lemma on
its own does *not* yet establish that an accepted trace's register partition avoids a disjoint
cycle. It is the order-theoretic half; the walk that extracts the list from the counterpart
relation is the remaining work on #342. -/
theorem registerChain_nodup_of_descent
    (timestamps : List FGL)
    (h_bounds : ∀ t ∈ timestamps, t.val < 2 ^ 40)
    (h_chain : List.IsChain (fun a b =>
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (b - a - 1)) timestamps) :
    timestamps.Nodup := by
  have h_mono := registerChain_strictMono_of_descent timestamps h_bounds h_chain
  haveI : Trans (fun a b : FGL => a.val < b.val) (fun a b : FGL => a.val < b.val)
      (fun a b : FGL => a.val < b.val) := ⟨fun h1 h2 => Nat.lt_trans h1 h2⟩
  have h_pairwise : timestamps.Pairwise (fun a b => a.val < b.val) :=
    h_mono.pairwise
  exact h_pairwise.imp (fun {a b} h h_eq => absurd (congrArg Fin.val h_eq) (Nat.ne_of_lt h))

/-- **Balance turns a bus-102 pull into a provider push.** Every component other than the
`RegisterStepRangeSlice` provider is silent on bus 102 except Main, and Main only ever emits at
multiplicity `-a_src_reg` and friends, which `exists_push_of_pull` excludes by returning a
counterpart with `mult ≠ -1` and `mult ≠ 0` -- so the counterpart is the provider. -/
theorem exists_registerStepRange_provider_of_pull
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints)
    {pullTable : Table FGL}
    (h_pullTable : pullTable ∈ witness.allTables)
    {pull : Interaction FGL}
    (h_pull : pull ∈ pullTable.interactionsWith RegisterStepRangeChannel.toRaw)
    (h_active : pull.mult = -1) :
    ∃ providerTable ∈ witness.allTables,
      providerTable.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component
        ∧ ∃ providerInteraction ∈ providerTable.interactionsWith RegisterStepRangeChannel.toRaw,
          providerInteraction.msg = pull.msg := by
  have h_pullWitness : pull ∈ witness.interactionsWith RegisterStepRangeChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨pullTable, h_pullTable, h_pull⟩
  obtain ⟨provider, h_providerWitness, h_message, h_nonzero, h_nonpull⟩ :=
    exists_push_of_pull (witness.interactionsWith RegisterStepRangeChannel.toRaw)
      (registerStepRange_balanced_of_witness witness h_balanced) pull h_pullWitness h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_providerWitness
  obtain ⟨providerTable, h_providerTable, h_providerInteraction⟩ := h_providerWitness
  have h_componentMem :
      providerTable.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_providerTable
  rcases component_mem_fullRv64im_cases h_componentMem with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exfalso
    have h_nil : providerTable.interactionsWith RegisterStepRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h]
      change RegisterStepRangeChannel.toRaw ∉ []
      simp
    simp [h_nil] at h_providerInteraction
  · exact absurd (registerBoundary_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (memAlignReadByte_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (memAlignByte_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (memAlign_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (memAlignRangeSlice_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (memAlignRomSlice_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (mem_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (specifiedRangesSlice_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact ⟨providerTable, h_providerTable, h, provider, h_providerInteraction, h_message⟩
  · exact absurd (arithDiv_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (arithMul_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (staticBinaryExtension_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (staticBinary_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exact absurd (binaryAdd_table_interactionsWith_registerStepRange_nil h)
      (by intro h_nil; simp [h_nil] at h_providerInteraction)
  · exfalso
    rcases main_registerStepRange_mult_cases h (h_constraints providerTable h_providerTable)
      h_providerInteraction with h_mult | h_mult
    · exact h_nonpull h_mult
    · exact h_nonzero h_mult

/-- **The register-step descent, from balance alone.** A Main pull on bus 102 carrying `value`
forces `rangeTable24.Spec value`. This is the fact that closes #342's cycle hole: the pulled
distance `<slot>_mem_step - <slot>_reg_prev_mem_step - 1` is a genuine 24-bit number, so
`<slot>_reg_prev_mem_step` is strictly below the row's own timestamp. -/
theorem rangeTable24_spec_of_registerStepRange_pull
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    (h_constraints : witness.Constraints)
    {pullTable : Table FGL}
    (h_pullTable : pullTable ∈ witness.allTables)
    {pull : Interaction FGL}
    (h_pull : pull ∈ pullTable.interactionsWith RegisterStepRangeChannel.toRaw)
    (h_active : pull.mult = -1)
    {value : FGL}
    (h_message : pull.msg = (toElements (registerStepMessage value)).toArray) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec value := by
  obtain ⟨providerTable, h_providerTable, h_providerComponent,
    providerInteraction, h_providerInteraction, h_providerMessage⟩ :=
    exists_registerStepRange_provider_of_pull h_balanced h_constraints
      h_pullTable h_pull h_active
  exact rangeTable24_spec_of_registerStepRange_provider_interaction h_specs h_providerTable
    h_providerComponent h_providerInteraction (h_providerMessage.trans h_message)

end ZiskFv.AirsClean.FullEnsemble
