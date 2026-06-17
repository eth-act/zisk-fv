import ZiskFv.AirsClean.Mem.Constraints
import ZiskFv.AirsClean.Mem.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import ZiskFv.Channels.SegmentContinuation
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Mem Clean Component (Phase C8)

Packages ZisK's Mem AIR per-row F-constraints as a Clean
`Air.Flat.Component`.

This is the per-row component layer only. The memory-bus provider path is a
family-terminal C10 concern because it must compose Mem, MemAlign*, and Main
against the same memory-bus channel without reintroducing a hidden
lookup/permutation promise.

## Trust note

No axioms. Completeness is a constructibility claim for rows equal to
`memRowOf ...`: primary/dual selectors, write flag, and address-change flag
are Boolean, the selector implications are explicit semantic side-conditions,
and `read_same_addr` plus read-on-address-change value zeroing are computed by
the builder. Cross-row memory consistency remains outside this row-local proof.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)
open Air.Flat

/-- Honest `read_same_addr` column for Mem. -/
def memReadSameAddrOf (addrChanges wr : Bool) : FGL :=
  (1 - boolF addrChanges) * (1 - boolF wr)

/-- Honest Mem value chunk: address-changing reads are zeroed, all other rows
    keep the caller-supplied chunk. -/
def memValueOf (addrChanges wr : Bool) (value : FGL) : FGL :=
  if addrChanges && !wr then 0 else value

/-- Honest row for Mem's row-local constraints. Selector columns are Boolean,
    `read_same_addr` is computed, and address-changing reads zero the value
    chunks constrained by this slice. -/
def memRowOf (sel selDual wr addrChanges : Bool)
    (addr step stepDual previousStep increment_0 increment_1 value_0 value_1 : FGL) :
    MemRow FGL :=
  { addr := addr
    step := step
    sel := boolF sel
    addr_changes := boolF addrChanges
    step_dual := stepDual
    sel_dual := boolF selDual
    value_0 := memValueOf addrChanges wr value_0
    value_1 := memValueOf addrChanges wr value_1
    wr := boolF wr
    previous_step := previousStep
    increment_0 := increment_0
    increment_1 := increment_1
    read_same_addr := memReadSameAddrOf addrChanges wr
    -- The 10 segment-boundary columns (XCAP #103, route (b)) are not part of the
    -- per-row Mem `Spec`; this honest row-local builder sets them to 0.
    segment_id := 0
    previous_segment_value_0 := 0
    previous_segment_value_1 := 0
    previous_segment_addr := 0
    previous_segment_step := 0
    segment_last_value_0 := 0
    segment_last_value_1 := 0
    segment_last_addr := 0
    segment_last_step := 0
    is_last_segment := 0 }

lemma memRowOf_constraintsHold (sel selDual wr addrChanges : Bool)
    (addr step stepDual previousStep increment_0 increment_1 value_0 value_1 : FGL)
    (h_selDual : selDual = true → sel = true)
    (h_wr : wr = true → sel = true) :
    Spec (memRowOf sel selDual wr addrChanges
      addr step stepDual previousStep increment_0 increment_1 value_0 value_1) := by
  cases sel <;> cases selDual <;> cases wr <;> cases addrChanges <;>
    simp [Spec, memRowOf, memReadSameAddrOf, memValueOf, boolF] at h_selDual h_wr ⊢

/-- Mem as a Clean `GeneralFormalCircuit`. -/
def circuit : GeneralFormalCircuit FGL MemRow unit :=
  { memElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built by `memRowOf`; the two selector
    -- implications are semantic side-conditions, not hidden constraints.
    ProverAssumptions := fun row _ _ =>
      ∃ sel selDual wr addrChanges addr step stepDual previousStep
        increment_0 increment_1 value_0 value_1,
        (selDual = true → sel = true) ∧ (wr = true → sel = true) ∧
          row = memRowOf sel selDual wr addrChanges
            addr step stepDual previousStep increment_0 increment_1 value_0 value_1
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
      exact ⟨ by simpa only [sub_eq_add_neg] using h0
            , by simpa only [sub_eq_add_neg] using h1
            , by simpa only [sub_eq_add_neg] using h2
            , by simpa only [sub_eq_add_neg] using h3
            , by simpa only [sub_eq_add_neg] using h4
            , by simpa only [sub_eq_add_neg] using h5
            , by simpa only [sub_eq_add_neg] using h6
            , by simpa only [sub_eq_add_neg] using h7
            , by simpa only [sub_eq_add_neg] using h8 ⟩
    completeness := by
      circuit_proof_start
      obtain ⟨sel, selDual, wr, addrChanges, addr, step, stepDual, previousStep,
        increment_0, increment_1, value_0, value_1, h_selDual, h_wr, hrow⟩ :=
        h_assumptions
      injection hrow with h_addr h_step h_sel h_addr_changes h_step_dual h_sel_dual
        h_value_0 h_value_1 h_wr_col h_previous_step h_increment_0 h_increment_1
        h_read_same_addr
      subst_vars
      simpa only [Spec, memRowOf, memReadSameAddrOf, memValueOf, sub_eq_add_neg] using
        memRowOf_constraintsHold sel selDual wr addrChanges
          addr step stepDual previousStep increment_0 increment_1 value_0 value_1
          h_selDual h_wr }

/-- Mem as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-! ## Mem-with-MemBus Component

`circuitWithMemBus` wraps `memWithMemBusElaborated` (Mem's per-row
constraints + the memory-bus provider emission) as a Clean
`GeneralFormalCircuit`. The Spec is unchanged from `Mem.circuit` —
the channel emission adds no per-row soundness obligation; the soundness
proof mirrors the base component. -/

def circuitWithMemBus : GeneralFormalCircuit FGL MemRow unit :=
  { memWithMemBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers the same honest rows as `circuit`; the memory-bus
    -- emission adds only a trivially-true channel guarantee.
    ProverAssumptions := fun row _ _ =>
      ∃ sel selDual wr addrChanges addr step stepDual previousStep
        increment_0 increment_1 value_0 value_1,
        (selDual = true → sel = true) ∧ (wr = true → sel = true) ∧
          row = memRowOf sel selDual wr addrChanges
            addr step stepDual previousStep increment_0 increment_1 value_0 value_1
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
        exact ⟨ by simpa only [sub_eq_add_neg] using h0
              , by simpa only [sub_eq_add_neg] using h1
              , by simpa only [sub_eq_add_neg] using h2
              , by simpa only [sub_eq_add_neg] using h3
              , by simpa only [sub_eq_add_neg] using h4
              , by simpa only [sub_eq_add_neg] using h5
              , by simpa only [sub_eq_add_neg] using h6
              , by simpa only [sub_eq_add_neg] using h7
              , by simpa only [sub_eq_add_neg] using h8 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [MemBusChannel]
      obtain ⟨sel, selDual, wr, addrChanges, addr, step, stepDual, previousStep,
        increment_0, increment_1, value_0, value_1, h_selDual, h_wr, hrow⟩ :=
        h_assumptions
      injection hrow with h_addr h_step h_sel h_addr_changes h_step_dual h_sel_dual
        h_value_0 h_value_1 h_wr_col h_previous_step h_increment_0 h_increment_1
        h_read_same_addr
      subst_vars
      simpa only [Spec, memRowOf, memReadSameAddrOf, memValueOf, sub_eq_add_neg] using
        memRowOf_constraintsHold sel selDual wr addrChanges
          addr step stepDual previousStep increment_0 increment_1 value_0 value_1
          h_selDual h_wr }

/-- Mem as a Clean `Air.Flat.Component` exposing the memory-bus
    provider emission. Used by Clean memory-bus component assembly. -/
def componentWithMemBus : Air.Flat.Component FGL := ⟨ circuitWithMemBus ⟩

/-- Dual-aware Mem wrapper. This models both `mem.pil` provider emissions:
    the primary row gated by `sel` and the dual read row gated by `sel_dual`.
    It is kept separate from `componentWithMemBus` while the FullEnsemble
    balance layer still expects the primary-only compatibility component. -/
def circuitWithDualMemBus : GeneralFormalCircuit FGL MemRow unit :=
  { memWithDualMemBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers the same honest rows as `circuit`; the two memory-bus
    -- emissions add only trivially-true channel guarantees.
    ProverAssumptions := fun row _ _ =>
      ∃ sel selDual wr addrChanges addr step stepDual previousStep
        increment_0 increment_1 value_0 value_1,
        (selDual = true → sel = true) ∧ (wr = true → sel = true) ∧
          row = memRowOf sel selDual wr addrChanges
            addr step stepDual previousStep increment_0 increment_1 value_0 value_1
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
        exact ⟨ by simpa only [sub_eq_add_neg] using h0
              , by simpa only [sub_eq_add_neg] using h1
              , by simpa only [sub_eq_add_neg] using h2
              , by simpa only [sub_eq_add_neg] using h3
              , by simpa only [sub_eq_add_neg] using h4
              , by simpa only [sub_eq_add_neg] using h5
              , by simpa only [sub_eq_add_neg] using h6
              , by simpa only [sub_eq_add_neg] using h7
              , by simpa only [sub_eq_add_neg] using h8 ⟩
      · -- The channel emissions (two MemBus, two seam) all have
        -- `Guarantees := True`, so every guarantee conjunct is trivial.
        simp only [MemBusChannel, SeamContChannel, and_imp, implies_true,
          and_true, true_and, forall_const]
    completeness := by
      circuit_proof_start [MemBusChannel]
      obtain ⟨sel, selDual, wr, addrChanges, addr, step, stepDual, previousStep,
        increment_0, increment_1, value_0, value_1, h_selDual, h_wr, hrow⟩ :=
        h_assumptions
      injection hrow with h_addr h_step h_sel h_addr_changes h_step_dual h_sel_dual
        h_value_0 h_value_1 h_wr_col h_previous_step h_increment_0 h_increment_1
        h_read_same_addr
      subst_vars
      simpa only [Spec, memRowOf, memReadSameAddrOf, memValueOf, sub_eq_add_neg] using
        memRowOf_constraintsHold sel selDual wr addrChanges
          addr step stepDual previousStep increment_0 increment_1 value_0 value_1
          h_selDual h_wr }

/-- Mem as a Clean `Air.Flat.Component` exposing both primary and dual
    memory-bus provider emissions. -/
def componentWithDualMemBus : Air.Flat.Component FGL := ⟨ circuitWithDualMemBus ⟩

theorem componentWithMemBus_interactionsWith_memBus :
    componentWithMemBus.operations.interactionsWith MemBusChannel.toRaw =
      [((MemBusChannel.emitted componentWithMemBus.rowInputVar.sel
          (memBusMessageExpr componentWithMemBus.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [((MemBusChannel.emitted componentWithMemBus.rowInputVar.sel
          (memBusMessageExpr componentWithMemBus.rowInputVar)).toRaw)]⟩ ∈
    componentWithMemBus.exposedChannels
  simp only [componentWithMemBus, circuitWithMemBus, memWithMemBusElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

theorem componentWithDualMemBus_interactionsWith_memBus :
    componentWithDualMemBus.operations.interactionsWith MemBusChannel.toRaw =
      [ ((MemBusChannel.emitted componentWithDualMemBus.rowInputVar.sel
            (memBusMessageExpr componentWithDualMemBus.rowInputVar)).toRaw)
        , ((MemBusChannel.emitted componentWithDualMemBus.rowInputVar.sel_dual
            (memBusDualMessageExpr componentWithDualMemBus.rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [ ((MemBusChannel.emitted componentWithDualMemBus.rowInputVar.sel
            (memBusMessageExpr componentWithDualMemBus.rowInputVar)).toRaw)
        , ((MemBusChannel.emitted componentWithDualMemBus.rowInputVar.sel_dual
            (memBusDualMessageExpr componentWithDualMemBus.rowInputVar)).toRaw) ]⟩ ∈
    componentWithDualMemBus.exposedChannels
  simp only [componentWithDualMemBus, circuitWithDualMemBus, memWithDualMemBusElaborated,
    Component.exposedChannels, expose, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Project `componentWithDualMemBus`'s `interactionsWith SeamContChannel.toRaw`
    to the raw emitted pull/gated-push pair (the route-(b) analogue of
    `componentWithDualMemBus_interactionsWith_memBus`). The seam-balance
    extraction over `fullRv64imEnsemble` reduces each Mem-table row's seam
    contribution through this lemma. -/
theorem componentWithDualMemBus_interactionsWith_seam :
    componentWithDualMemBus.operations.interactionsWith SeamContChannel.toRaw =
      [ ((SeamContChannel.emitted (-1)
            (prevSeamMessageExpr componentWithDualMemBus.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (1 - componentWithDualMemBus.rowInputVar.is_last_segment)
            (lastSeamMessageExpr componentWithDualMemBus.rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨SeamContChannel.toRaw,
      [ ((SeamContChannel.emitted (-1)
            (prevSeamMessageExpr componentWithDualMemBus.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (1 - componentWithDualMemBus.rowInputVar.is_last_segment)
            (lastSeamMessageExpr componentWithDualMemBus.rowInputVar)).toRaw) ]⟩ ∈
    componentWithDualMemBus.exposedChannels
  simp only [componentWithDualMemBus, circuitWithDualMemBus, memWithDualMemBusElaborated,
    Component.exposedChannels, expose, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-! ## T... — cross-segment seam BOOT endpoint (XCAP #103, route (b), L4.6)

The Mem rows emit the seam as `pull(tag = segment_id)` and gated
`push(tag = segment_id + 1)` (the gate `1 - is_last_segment` turns the LAST
segment's push OFF). For an `N`-segment chain (`segment_id = 0 .. N-1`, the last
row `is_last_segment = 1`) this telescopes:

* tag `0`: pulled by seg0, but pushed by NOTHING — it dangles;
* tag `k` (`1 ≤ k ≤ N-1`): pushed by seg(k-1), pulled by seg k — balanced;
* tag `N`: never emitted (the last segment's push is gated off).

So the ONLY missing endpoint is a single tag-0 BOOT push. With the
`is_last_segment` gate already closing the high end, NO separate final pull is
needed (this is the structural difference from the deleted scaffold `bootComp`,
whose two segments were both non-last and therefore needed a final pull).

This is the analogue of ZisK's `mem.pil:253`
`direct_global_update_proves(MEMORY_CONTINUATION_ID, [base_address, 0,
internal_base_address, 0, ...], sel: enable_flag)` — a GLOBAL/verifier endpoint,
NOT a per-segment Mem row. We host it as a tiny dedicated `bootComp` table added
to `fullRv64imEnsemble`. It emits the boot push via `emit` (requirements bucket),
so — exactly like `componentWithDualMemBus` — the seam stays OUT of
`channelsWithGuarantees`. -/

/-- The boot endpoint's seam message: the base-address boundary tuple pushed at
    tag 0 (`mem.pil:253`: `[base_address, 0, internal_base_address, 0]`). The
    `BootRow` carries the boundary fields as free columns. -/
structure BootRow (F : Type) where
  boot_value_0 : F
  boot_value_1 : F
  boot_addr : F
  boot_step : F
deriving ProvableStruct

/-- The boot push message: the boundary tuple tagged with `segment_id = 0`. -/
@[reducible]
def bootSeamMessageExpr (r : Var BootRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.boot_value_0
    value_1 := r.boot_value_1
    addr := r.boot_addr
    step := r.boot_step
    segment_id := 0 }

/-- The boot endpoint's per-row circuit: emit the single tag-0 boot push
    (mult `+1`), in the requirements bucket (`emit`, not `pull`). No row-local
    constraints. -/
@[circuit_norm]
def bootMain (r : Var BootRow FGL) : Circuit FGL Unit := do
  SeamContChannel.emit 1 (bootSeamMessageExpr r)

/-- The boot endpoint as a Clean `GeneralFormalCircuit`. `Spec := True` (it is a
    verifier endpoint with no per-row obligation); the seam channel is in
    `channelsWithRequirements`, never `channelsWithGuarantees`. -/
def bootCircuit : GeneralFormalCircuit FGL BootRow unit where
  main := bootMain
  localLength _ := 0
  output _ _ := ()
  Assumptions _ _ := True
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  ProverSpec _ _ _ := True
  channelsWithGuarantees := []
  channelsWithRequirements := [SeamContChannel.toRaw]
  exposedChannels r _ :=
    expose SeamContChannel [ SeamContChannel.emitted 1 (bootSeamMessageExpr r) ]
  channelsLawful := by
    simp [circuit_norm, bootMain, bootSeamMessageExpr, SeamContChannel]
  soundness := by circuit_proof_start [SeamContChannel]
  completeness := by circuit_proof_start [SeamContChannel]

/-- The boot endpoint as a Clean `Air.Flat.Component`. -/
def bootComp : Air.Flat.Component FGL := ⟨ bootCircuit ⟩

/-- Project `bootComp`'s `interactionsWith SeamContChannel.toRaw` to the single
    raw emitted boot push (the route-(b) endpoint analogue of
    `componentWithDualMemBus_interactionsWith_seam`). -/
theorem bootComp_interactionsWith_seam :
    bootComp.operations.interactionsWith SeamContChannel.toRaw =
      [ ((SeamContChannel.emitted 1
            (bootSeamMessageExpr bootComp.rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨SeamContChannel.toRaw,
      [ ((SeamContChannel.emitted 1
            (bootSeamMessageExpr bootComp.rowInputVar)).toRaw) ]⟩ ∈
    bootComp.exposedChannels
  simp only [bootComp, bootCircuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil, Channel.emitted]

/-- `bootComp` emits NO memory-bus interactions. -/
theorem bootComp_interactionsWith_memBus :
    bootComp.operations.interactionsWith MemBusChannel.toRaw = [] := by
  rw [Component.interactionsWith_eq]
  simp only [bootComp, bootCircuit, Component.rowOperations, bootMain,
    bootSeamMessageExpr, circuit_norm, SeamContChannel, MemBusChannel,
    Channel.toRaw, RawChannel.mk.injEq]

/-- Project the generic Clean component `Spec` for `componentWithMemBus` to
    the concrete Mem row `Spec`. -/
theorem spec_of_componentWithMemBus_spec
    (env : Environment FGL)
    (h_spec : componentWithMemBus.Spec env) :
    Spec (componentWithMemBus.rowInput env) := by
  exact h_spec

/-- Project the generic Clean component `Spec` for
    `componentWithDualMemBus` to the concrete Mem row `Spec`. -/
theorem spec_of_componentWithDualMemBus_spec
    (env : Environment FGL)
    (h_spec : componentWithDualMemBus.Spec env) :
    Spec (componentWithDualMemBus.rowInput env) := by
  exact h_spec

/-- The dual-aware component spec gives boolean primary selectors. -/
theorem sel_boolean_of_componentWithDualMemBus_spec
    (env : Environment FGL)
    (h_spec : componentWithDualMemBus.Spec env) :
    (componentWithDualMemBus.rowInput env).sel = 0
      ∨ (componentWithDualMemBus.rowInput env).sel = 1 :=
  sel_boolean_of_spec _
    (spec_of_componentWithDualMemBus_spec env h_spec)

/-- The dual-aware component spec gives boolean dual selectors. -/
theorem sel_dual_boolean_of_componentWithDualMemBus_spec
    (env : Environment FGL)
    (h_spec : componentWithDualMemBus.Spec env) :
    (componentWithDualMemBus.rowInput env).sel_dual = 0
      ∨ (componentWithDualMemBus.rowInput env).sel_dual = 1 :=
  sel_dual_boolean_of_spec _
    (spec_of_componentWithDualMemBus_spec env h_spec)

/-- A selected dual Mem emission implies the primary selector is active. -/
theorem sel_of_sel_dual_one_of_componentWithDualMemBus_spec
    (env : Environment FGL)
    (h_spec : componentWithDualMemBus.Spec env)
    (h_sel_dual :
      (componentWithDualMemBus.rowInput env).sel_dual = 1) :
    (componentWithDualMemBus.rowInput env).sel = 1 :=
  sel_of_sel_dual_one_of_spec _
    (spec_of_componentWithDualMemBus_spec env h_spec)
    h_sel_dual

/-- The Mem `Spec` for a row, derived through the Clean Component. -/
theorem spec_via_component (row : MemRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, memElaborated,
    circuit_norm] at hsound
  refine hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { addr := .const row.addr
      step := .const row.step
      sel := .const row.sel
      addr_changes := .const row.addr_changes
      step_dual := .const row.step_dual
      sel_dual := .const row.sel_dual
      value_0 := .const row.value_0
      value_1 := .const row.value_1
      wr := .const row.wr
      previous_step := .const row.previous_step
      increment_0 := .const row.increment_0
      increment_1 := .const row.increment_1
      read_same_addr := .const row.read_same_addr
      segment_id := .const row.segment_id
      previous_segment_value_0 := .const row.previous_segment_value_0
      previous_segment_value_1 := .const row.previous_segment_value_1
      previous_segment_addr := .const row.previous_segment_addr
      previous_segment_step := .const row.previous_segment_step
      segment_last_value_0 := .const row.segment_last_value_0
      segment_last_value_1 := .const row.segment_last_value_1
      segment_last_addr := .const row.segment_last_addr
      segment_last_step := .const row.segment_last_step
      is_last_segment := .const row.is_last_segment }
    row ?_ ?_
  · rfl
  · simpa only [Spec, sub_eq_add_neg] using h_constraints

end ZiskFv.AirsClean.Mem
