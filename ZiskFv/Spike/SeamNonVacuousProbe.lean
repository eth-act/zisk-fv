import ZiskFv.Spike.SeamVmTagChain
import ZiskFv.Channels.SegmentContinuation
import Clean.Air.FlatEnsemble
import Clean.Air.OrderedChannel
import Clean.Utils.Tactics

/-!
# SPIKE — NON-VACUOUS end-to-end seam instance (#76 PATH 1 confirmation)

THROWAWAY go/no-go. NOT for merge. Additive; nothing in the live ensemble
imports it.

Closes the residual flagged in the adversarial verify of the prior (deleted)
`SeamPathProbe.lean`: that probe was VACUOUS (single seam row, no boot push, no
second segment, so the seam `BalancedInteractions` antecedent was UNSATISFIABLE
and the headline theorem was vacuously true).

Here we:
1. Build a NON-VACUOUS seam ensemble: a boot/endpoint component (boot push tag 0
   + final pull tag tf) + TWO segment components (each pull/push, faithful +1
   emission), wired so the seam channel ∈ `ens.channels`.
2. Extract the seam `BalancedInteractions` from the ensemble `Statement` (via the
   seam channel ∈ `ens.channels` membership in `BalancedChannels`), reduce the
   `interactionsWith` list (up to permutation) to the `theList2` shape, and
   discharge through `SeamVmTagChain.tag_chain_derived` to obtain the seam
   value-equality `seg1.prev = seg0.last` end-to-end.
3. Exhibit a concrete balanced multi-segment witness (`SeamVmTagChain.goodList2`)
   to certify the antecedent is SATISFIABLE — the theorem is NOT vacuously true.

The seam channel, message type, multiplicity conventions, and +1 tag emission
are the REAL production ones (`ZiskFv/Channels/SegmentContinuation.lean`,
`ZiskFv/AirsClean/Mem/SeamCircuit.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ZiskFv.Spike.SeamNonVacuousProbe

open Goldilocks
open Air.Flat
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)
open ZiskFv.Spike.SeamVmTagChain

/-! ## Component input rows. -/

/-- Boot/endpoint row: boot boundary (pushed at tag 0) + final boundary (pulled
    at the free tag `tf`). -/
structure BootRow (F : Type) where
  boot_value_0 : F
  boot_value_1 : F
  boot_addr : F
  boot_step : F
  final_value_0 : F
  final_value_1 : F
  final_addr : F
  final_step : F
  tf : F
deriving ProvableStruct

/-- Segment row: incoming boundary (pulled at free tag `t`) + outgoing boundary
    (pushed at tag `t + 1`, the faithful +1 emission). -/
structure SegRow (F : Type) where
  prev_value_0 : F
  prev_value_1 : F
  prev_addr : F
  prev_step : F
  last_value_0 : F
  last_value_1 : F
  last_addr : F
  last_step : F
  t : F
deriving ProvableStruct

/-! ## The seam-emitting components.

Each uses the REAL production `SeamContChannel` carrying the REAL `SeamMessage`.
The per-row Spec is trivial: the seam is a GLOBAL balance fact, not a per-row
guarantee — exactly as `SeamContChannel.Guarantees := True` documents. -/

@[reducible]
def bootPushMsg (r : Var BootRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.boot_value_0, value_1 := r.boot_value_1,
    addr := r.boot_addr, step := r.boot_step, segment_id := 0 }

@[reducible]
def finalPullMsg (r : Var BootRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.final_value_0, value_1 := r.final_value_1,
    addr := r.final_addr, step := r.final_step, segment_id := r.tf }

/-- Boot/endpoint component: PUSH boot boundary (tag 0), PULL final boundary
    (tag tf). Mirrors the verifier endpoint table of `theList2`. -/
def bootCircuit : GeneralFormalCircuit FGL BootRow unit where
  main r := do
    SeamContChannel.push (bootPushMsg r)
    SeamContChannel.pull (finalPullMsg r)
  localLength _ := 0
  output _ _ := ()
  Assumptions _ _ := True
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  ProverSpec _ _ _ := True
  channelsWithGuarantees := [SeamContChannel.toRaw]
  channelsWithRequirements := [SeamContChannel.toRaw]
  exposedChannels r _ :=
    expose SeamContChannel
      [ pushed (bootPushMsg r), pulled (finalPullMsg r) ]
  channelsLawful := by
    simp [circuit_norm, bootPushMsg, finalPullMsg, SeamContChannel]
  soundness := by circuit_proof_start [SeamContChannel]
  completeness := by circuit_proof_start [SeamContChannel]

@[reducible]
def segPullMsg (r : Var SegRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.prev_value_0, value_1 := r.prev_value_1,
    addr := r.prev_addr, step := r.prev_step, segment_id := r.t }

@[reducible]
def segPushMsg (r : Var SegRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.last_value_0, value_1 := r.last_value_1,
    addr := r.last_addr, step := r.last_step, segment_id := r.t + 1 }

/-- Segment component: PULL incoming boundary (tag t), PUSH outgoing boundary
    (tag t+1, faithful +1 emission). -/
def segCircuit : GeneralFormalCircuit FGL SegRow unit where
  main r := do
    SeamContChannel.pull (segPullMsg r)
    SeamContChannel.push (segPushMsg r)
  localLength _ := 0
  output _ _ := ()
  Assumptions _ _ := True
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  ProverSpec _ _ _ := True
  channelsWithGuarantees := [SeamContChannel.toRaw]
  channelsWithRequirements := [SeamContChannel.toRaw]
  exposedChannels r _ :=
    expose SeamContChannel
      [ pulled (segPullMsg r), pushed (segPushMsg r) ]
  channelsLawful := by
    simp [circuit_norm, segPullMsg, segPushMsg, SeamContChannel]
  soundness := by circuit_proof_start [SeamContChannel]
  completeness := by circuit_proof_start [SeamContChannel]

/-! ## The components and the ensemble. -/

@[reducible] def bootComp : Component FGL := ⟨ bootCircuit ⟩
@[reducible] def segComp : Component FGL := ⟨ segCircuit ⟩

/-- The non-vacuous seam ensemble: boot/endpoint table + TWO segment tables, with
    the seam channel in `ens.channels`. (PublicIO is `unit`; the seam content is
    carried by the per-table rows.) -/
def seamEnsemble : Ensemble FGL unit where
  tables := [bootComp, segComp, segComp]
  channels := [SeamContChannel.toRaw]
  verifier := .empty FGL unit

/-- Sanity: the seam channel is in the ensemble's channels. -/
theorem seam_mem_channels : SeamContChannel.toRaw ∈ seamEnsemble.channels := by
  simp [seamEnsemble]

/-! ## Per-component abstract interaction reduction (the canonical-var lists). -/

theorem bootComp_interactionsWith :
    bootComp.operations.interactionsWith SeamContChannel.toRaw
      = [ (SeamContChannel.pushed (bootPushMsg (varFromOffset BootRow 0))).toRaw,
          (SeamContChannel.pulled (finalPullMsg (varFromOffset BootRow 0))).toRaw ] :=
  Component.interactionsWith_of_exposedChannels
    (by simp only [bootComp, bootCircuit, Component.exposedChannels, expose,
      List.map_cons, List.map_nil]; exact List.mem_singleton.mpr rfl)

theorem segComp_interactionsWith :
    segComp.operations.interactionsWith SeamContChannel.toRaw
      = [ (SeamContChannel.pulled (segPullMsg (varFromOffset SegRow 0))).toRaw,
          (SeamContChannel.pushed (segPushMsg (varFromOffset SegRow 0))).toRaw ] :=
  Component.interactionsWith_of_exposedChannels
    (by simp only [segComp, segCircuit, Component.exposedChannels, expose,
      List.map_cons, List.map_nil]; exact List.mem_singleton.mpr rfl)

/-! ## Round-trip: evaluating the canonical var against a `toElements` row. -/

theorem valueFromOffset_fromArray (M : TypeMap) [ProvableType M] (v : M FGL)
    (data : ProverData FGL) :
    valueFromOffset M 0 (Environment.fromArray (toElements v).toArray data) = v := by
  simp only [valueFromOffset]
  conv_rhs => rw [← ProvableType.fromElements_toElements v]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_mapRange, Environment.fromArray, Nat.zero_add]
  rw [Array.getElem?_eq_getElem (by simpa using hi)]
  rfl

/-! ## Value-level seam messages (what each row evaluates to). -/

@[reducible] def bootPushVal (r : BootRow FGL) : SeamMessage FGL :=
  { value_0 := r.boot_value_0, value_1 := r.boot_value_1,
    addr := r.boot_addr, step := r.boot_step, segment_id := 0 }
@[reducible] def finalPullVal (r : BootRow FGL) : SeamMessage FGL :=
  { value_0 := r.final_value_0, value_1 := r.final_value_1,
    addr := r.final_addr, step := r.final_step, segment_id := r.tf }
@[reducible] def segPullVal (r : SegRow FGL) : SeamMessage FGL :=
  { value_0 := r.prev_value_0, value_1 := r.prev_value_1,
    addr := r.prev_addr, step := r.prev_step, segment_id := r.t }
@[reducible] def segPushVal (r : SegRow FGL) : SeamMessage FGL :=
  { value_0 := r.last_value_0, value_1 := r.last_value_1,
    addr := r.last_addr, step := r.last_step, segment_id := r.t + 1 }

/-! ## Evaluating a canonical-var message against a `toElements` row. -/

theorem eval_bootPushMsg (v : BootRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (bootPushMsg (varFromOffset BootRow 0)) = bootPushVal v := by
  simp only [bootPushMsg, bootPushVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk, Vector.toArray_mk]
  rfl

theorem eval_finalPullMsg (v : BootRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (finalPullMsg (varFromOffset BootRow 0)) = finalPullVal v := by
  simp only [finalPullMsg, finalPullVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk, Vector.toArray_mk]
  rfl

theorem eval_segPullMsg (v : SegRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (segPullMsg (varFromOffset SegRow 0)) = segPullVal v := by
  simp only [segPullMsg, segPullVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk, Vector.toArray_mk]
  rfl

theorem eval_segPushMsg (v : SegRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (segPushMsg (varFromOffset SegRow 0)) = segPushVal v := by
  simp only [segPushMsg, segPushVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk, Vector.toArray_mk]
  rfl

/-! ## One-row tables and their evaluated seam interaction lists. -/

/-- A one-row table over a component, with the row carrying `v`. -/
def mkTable (comp : Component FGL) (v : comp.Input FGL) (data : ProverData FGL) : Table FGL where
  component := comp
  width := size comp.Input
  table := [(toElements v).toArray]
  data := data
  uniform_width := by intro row hrow; simp at hrow; subst hrow; simp

/-- The boot table's seam interactions, evaluated: boot push (tag 0) + final pull
    (tag tf). -/
theorem bootTable_interactionsWith (v : BootRow FGL) (data : ProverData FGL) :
    (mkTable bootComp v data).interactionsWith SeamContChannel.toRaw
      = [ SeamContChannel.pushedValue (bootPushVal v),
          SeamContChannel.pulledValue (finalPullVal v) ] := by
  simp only [Table.interactionsWith, mkTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Operations.interactionValuesWith_eq_map, bootComp_interactionsWith,
    List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, Table.environment]
  rw [eval_bootPushMsg, eval_finalPullMsg]

/-- A segment table's seam interactions, evaluated: pull (tag t) + push (tag t+1). -/
theorem segTable_interactionsWith (v : SegRow FGL) (data : ProverData FGL) :
    (mkTable segComp v data).interactionsWith SeamContChannel.toRaw
      = [ SeamContChannel.pulledValue (segPullVal v),
          SeamContChannel.pushedValue (segPushVal v) ] := by
  simp only [Table.interactionsWith, mkTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Operations.interactionValuesWith_eq_map, segComp_interactionsWith,
    List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, Table.environment]
  rw [eval_segPullMsg, eval_segPushMsg]

/-! ## The concrete witness over `seamEnsemble`. -/

/-- A concrete `EnsembleWitness` over `seamEnsemble`: one boot row + two segment
    rows. -/
def mkWitness (vb : BootRow FGL) (v0 v1 : SegRow FGL) (data : ProverData FGL) :
    EnsembleWitness seamEnsemble where
  tables := [mkTable bootComp vb data, mkTable segComp v0 data, mkTable segComp v1 data]
  data := data
  publicInput := ()
  same_length := by rfl
  same_circuits := by
    intro i hi
    simp only [seamEnsemble, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i <;> rfl
  same_data := by
    intro table htable
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htable
    rcases htable with rfl | rfl | rfl <;> rfl

/-- The witness's seam interactions reduce to the 6-element faithful list:
    boot push (tag 0), final pull (tag tf), seg0 pull/push, seg1 pull/push. -/
theorem mkWitness_interactionsWith (vb : BootRow FGL) (v0 v1 : SegRow FGL) (data : ProverData FGL) :
    (mkWitness vb v0 v1 data).interactionsWith SeamContChannel.toRaw
      = [ SeamContChannel.pushedValue (bootPushVal vb),
          SeamContChannel.pulledValue (finalPullVal vb),
          SeamContChannel.pulledValue (segPullVal v0),
          SeamContChannel.pushedValue (segPushVal v0),
          SeamContChannel.pulledValue (segPullVal v1),
          SeamContChannel.pushedValue (segPushVal v1) ] := by
  rw [EnsembleWitness.interactionsWith_of_verifier_empty (by rfl)]
  simp only [mkWitness, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    bootTable_interactionsWith, segTable_interactionsWith, List.cons_append, List.nil_append]

/-! ## Bridge: `BalancedInteractions` ignores the channel field.

`balanceOf` (hence `BalancedInteractions`) inspects only `.msg` and `.mult`. So a
list of production seam interactions and the derivation's `theList2` (which uses
its own `SeamChannel5`) have identical balance iff their `(mult, msg)` projections
agree element-wise. We use this to feed the production seam balance into
`SeamVmTagChain.tag_chain_derived`. -/

/-- `balanceOf` depends only on the `(mult, msg)` projection of each interaction. -/
theorem balanceOf_proj (l : List (Interaction FGL)) (m : Array FGL) :
    balanceOf l m
      = (((l.map (fun i => (i.mult, i.msg))).filter (fun p => p.2 = m)).map (fun p => p.1)).sum := by
  simp only [balanceOf, List.filter_map, List.map_map]; rfl

theorem balanceOf_congr_of_proj {as bs : List (Interaction FGL)}
    (h : as.map (fun i => (i.mult, i.msg)) = bs.map (fun i => (i.mult, i.msg))) (m : Array FGL) :
    balanceOf as m = balanceOf bs m := by
  rw [balanceOf_proj, balanceOf_proj, h]

/-- Transfer `BalancedInteractions` across the `(mult, msg)`-projection. -/
theorem balancedInteractions_of_proj {as bs : List (Interaction FGL)}
    (h : as.map (fun i => (i.mult, i.msg)) = bs.map (fun i => (i.mult, i.msg)))
    (hbal : BalancedInteractions as) : BalancedInteractions bs := by
  refine ⟨?_, ?_⟩
  · have hlen : as.length = bs.length := by
      have := congrArg List.length h; simpa using this
    rw [← hlen]; exact hbal.1
  · intro m
    rw [← balanceOf_congr_of_proj h m]
    exact hbal.2 m

/-! ## The production seam message array equals the derivation's `seam5`. -/

theorem toElements_seamMessage (a b c d e : FGL) :
    (toElements ({ value_0 := a, value_1 := b, addr := c, step := d, segment_id := e } : SeamMessage FGL)).toArray
      = seam5 a b c d e := by
  simp [seam5, explicit_provable_type, ProvableStruct.componentsToElements, components,
    ProvableStruct.toComponents, Vector.toArray_cast, Vector.toArray_append]

/-! ## The 6-element production list projects onto `theList2`.

`theList2` is the derivation's interaction list (over its own `SeamChannel5`),
but balance ignores the channel field. We show the `(mult, msg)` projections of
the production seam list and the matching `theList2` instance agree, so balance
transfers (`balancedInteractions_of_proj`). -/

/-- Map a `BootRow`/`SegRow` pair onto `theList2`'s 26 free arguments. -/
@[reducible] def asTheList2 (vb : BootRow FGL) (v0 v1 : SegRow FGL) : List (Interaction FGL) :=
  theList2
    vb.boot_value_0 vb.boot_value_1 vb.boot_addr vb.boot_step
    vb.final_value_0 vb.final_value_1 vb.final_addr vb.final_step vb.tf
    v0.prev_value_0 v0.prev_value_1 v0.prev_addr v0.prev_step v0.t
    v0.last_value_0 v0.last_value_1 v0.last_addr v0.last_step
    v1.prev_value_0 v1.prev_value_1 v1.prev_addr v1.prev_step v1.t
    v1.last_value_0 v1.last_value_1 v1.last_addr v1.last_step

theorem proj_eq (vb : BootRow FGL) (v0 v1 : SegRow FGL) :
    ([ SeamContChannel.pushedValue (bootPushVal vb),
       SeamContChannel.pulledValue (finalPullVal vb),
       SeamContChannel.pulledValue (segPullVal v0),
       SeamContChannel.pushedValue (segPushVal v0),
       SeamContChannel.pulledValue (segPullVal v1),
       SeamContChannel.pushedValue (segPushVal v1) ] : List (Interaction FGL)).map
        (fun i => (i.mult, i.msg))
      = (asTheList2 vb v0 v1).map (fun i => (i.mult, i.msg)) := by
  simp only [asTheList2, theList2, List.map_cons, List.map_nil,
    Channel.pushedValue, Channel.pulledValue, pushMsg5, pullMsg5,
    bootPushVal, finalPullVal, segPullVal, segPushVal,
    toElements_seamMessage]

/-! ## EXTRACTION: from the ensemble `Statement`/`BalancedChannels` to `theList2` balance. -/

/-- The seam-channel balance of the concrete witness, transported to the
    derivation's `theList2` shape (balance ignores the channel field). -/
theorem theList2_balanced_of_witness_balance (vb : BootRow FGL) (v0 v1 : SegRow FGL)
    (data : ProverData FGL)
    (hbal : EnsembleWitness.BalancedChannel (mkWitness vb v0 v1 data) SeamContChannel.toRaw) :
    BalancedInteractions (asTheList2 vb v0 v1) := by
  -- `BalancedChannel witness channel = BalancedInteractions (witness.allTablesWitness.interactionsWith channel)`
  rw [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith_allTablesWitness,
    mkWitness_interactionsWith] at hbal
  exact balancedInteractions_of_proj (proj_eq vb v0 v1) hbal

/-- From the full `BalancedChannels` (a conjunct of the ensemble `Statement`,
    holding for the seam channel because it is in `ens.channels`), extract the
    `theList2` balance. -/
theorem theList2_balanced_of_balancedChannels (vb : BootRow FGL) (v0 v1 : SegRow FGL)
    (data : ProverData FGL)
    (hbal : EnsembleWitness.BalancedChannels (mkWitness vb v0 v1 data)) :
    BalancedInteractions (asTheList2 vb v0 v1) :=
  theList2_balanced_of_witness_balance vb v0 v1 data
    (hbal SeamContChannel.toRaw (by simp [seamEnsemble]))

/-! ## THE SEAM VALUE-EQUALITY, derived end-to-end from ensemble balance.

From the ensemble `Statement`'s `BalancedChannels` (holding on the seam channel
because it is in `ens.channels`), `SeamVmTagChain.tag_chain_derived` forces the
per-tag value seam. We expose the SEAM conjunct: one segment's incoming boundary
equals the other segment's outgoing boundary (the disjunction is the honest
permutation ambiguity — both disjuncts carry a genuine seam). -/
theorem seam_value_equality (vb : BootRow FGL) (v0 v1 : SegRow FGL) (data : ProverData FGL)
    (hbal : EnsembleWitness.BalancedChannels (mkWitness vb v0 v1 data)) :
    -- chain position 0 = seg0: seg1.prev = seg0.last (THE SEAM)
    ( v0.t = 0 ∧ v1.t = 1 ∧ vb.tf = 2
      ∧ seam5 v1.prev_value_0 v1.prev_value_1 v1.prev_addr v1.prev_step v1.t
        = seam5 v0.last_value_0 v0.last_value_1 v0.last_addr v0.last_step (v0.t + 1) )
    -- chain position 0 = seg1 (permutation): seg0.prev = seg1.last (THE SEAM)
    ∨ ( v1.t = 0 ∧ v0.t = 1 ∧ vb.tf = 2
      ∧ seam5 v0.prev_value_0 v0.prev_value_1 v0.prev_addr v0.prev_step v0.t
        = seam5 v1.last_value_0 v1.last_value_1 v1.last_addr v1.last_step (v1.t + 1) ) := by
  have hbalanced := theList2_balanced_of_balancedChannels vb v0 v1 data hbal
  rw [asTheList2] at hbalanced
  rcases tag_chain_derived
      vb.boot_value_0 vb.boot_value_1 vb.boot_addr vb.boot_step
      vb.final_value_0 vb.final_value_1 vb.final_addr vb.final_step vb.tf
      v0.prev_value_0 v0.prev_value_1 v0.prev_addr v0.prev_step v0.t
      v0.last_value_0 v0.last_value_1 v0.last_addr v0.last_step
      v1.prev_value_0 v1.prev_value_1 v1.prev_addr v1.prev_step v1.t
      v1.last_value_0 v1.last_value_1 v1.last_addr v1.last_step hbalanced with
    ⟨ht0, ht1, htf, _, hseam, _⟩ | ⟨ht1, ht0, htf, _, hseam, _⟩
  · exact Or.inl ⟨ht0, ht1, htf, hseam⟩
  · exact Or.inr ⟨ht1, ht0, htf, hseam⟩

/-! ## NON-VACUITY: a concrete balanced multi-segment witness.

`seam_value_equality` quantifies over genuinely free rows; its antecedent
`BalancedChannels (mkWitness ..)` must be SATISFIABLE for the theorem to say
something. We exhibit the intended 2-segment chain and prove its seam-channel
balance, transported from `SeamVmTagChain.goodList2_balanced`. -/

/-- The boot row of the intended chain: boot `(0,0,B,0)` tag 0; final `(2,0,200,9)`
    tag tf = 2. -/
@[reducible] def goodBoot : BootRow FGL :=
  { boot_value_0 := 0, boot_value_1 := 0, boot_addr := 335544320, boot_step := 0,
    final_value_0 := 2, final_value_1 := 0, final_addr := 200, final_step := 9, tf := 2 }
/-- seg0: prev = boot `(0,0,B,0)` tag 0; last `(1,0,100,5)` pushed tag 1. -/
@[reducible] def goodSeg0 : SegRow FGL :=
  { prev_value_0 := 0, prev_value_1 := 0, prev_addr := 335544320, prev_step := 0,
    last_value_0 := 1, last_value_1 := 0, last_addr := 100, last_step := 5, t := 0 }
/-- seg1: prev = seg0.last `(1,0,100,5)` tag 1 (THE SEAM); last `(2,0,200,9)` tag 2. -/
@[reducible] def goodSeg1 : SegRow FGL :=
  { prev_value_0 := 1, prev_value_1 := 0, prev_addr := 100, prev_step := 5,
    last_value_0 := 2, last_value_1 := 0, last_addr := 200, last_step := 9, t := 1 }

/-- The intended chain's `asTheList2` is exactly `SeamVmTagChain.goodList2`. -/
theorem asTheList2_good : asTheList2 goodBoot goodSeg0 goodSeg1 = goodList2 := by
  rfl

/-- THE SATISFIABILITY WITNESS: the concrete 2-segment chain's seam channel is
    balanced. This proves the antecedent of `seam_value_equality` is INHABITED, so
    the theorem is NOT vacuously true. -/
theorem good_balancedChannels (data : ProverData FGL) :
    EnsembleWitness.BalancedChannels (mkWitness goodBoot goodSeg0 goodSeg1 data) := by
  intro channel hchannel
  simp only [seamEnsemble, List.mem_singleton] at hchannel
  subst hchannel
  rw [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith_allTablesWitness,
    mkWitness_interactionsWith]
  exact balancedInteractions_of_proj (by
    have := proj_eq goodBoot goodSeg0 goodSeg1
    rwa [asTheList2_good] at this)
    goodList2_balanced

/-- NON-VACUOUS instantiation: running `seam_value_equality` on the concrete
    balanced witness lands in the first disjunct, the tags resolve to `(0,1)`,
    `tf = 2`, and the SEAM holds: seg1.prev `(1,0,100,5)` = seg0.last `(1,0,100,5)`.
    This certifies non-vacuity end-to-end. -/
theorem good_seam_holds (data : ProverData FGL) :
    seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1) := by
  rcases seam_value_equality goodBoot goodSeg0 goodSeg1 data (good_balancedChannels data) with
    ⟨_, _, _, hseam⟩ | ⟨ht1, _, _, _⟩
  · exact hseam
  · -- the permutation disjunct forces goodSeg1.t = 0, but it is 1; absurd
    simp only [goodSeg1] at ht1
    exact (one_ne_zero ht1).elim

end ZiskFv.Spike.SeamNonVacuousProbe

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom, NO
`native_decide`. -/
#print axioms ZiskFv.Spike.SeamNonVacuousProbe.mkWitness_interactionsWith
#print axioms ZiskFv.Spike.SeamNonVacuousProbe.theList2_balanced_of_balancedChannels
#print axioms ZiskFv.Spike.SeamNonVacuousProbe.seam_value_equality
#print axioms ZiskFv.Spike.SeamNonVacuousProbe.good_balancedChannels
#print axioms ZiskFv.Spike.SeamNonVacuousProbe.good_seam_holds
