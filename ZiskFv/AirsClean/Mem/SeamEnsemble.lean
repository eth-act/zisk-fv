import ZiskFv.AirsClean.Mem.SeamCircuit
import ZiskFv.Spike.SeamVmTagChain
import Clean.Air.FlatEnsemble
import Clean.Air.OrderedChannel
import Clean.Utils.Tactics

/-!
# Cross-segment seam: wiring + non-vacuous balance extraction on a real-component
  ensemble (XCAP #103 / PLAN_ENDGAME_P4_103 L3)

This module lands the seam channel on an ensemble built from the **production**
`componentWithSeamAndMemBus` (the real Mem component that emits BOTH the dual
MemBus AND the segment-continuation seam per row, via `emit`), through the
`SoundEnsemble.addChannel` idiom (`Clean/Air/OrderedChannel.lean:683`):

* `addChannel` puts the seam channel in `ens.channels` with **NO soundness
  obligation** (its only fields prepend to `channels`; `subset_finished`
  inherits unchanged because the seam is in `channelsWithRequirements`, never
  `channelsWithGuarantees`).
* Its balance therefore becomes an assumed conjunct of
  `EnsembleWitness.BalancedChannels` — the SAME trust class as `trace.balanced`.
* From that balance we extract the seam `BalancedInteractions` and discharge the
  N=2 tag-chain derivation (`SeamVmTagChain.tag_chain_derived`) to obtain the
  cross-segment value seam.

## Scope (L2+L3, this increment)

The seam-emitting Mem tables use the production `componentWithSeamAndMemBus`. The
boot/endpoint (`mem.pil:253` `direct_global_update_proves` tag 0 + the verifier's
global END) is hosted as a dedicated endpoint component — exactly the verifier
endpoint the probe and `SeamVmTagChain.lean §"verifier boot push"` model.

This ensemble is SEPARATE from `fullRv64imEnsemble`: the 28 merged construction
families root on `fullRv64imEnsemble` and do NOT yet consume the seam (that is
L5/#76). Keeping them on the untouched ensemble holds the HARD constraint that
they stay byte-identical. The 10 non-Mem provider tables of the real ensemble
contribute `[]` to the seam channel's balance (they do not emit it), so they add
no seam-soundness content; embedding the seam component into the full 11-table
`fullRv64imEnsemble` for the #76 consumer is L5.

## Non-vacuity (the anti-laundering guard)

A green `BalancedChannels → seam` is worthless if `BalancedChannels` is
unsatisfiable. We exhibit a concrete boot + 2-segment witness and PROVE its seam
channel balanced (`good_seamWithSeam_balancedChannels`), then run the derivation
on it to land the seam holding (`good_seam_holds`). This is the trap that bit the
first probe; it is closed here as a build artifact, not an argument.

## Trust note

No axioms. The seam balance is consumed as the existing channel-balance trust
class; nothing consumes the seam channel's guarantees (`Guarantees := True`).
-/

set_option linter.unusedSimpArgs false

namespace ZiskFv.AirsClean.Mem.SeamEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)
open ZiskFv.Spike.SeamVmTagChain
open ZiskFv.AirsClean.Mem

/-! ## Boot / verifier-endpoint component.

The boot endpoint hosts the two GLOBAL contributions that are NOT per-segment Mem
rows: the boot push at tag 0 (`mem.pil:253` `direct_global_update_proves`) and the
verifier's final pull that terminates the chain. Both use `emit` (requirements
bucket), so this component, like `componentWithSeamAndMemBus`, keeps the seam OUT
of `channelsWithGuarantees`. -/

/-- Boot/endpoint row: boot boundary (pushed at tag 0) + final boundary (pulled
    at the free tag `tf`, the verifier END). -/
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

@[reducible]
def bootPushMsg (r : Var BootRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.boot_value_0, value_1 := r.boot_value_1,
    addr := r.boot_addr, step := r.boot_step, segment_id := 0 }

@[reducible]
def finalPullMsg (r : Var BootRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := r.final_value_0, value_1 := r.final_value_1,
    addr := r.final_addr, step := r.final_step, segment_id := r.tf }

@[circuit_norm]
def bootMain (r : Var BootRow FGL) : Circuit FGL Unit := do
  SeamContChannel.emit 1 (bootPushMsg r)
  SeamContChannel.emit (-1) (finalPullMsg r)

/-- Boot/endpoint circuit: emit the boot push (tag 0) and the final pull (tag tf),
    both in the requirements bucket. The seam channel is deliberately absent from
    `channelsWithGuarantees`. -/
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
    expose SeamContChannel
      [ emitted 1 (bootPushMsg r), emitted (-1) (finalPullMsg r) ]
  channelsLawful := by
    simp [circuit_norm, bootMain, bootPushMsg, finalPullMsg, SeamContChannel]
  soundness := by circuit_proof_start [SeamContChannel]
  completeness := by circuit_proof_start [SeamContChannel]

@[reducible] def bootComp : Component FGL := ⟨ bootCircuit ⟩

theorem bootComp_interactionsWith_seam :
    bootComp.operations.interactionsWith SeamContChannel.toRaw
      = [ ((SeamContChannel.emitted 1 (bootPushMsg bootComp.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (-1) (finalPullMsg bootComp.rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨SeamContChannel.toRaw,
      [ ((SeamContChannel.emitted 1 (bootPushMsg bootComp.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (-1) (finalPullMsg bootComp.rowInputVar)).toRaw) ]⟩ ∈
    bootComp.exposedChannels
  simp only [bootComp, bootCircuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil, Channel.emitted]

/-! ## The seam-emitting Mem component (production).

The segment tables use the production `componentWithSeamAndMemBus`
(`ZiskFv/AirsClean/Mem/SeamCircuit.lean`): the REAL Mem component that emits the
dual MemBus AND the seam per row. `componentWithSeamAndMemBus.rowInputVar` is
`varFromOffset MemSeamRow 0`, and `componentWithSeamAndMemBus_interactionsWith_seam`
projects its `interactionsWith Seam` to the raw emitted pull/gated-push pair. -/

@[reducible] def segComp : Component FGL := componentWithSeamAndMemBus

theorem segComp_interactionsWith_seam :
    segComp.operations.interactionsWith SeamContChannel.toRaw
      = [ ((SeamContChannel.emitted (-1)
            (prevSeamMessageExpr segComp.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (1 - segComp.rowInputVar.is_last_segment)
            (lastSeamMessageExpr segComp.rowInputVar)).toRaw) ] :=
  componentWithSeamAndMemBus_interactionsWith_seam

/-! ## Round-trip: evaluating a canonical var against a `toElements` row. -/

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

/-! ## Value-level seam messages and gated multiplicities. -/

@[reducible] def bootPushVal (r : BootRow FGL) : SeamMessage FGL :=
  { value_0 := r.boot_value_0, value_1 := r.boot_value_1,
    addr := r.boot_addr, step := r.boot_step, segment_id := 0 }
@[reducible] def finalPullVal (r : BootRow FGL) : SeamMessage FGL :=
  { value_0 := r.final_value_0, value_1 := r.final_value_1,
    addr := r.final_addr, step := r.final_step, segment_id := r.tf }
@[reducible] def segPrevVal (r : MemSeamRow FGL) : SeamMessage FGL :=
  { value_0 := r.previous_segment_value_0, value_1 := r.previous_segment_value_1,
    addr := r.previous_segment_addr, step := r.previous_segment_step,
    segment_id := r.segment_id }
@[reducible] def segLastVal (r : MemSeamRow FGL) : SeamMessage FGL :=
  { value_0 := r.segment_last_value_0, value_1 := r.segment_last_value_1,
    addr := r.segment_last_addr, step := r.segment_last_step,
    segment_id := r.segment_id + 1 }

/-- `emittedValue mult msg`: the value-level interaction an `emit mult msg`
    contributes (mirrors `Channel.pushedValue`/`pulledValue` but at a free
    multiplicity, for the gated push). -/
@[reducible] def emittedSeamValue (mult : FGL) (msg : SeamMessage FGL) : Interaction FGL where
  channel := SeamContChannel.toRaw
  mult := mult
  msg := (toElements msg).toArray
  same_size := by simp [SeamContChannel, Channel.toRaw]
  assumeGuarantees := false

/-- Eval of an `emit mult msg` interaction (mirrors `Channel.eval_pushed`). The
    multiplicity expression is evaluated by `env` (so a gated push
    `1 - is_last_segment` evaluates to `1 - v.is_last_segment`). -/
theorem eval_emittedSeam {mult : Expression FGL} {msg : SeamMessage (Expression FGL)}
    {env : Environment FGL} :
    (SeamContChannel.emitted mult msg).toRaw.eval env
      = emittedSeamValue (env mult) (eval env msg) := by
  have hmsg : (Vector.map (Expression.eval env) (toElements msg))
      = toElements (Eval.eval env msg) := by
    conv_rhs => rw [← ProvableType.fromElements_eval_toElements (env := env) msg]
    rw [ProvableType.toElements_fromElements]
  simp only [Channel.emitted, emitted, ChannelInteraction.toRaw,
    AbstractInteraction.eval, emittedSeamValue, Interaction.mk.injEq, hmsg]

/-! ## Evaluating a canonical-var message against a `toElements` row. -/

theorem eval_bootPushMsg (v : BootRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (bootPushMsg (varFromOffset BootRow 0)) = bootPushVal v := by
  simp only [bootPushMsg, bootPushVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

theorem eval_finalPullMsg (v : BootRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (finalPullMsg (varFromOffset BootRow 0)) = finalPullVal v := by
  simp only [finalPullMsg, finalPullVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

theorem eval_segPrevMsg (v : MemSeamRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (prevSeamMessageExpr (varFromOffset MemSeamRow 0)) = segPrevVal v := by
  simp only [prevSeamMessageExpr, segPrevVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

theorem eval_segLastMsg (v : MemSeamRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (lastSeamMessageExpr (varFromOffset MemSeamRow 0)) = segLastVal v := by
  simp only [lastSeamMessageExpr, segLastVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

/-- The `is_last_segment` column evaluates to the row's field. -/
theorem eval_is_last (v : MemSeamRow FGL) (data : ProverData FGL) :
    (Environment.fromArray (toElements v).toArray data)
        (varFromOffset MemSeamRow 0 |>.is_last_segment) = v.is_last_segment := by
  simp only [eval, explicit_provable_type, circuit_norm,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray]
  rfl

/-! ## One-row tables and their evaluated seam interaction lists. -/

/-- A one-row table over a component, with the row carrying `v`. -/
def mkTable (comp : Component FGL) (v : comp.Input FGL) (data : ProverData FGL) :
    Table FGL where
  component := comp
  width := size comp.Input
  table := [(toElements v).toArray]
  data := data
  uniform_width := by intro row hrow; simp at hrow; subst hrow; simp

/-- The boot table's seam interactions, evaluated: boot push (tag 0, mult 1) +
    final pull (tag tf, mult -1). -/
theorem bootTable_interactionsWith (v : BootRow FGL) (data : ProverData FGL) :
    (mkTable bootComp v data).interactionsWith SeamContChannel.toRaw
      = [ emittedSeamValue 1 (bootPushVal v),
          emittedSeamValue (-1) (finalPullVal v) ] := by
  simp only [Table.interactionsWith, mkTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Operations.interactionValuesWith_eq_map,
    bootComp_interactionsWith_seam, List.map_cons, List.map_nil, Table.environment]
  rw [show bootComp.rowInputVar = varFromOffset BootRow 0 from rfl,
    eval_emittedSeam, eval_emittedSeam, eval_bootPushMsg, eval_finalPullMsg]
  simp only [Expression.eval, Variable.index, mul_one]

/-- A segment table's (production `componentWithSeamAndMemBus`) seam
    interactions, evaluated: prev pull (tag segment_id, mult -1) + last push
    (tag segment_id+1, gated mult `1 - is_last_segment`). -/
theorem segTable_interactionsWith (v : MemSeamRow FGL) (data : ProverData FGL) :
    (mkTable segComp v data).interactionsWith SeamContChannel.toRaw
      = [ emittedSeamValue (-1) (segPrevVal v),
          emittedSeamValue (1 - v.is_last_segment) (segLastVal v) ] := by
  simp only [Table.interactionsWith, mkTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Operations.interactionValuesWith_eq_map,
    segComp_interactionsWith_seam, List.map_cons, List.map_nil, Table.environment]
  have h_prevmult : (Environment.fromArray (toElements v).toArray data)
      (-1 : Expression FGL) = (-1 : FGL) := by
    simp only [Expression.eval, Variable.index, mul_one]
  have h_lastmult : (Environment.fromArray (toElements v).toArray data)
      (1 - (varFromOffset MemSeamRow 0).is_last_segment) = 1 - v.is_last_segment := by
    show (1 : FGL) + (-1 : FGL) *
        ((Environment.fromArray (toElements v).toArray data)
          ((varFromOffset MemSeamRow 0).is_last_segment)) = 1 - v.is_last_segment
    rw [eval_is_last]; ring
  rw [show segComp.rowInputVar = varFromOffset MemSeamRow 0 from rfl,
    eval_emittedSeam, eval_emittedSeam, eval_segPrevMsg, eval_segLastMsg,
    h_prevmult, h_lastmult]

/-! ## The seam ensemble (real-component) and a concrete witness.

ONE ensemble: the boot/endpoint table + two segment tables built from the
production `componentWithSeamAndMemBus`, with the seam channel in `ens.channels`
(the `SoundEnsemble.addChannel` position — `verifier := .empty`, no soundness
obligation). This is the N=2 instance of "model the whole multi-segment execution
as one ensemble whose Mem rows hold every segment boundary." -/

/-- The real-component seam ensemble: boot/endpoint + 2 production seam-Mem
    tables, seam channel ∈ `ens.channels`. -/
def seamEnsemble : Ensemble FGL unit where
  tables := [bootComp, segComp, segComp]
  channels := [SeamContChannel.toRaw]
  verifier := .empty FGL unit

theorem seam_mem_channels : SeamContChannel.toRaw ∈ seamEnsemble.channels := by
  simp [seamEnsemble]

/-- A concrete `EnsembleWitness` over `seamEnsemble`: one boot row + two segment
    (`MemSeamRow`) rows. -/
def mkWitness (vb : BootRow FGL) (v0 v1 : MemSeamRow FGL) (data : ProverData FGL) :
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
    boot push (tag 0), final pull (tag tf), seg0 pull/gated-push, seg1
    pull/gated-push. -/
theorem mkWitness_interactionsWith (vb : BootRow FGL) (v0 v1 : MemSeamRow FGL)
    (data : ProverData FGL) :
    (mkWitness vb v0 v1 data).interactionsWith SeamContChannel.toRaw
      = [ emittedSeamValue 1 (bootPushVal vb),
          emittedSeamValue (-1) (finalPullVal vb),
          emittedSeamValue (-1) (segPrevVal v0),
          emittedSeamValue (1 - v0.is_last_segment) (segLastVal v0),
          emittedSeamValue (-1) (segPrevVal v1),
          emittedSeamValue (1 - v1.is_last_segment) (segLastVal v1) ] := by
  rw [EnsembleWitness.interactionsWith_of_verifier_empty (by rfl)]
  simp only [mkWitness, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    bootTable_interactionsWith, segTable_interactionsWith, List.cons_append,
    List.nil_append]

/-! ## Bridge: `BalancedInteractions` ignores the channel field.

`balanceOf` (hence `BalancedInteractions`) inspects only `.msg` and `.mult`. So a
list of production seam interactions and the derivation's `theList2` (which uses
its own `SeamChannel5`) have identical balance iff their `(mult, msg)` projections
agree element-wise. (Verbatim from the confirmed probe — balance is
channel-blind.) -/

theorem balanceOf_proj (l : List (Interaction FGL)) (m : Array FGL) :
    balanceOf l m
      = (((l.map (fun i => (i.mult, i.msg))).filter (fun p => p.2 = m)).map
          (fun p => p.1)).sum := by
  simp only [balanceOf, List.filter_map, List.map_map]; rfl

theorem balanceOf_congr_of_proj {as bs : List (Interaction FGL)}
    (h : as.map (fun i => (i.mult, i.msg)) = bs.map (fun i => (i.mult, i.msg)))
    (m : Array FGL) : balanceOf as m = balanceOf bs m := by
  rw [balanceOf_proj, balanceOf_proj, h]

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

/-- The production `SeamMessage` value's `toElements` array equals the
    derivation's `seam5` 5-tuple (so the message arrays coincide and balance
    transfers). -/
theorem toElements_seamMessage (a b c d e : FGL) :
    (toElements ({ value_0 := a, value_1 := b, addr := c, step := d, segment_id := e } : SeamMessage FGL)).toArray
      = seam5 a b c d e := by
  simp [seam5, explicit_provable_type, ProvableStruct.componentsToElements,
    components, ProvableStruct.toComponents, Vector.toArray_cast,
    Vector.toArray_append]

/-- Map a `BootRow`/`MemSeamRow` triple onto `theList2`'s 26 free arguments. The
    segment tags are the rows' `segment_id`s; the +1 push tags are intrinsic. -/
@[reducible] def asTheList2 (vb : BootRow FGL) (v0 v1 : MemSeamRow FGL) :
    List (Interaction FGL) :=
  theList2
    vb.boot_value_0 vb.boot_value_1 vb.boot_addr vb.boot_step
    vb.final_value_0 vb.final_value_1 vb.final_addr vb.final_step vb.tf
    v0.previous_segment_value_0 v0.previous_segment_value_1 v0.previous_segment_addr
    v0.previous_segment_step v0.segment_id
    v0.segment_last_value_0 v0.segment_last_value_1 v0.segment_last_addr v0.segment_last_step
    v1.previous_segment_value_0 v1.previous_segment_value_1 v1.previous_segment_addr
    v1.previous_segment_step v1.segment_id
    v1.segment_last_value_0 v1.segment_last_value_1 v1.segment_last_addr v1.segment_last_step

/-- The production 6-element seam list projects onto `theList2` PROVIDED both
    segments are non-last (`is_last_segment = 0`, so the gated push multiplicity
    is `1 - 0 = 1`, matching `theList2`'s `pushMsg5`). A last segment's push is
    gated off and is closed instead by the boot/verifier END (it would not appear
    in this 6-element chain). -/
theorem proj_eq (vb : BootRow FGL) (v0 v1 : MemSeamRow FGL)
    (h0 : v0.is_last_segment = 0) (h1 : v1.is_last_segment = 0) :
    ([ emittedSeamValue 1 (bootPushVal vb),
       emittedSeamValue (-1) (finalPullVal vb),
       emittedSeamValue (-1) (segPrevVal v0),
       emittedSeamValue (1 - v0.is_last_segment) (segLastVal v0),
       emittedSeamValue (-1) (segPrevVal v1),
       emittedSeamValue (1 - v1.is_last_segment) (segLastVal v1) ]
        : List (Interaction FGL)).map (fun i => (i.mult, i.msg))
      = (asTheList2 vb v0 v1).map (fun i => (i.mult, i.msg)) := by
  simp only [asTheList2, theList2, List.map_cons, List.map_nil,
    pushMsg5, pullMsg5, emittedSeamValue, h0, h1, sub_zero,
    bootPushVal, finalPullVal, segPrevVal, segLastVal, toElements_seamMessage]

/-! ## EXTRACTION: from the ensemble `BalancedChannels` to `theList2` balance.

`BalancedChannels` is a conjunct of the ensemble `Statement`; it holds for the
seam channel because it is in `ens.channels` (the `addChannel` position). We pull
out the seam-channel balance and transport it to the derivation's `theList2`
shape (balance is channel-blind). -/

/-- From the full `BalancedChannels`, extract the `theList2` balance for the seam
    channel (both segments non-last). -/
theorem theList2_balanced_of_balancedChannels (vb : BootRow FGL) (v0 v1 : MemSeamRow FGL)
    (data : ProverData FGL)
    (h0 : v0.is_last_segment = 0) (h1 : v1.is_last_segment = 0)
    (hbal : EnsembleWitness.BalancedChannels (mkWitness vb v0 v1 data)) :
    BalancedInteractions (asTheList2 vb v0 v1) := by
  have hseam := hbal SeamContChannel.toRaw (by simp [seamEnsemble])
  rw [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith_allTablesWitness,
    mkWitness_interactionsWith] at hseam
  exact balancedInteractions_of_proj (proj_eq vb v0 v1 h0 h1) hseam

/-! ## THE SEAM VALUE-EQUALITY, derived end-to-end from ensemble balance (L4).

From the ensemble's `BalancedChannels` (the assumed channel-balance trust class,
holding on the seam channel because it is in `ens.channels`),
`SeamVmTagChain.tag_chain_derived` forces the per-tag value seam. We expose the
SEAM conjunct: one segment's incoming boundary equals the other's outgoing
boundary. The disjunction is the honest permutation ambiguity (which physical
segment plays which chain position); both disjuncts carry a genuine seam. -/
theorem seam_value_equality (vb : BootRow FGL) (v0 v1 : MemSeamRow FGL)
    (data : ProverData FGL)
    (h0 : v0.is_last_segment = 0) (h1 : v1.is_last_segment = 0)
    (hbal : EnsembleWitness.BalancedChannels (mkWitness vb v0 v1 data)) :
    -- chain position 0 = seg0: seg1.prev = seg0.last (THE SEAM)
    ( v0.segment_id = 0 ∧ v1.segment_id = 1 ∧ vb.tf = 2
      ∧ seam5 v1.previous_segment_value_0 v1.previous_segment_value_1
          v1.previous_segment_addr v1.previous_segment_step v1.segment_id
        = seam5 v0.segment_last_value_0 v0.segment_last_value_1
          v0.segment_last_addr v0.segment_last_step (v0.segment_id + 1) )
    -- chain position 0 = seg1 (permutation): seg0.prev = seg1.last (THE SEAM)
    ∨ ( v1.segment_id = 0 ∧ v0.segment_id = 1 ∧ vb.tf = 2
      ∧ seam5 v0.previous_segment_value_0 v0.previous_segment_value_1
          v0.previous_segment_addr v0.previous_segment_step v0.segment_id
        = seam5 v1.segment_last_value_0 v1.segment_last_value_1
          v1.segment_last_addr v1.segment_last_step (v1.segment_id + 1) ) := by
  have hbalanced := theList2_balanced_of_balancedChannels vb v0 v1 data h0 h1 hbal
  rw [asTheList2] at hbalanced
  rcases tag_chain_derived
      vb.boot_value_0 vb.boot_value_1 vb.boot_addr vb.boot_step
      vb.final_value_0 vb.final_value_1 vb.final_addr vb.final_step vb.tf
      v0.previous_segment_value_0 v0.previous_segment_value_1 v0.previous_segment_addr
      v0.previous_segment_step v0.segment_id
      v0.segment_last_value_0 v0.segment_last_value_1 v0.segment_last_addr v0.segment_last_step
      v1.previous_segment_value_0 v1.previous_segment_value_1 v1.previous_segment_addr
      v1.previous_segment_step v1.segment_id
      v1.segment_last_value_0 v1.segment_last_value_1 v1.segment_last_addr v1.segment_last_step
      hbalanced with
    ⟨ht0, ht1, htf, _, hseam, _⟩ | ⟨ht1, ht0, htf, _, hseam, _⟩
  · exact Or.inl ⟨ht0, ht1, htf, hseam⟩
  · exact Or.inr ⟨ht1, ht0, htf, hseam⟩

/-! ## NON-VACUITY: a concrete balanced multi-segment witness over the real
    component ensemble (the anti-laundering guard).

`seam_value_equality` quantifies over genuinely free rows; its antecedent
`BalancedChannels (mkWitness ..)` must be SATISFIABLE for the theorem to say
something. We exhibit the intended 2-segment chain — using the PRODUCTION
`MemSeamRow` rows — and prove its seam-channel balance, transported from
`SeamVmTagChain.goodList2_balanced`. -/

/-- The boot row of the intended chain: boot `(0,0,B,0)` tag 0; final `(2,0,200,9)`
    tag tf = 2. -/
@[reducible] def goodBoot : BootRow FGL :=
  { boot_value_0 := 0, boot_value_1 := 0, boot_addr := 335544320, boot_step := 0,
    final_value_0 := 2, final_value_1 := 0, final_addr := 200, final_step := 9, tf := 2 }

/-- seg0 (`MemSeamRow`): prev = boot `(0,0,B,0)` tag 0; last `(1,0,100,5)` pushed
    tag 1; non-last (`is_last_segment = 0`). The base MemRow columns are 0 (they
    do not participate in the seam channel; they drive the separate MemBus). -/
@[reducible] def goodSeg0 : MemSeamRow FGL :=
  { addr := 0, step := 0, sel := 0, addr_changes := 0, step_dual := 0, sel_dual := 0,
    value_0 := 0, value_1 := 0, wr := 0, previous_step := 0, increment_0 := 0,
    increment_1 := 0, read_same_addr := 0,
    segment_id := 0,
    previous_segment_value_0 := 0, previous_segment_value_1 := 0,
    previous_segment_addr := 335544320, previous_segment_step := 0,
    segment_last_value_0 := 1, segment_last_value_1 := 0,
    segment_last_addr := 100, segment_last_step := 5,
    is_last_segment := 0 }

/-- seg1 (`MemSeamRow`): prev = seg0.last `(1,0,100,5)` tag 1 (THE SEAM); last
    `(2,0,200,9)` tag 2; non-last. -/
@[reducible] def goodSeg1 : MemSeamRow FGL :=
  { addr := 0, step := 0, sel := 0, addr_changes := 0, step_dual := 0, sel_dual := 0,
    value_0 := 0, value_1 := 0, wr := 0, previous_step := 0, increment_0 := 0,
    increment_1 := 0, read_same_addr := 0,
    segment_id := 1,
    previous_segment_value_0 := 1, previous_segment_value_1 := 0,
    previous_segment_addr := 100, previous_segment_step := 5,
    segment_last_value_0 := 2, segment_last_value_1 := 0,
    segment_last_addr := 200, segment_last_step := 9,
    is_last_segment := 0 }

/-- The intended chain's `asTheList2` is exactly `SeamVmTagChain.goodList2`. -/
theorem asTheList2_good : asTheList2 goodBoot goodSeg0 goodSeg1 = goodList2 := by
  rfl

/-- THE SATISFIABILITY WITNESS: the concrete 2-segment chain's seam channel is
    balanced. This proves the antecedent of `seam_value_equality` is INHABITED on
    the REAL-component ensemble, so the theorem is NOT vacuously true. -/
theorem good_balancedChannels (data : ProverData FGL) :
    EnsembleWitness.BalancedChannels (mkWitness goodBoot goodSeg0 goodSeg1 data) := by
  intro channel hchannel
  simp only [seamEnsemble, List.mem_singleton] at hchannel
  subst hchannel
  rw [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith_allTablesWitness,
    mkWitness_interactionsWith]
  exact balancedInteractions_of_proj (by
    have := proj_eq goodBoot goodSeg0 goodSeg1 (by rfl) (by rfl)
    rwa [asTheList2_good] at this)
    goodList2_balanced

/-- NON-VACUOUS instantiation: running `seam_value_equality` on the concrete
    balanced witness lands in the first disjunct, tags resolve to `(0,1)`,
    `tf = 2`, and the SEAM holds: seg1.prev `(1,0,100,5)` = seg0.last
    `(1,0,100,5)`. Certifies non-vacuity end-to-end on the real component. -/
theorem good_seam_holds (data : ProverData FGL) :
    seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1) := by
  rcases seam_value_equality goodBoot goodSeg0 goodSeg1 data (by rfl) (by rfl)
      (good_balancedChannels data) with
    ⟨_, _, _, hseam⟩ | ⟨ht1, _, _, _⟩
  · exact hseam
  · -- the permutation disjunct forces goodSeg1.segment_id = 0, but it is 1; absurd
    simp only [goodSeg1] at ht1
    exact (one_ne_zero ht1).elim

end ZiskFv.AirsClean.Mem.SeamEnsemble

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom, NO
`native_decide`. -/
#print axioms ZiskFv.AirsClean.Mem.SeamEnsemble.mkWitness_interactionsWith
#print axioms ZiskFv.AirsClean.Mem.SeamEnsemble.theList2_balanced_of_balancedChannels
#print axioms ZiskFv.AirsClean.Mem.SeamEnsemble.seam_value_equality
#print axioms ZiskFv.AirsClean.Mem.SeamEnsemble.good_balancedChannels
#print axioms ZiskFv.AirsClean.Mem.SeamEnsemble.good_seam_holds
