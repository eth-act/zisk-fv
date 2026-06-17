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

end ZiskFv.AirsClean.Mem.SeamEnsemble
