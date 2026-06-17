import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.Channels.SeamTagChain
import Clean.Air.FlatEnsemble
import Clean.Air.OrderedChannel
import Clean.Utils.Tactics

/-!
# Cross-segment seam: NON-VACUITY on the REAL `fullRv64imEnsemble`
  (XCAP #103, route (b), L4.6)

Route (b) folded the cross-segment seam into the real `componentWithDualMemBus`
and added it to `fullRv64imEnsemble` via `SoundEnsemble.addChannel`, so the seam
balance is now a conjunct of every accepted trace's `BalancedChannels`
(`Compliance.AcceptedTrace.seam_balanced`). L4.6 added the missing tag-0 BOOT
push (`Mem.bootComp`, the analogue of ZisK's `mem.pil:253`
`direct_global_update_proves`) as a table of the real ensemble.

This module closes the LATENT VACUITY that route (b) surfaced: without the boot
endpoint the seam balanced ONLY for zero/empty-Mem traces, so `AcceptedTrace`'s
seam conjunct was satisfiable only degenerately. Here we exhibit a CONCRETE
`EnsembleWitness` over the REAL `fullRv64imEnsemble` whose Mem table carries TWO
NONZERO segments plus the boot endpoint, and PROVE:

* its seam channel BALANCES (`good_seam_balancedChannel`), so the seam conjunct
  of `BalancedChannels`/`AcceptedTrace` is SATISFIABLE for a real multi-segment
  Mem trace — NOT vacuous; and
* running the channel-level boot-chain derivation
  (`SeamTagChain.boot_chain_derived`) on that balance lands the cross-segment
  VALUE seam: `seg1.previous_segment_* = seg0.segment_last_*`
  (`good_seam_holds`).

## Construction

The witness's tables follow `fullRv64imEnsemble.ensemble.tables` order exactly.
Every NON-Mem, non-boot table is given an EMPTY row list (`table := []`), so it
contributes `[]` to the seam channel for free (the flatMap over no rows). Only
the boot table (one boot row) and the Mem table (two segment rows) carry rows;
they realise precisely `SeamTagChain.bootList2`'s boot + 2-segment interaction
list, whose balance is `SeamTagChain.goodBootList2_balanced`.

## Trust note

No axioms. The seam balance is consumed as the existing channel-balance trust
class (nothing consumes the seam channel's guarantees, `Guarantees := True`).
The witness is concrete (all rows are explicit literals), so the satisfiability
is a build artifact, not an argument.
-/

set_option linter.unusedSimpArgs false

namespace ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity

open Goldilocks
open Air.Flat
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)
open ZiskFv.Channels.SeamTagChain
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.Mem (MemRow BootRow componentWithDualMemBus bootComp
  prevSeamMessageExpr lastSeamMessageExpr bootSeamMessageExpr)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

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

/-! ## Value-level seam messages and the `emit` interaction value. -/

@[reducible] def bootPushVal (r : BootRow FGL) : SeamMessage FGL :=
  { value_0 := r.boot_value_0, value_1 := r.boot_value_1,
    addr := r.boot_addr, step := r.boot_step, segment_id := 0 }
@[reducible] def segPrevVal (r : MemRow FGL) : SeamMessage FGL :=
  { value_0 := r.previous_segment_value_0, value_1 := r.previous_segment_value_1,
    addr := r.previous_segment_addr, step := r.previous_segment_step,
    segment_id := r.segment_id }
@[reducible] def segLastVal (r : MemRow FGL) : SeamMessage FGL :=
  { value_0 := r.segment_last_value_0, value_1 := r.segment_last_value_1,
    addr := r.segment_last_addr, step := r.segment_last_step,
    segment_id := r.segment_id + 1 }

/-- The value-level interaction an `emit mult msg` contributes (free
    multiplicity, for the `1 - is_last_segment` gated push). -/
@[reducible] def emittedSeamValue (mult : FGL) (msg : SeamMessage FGL) : Interaction FGL where
  channel := SeamContChannel.toRaw
  mult := mult
  msg := (toElements msg).toArray
  same_size := by simp [SeamContChannel, Channel.toRaw]
  assumeGuarantees := false

/-- Eval of an `emit mult msg` interaction (the multiplicity is evaluated by the
    environment, so the gated `1 - is_last_segment` reduces to `1 - row.is_last`). -/
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

/-! ## Evaluating each canonical-var seam message against a `toElements` row. -/

theorem eval_bootPushMsg (v : BootRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (bootSeamMessageExpr (varFromOffset BootRow 0)) = bootPushVal v := by
  simp only [bootSeamMessageExpr, bootPushVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

theorem eval_segPrevMsg (v : MemRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (prevSeamMessageExpr (varFromOffset MemRow 0)) = segPrevVal v := by
  simp only [prevSeamMessageExpr, segPrevVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

theorem eval_segLastMsg (v : MemRow FGL) (data : ProverData FGL) :
    eval (Environment.fromArray (toElements v).toArray data)
        (lastSeamMessageExpr (varFromOffset MemRow 0)) = segLastVal v := by
  simp only [lastSeamMessageExpr, segLastVal, circuit_norm, explicit_provable_type,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray, Vector.cast_mk,
    Vector.toArray_mk]
  rfl

theorem eval_is_last (v : MemRow FGL) (data : ProverData FGL) :
    (Environment.fromArray (toElements v).toArray data)
        (varFromOffset MemRow 0 |>.is_last_segment) = v.is_last_segment := by
  simp only [eval, explicit_provable_type, circuit_norm,
    eval_varFromOffset_valueFromOffset, valueFromOffset_fromArray]
  rfl

/-! ## One-row / multi-row tables and their evaluated seam interaction lists. -/

/-- A table over `comp` carrying the given value rows. -/
def mkTable (comp : Component FGL) (rows : List (comp.Input FGL)) (data : ProverData FGL) :
    Table FGL where
  component := comp
  width := size comp.Input
  table := rows.map (fun v => (toElements v).toArray)
  data := data
  uniform_width := by
    intro row hrow
    simp only [List.mem_map] at hrow
    obtain ⟨v, _, rfl⟩ := hrow
    simp

/-- A table with NO rows contributes nothing to any channel. -/
theorem mkTable_nil_interactionsWith (comp : Component FGL) (data : ProverData FGL)
    (channel : RawChannel FGL) :
    (mkTable comp [] data).interactionsWith channel = [] := by
  simp [Table.interactionsWith, mkTable]

/-- The boot table's seam interactions, evaluated: a single boot push (tag 0,
    mult 1). -/
theorem bootTable_interactionsWith (v : BootRow FGL) (data : ProverData FGL) :
    (mkTable bootComp [v] data).interactionsWith SeamContChannel.toRaw
      = [ emittedSeamValue 1 (bootPushVal v) ] := by
  simp only [Table.interactionsWith, mkTable, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.bootComp_interactionsWith_seam, Table.environment]
  rw [show bootComp.rowInputVar = varFromOffset BootRow 0 from rfl,
    eval_emittedSeam, eval_bootPushMsg]
  simp only [Expression.eval, Variable.index, mul_one]

/-- A single Mem row's evaluated seam contribution: prev pull (tag `segment_id`,
    mult -1) + last push (tag `segment_id + 1`, gated mult `1 - is_last_segment`). -/
@[reducible] def memRowSeamContribution (v : MemRow FGL) : List (Interaction FGL) :=
  [ emittedSeamValue (-1) (segPrevVal v),
    emittedSeamValue (1 - v.is_last_segment) (segLastVal v) ]

/-- The Mem component's per-row seam contribution evaluated at a `toElements`
    row equals `memRowSeamContribution`. -/
theorem memRow_interactionValuesWith (v : MemRow FGL) (data : ProverData FGL) :
    componentWithDualMemBus.operations.interactionValuesWith SeamContChannel.toRaw
        (Environment.fromArray (toElements v).toArray data)
      = memRowSeamContribution v := by
  simp only [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_seam,
    List.map_cons, List.map_nil, memRowSeamContribution]
  have h_prevmult : (Environment.fromArray (toElements v).toArray data)
      (-1 : Expression FGL) = (-1 : FGL) := by
    simp only [Expression.eval, Variable.index, mul_one]
  have h_lastmult : (Environment.fromArray (toElements v).toArray data)
      (1 - (varFromOffset MemRow 0).is_last_segment) = 1 - v.is_last_segment := by
    show (1 : FGL) + (-1 : FGL) *
        ((Environment.fromArray (toElements v).toArray data)
          ((varFromOffset MemRow 0).is_last_segment)) = 1 - v.is_last_segment
    rw [eval_is_last]; ring
  rw [show componentWithDualMemBus.rowInputVar = varFromOffset MemRow 0 from rfl,
    eval_emittedSeam, eval_emittedSeam, eval_segPrevMsg, eval_segLastMsg,
    h_prevmult, h_lastmult]

/-- A Mem table's seam interactions = the flatMap of its rows' contributions. -/
theorem memTable_interactionsWith (rows : List (MemRow FGL)) (data : ProverData FGL) :
    (mkTable componentWithDualMemBus rows data).interactionsWith SeamContChannel.toRaw
      = rows.flatMap memRowSeamContribution := by
  simp only [Table.interactionsWith, mkTable, List.flatMap_map, Table.environment]
  apply List.flatMap_congr
  intro v _
  exact memRow_interactionValuesWith v data

/-- A 2-row Mem table's seam interactions = the two rows' contributions. -/
theorem memTable_two_interactionsWith (v0 v1 : MemRow FGL) (data : ProverData FGL) :
    (mkTable componentWithDualMemBus [v0, v1] data).interactionsWith SeamContChannel.toRaw
      = [ emittedSeamValue (-1) (segPrevVal v0),
          emittedSeamValue (1 - v0.is_last_segment) (segLastVal v0),
          emittedSeamValue (-1) (segPrevVal v1),
          emittedSeamValue (1 - v1.is_last_segment) (segLastVal v1) ] := by
  rw [memTable_interactionsWith]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    memRowSeamContribution, List.cons_append, List.nil_append]

/-! ## The concrete real-ensemble witness. -/

variable {length : ℕ} {program : Program length}

/-- The concrete `EnsembleWitness` over the REAL `fullRv64imEnsemble`: every
    non-Mem, non-boot table is EMPTY (contributes `[]` to the seam), the boot
    table carries one boot row, and the Mem table carries two segment rows. The
    table order matches `fullRv64imEnsemble.ensemble.tables` exactly. -/
def mkFullWitness (vb : BootRow FGL) (v0 v1 : MemRow FGL)
    (publicInput : unit FGL) (data : ProverData FGL) :
    EnsembleWitness (fullRv64imEnsemble length program).ensemble where
  tables :=
    [ mkTable ZiskFv.AirsClean.MemAlignReadByte.component [] data
    , mkTable ZiskFv.AirsClean.MemAlignByte.component [] data
    , mkTable ZiskFv.AirsClean.MemAlign.component [] data
    , mkTable bootComp [vb] data
    , mkTable componentWithDualMemBus [v0, v1] data
    , mkTable ZiskFv.AirsClean.ArithDiv.component [] data
    , mkTable ZiskFv.AirsClean.ArithMul.componentWithArithTable [] data
    , mkTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent [] data
    , mkTable ZiskFv.AirsClean.Binary.staticLookupComponent [] data
    , mkTable ZiskFv.AirsClean.BinaryAdd.component [] data
    , mkTable (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) [] data ]
  data := data
  publicInput := publicInput
  same_length := by
    simp [fullRv64imEnsemble, SoundEnsemble.toFormal, SoundEnsemble.addTable_tables,
      SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables,
      SoundEnsemble.empty_tables]
  same_circuits := by
    intro i hi
    simp only [fullRv64imEnsemble, SoundEnsemble.toFormal, SoundEnsemble.addTable_tables,
      SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addChannel_tables,
      SoundEnsemble.empty_tables, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i <;> rfl
  same_data := by
    intro table htable
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htable
    rcases htable with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The full witness's seam interactions reduce to the boot + 2-segment list:
    boot push (tag 0), seg0 pull/gated-push, seg1 pull/gated-push. Every empty
    provider table drops out. -/
theorem mkFullWitness_interactionsWith (vb : BootRow FGL) (v0 v1 : MemRow FGL)
    (publicInput : unit FGL) (data : ProverData FGL) :
    (mkFullWitness (length := length) (program := program) vb v0 v1 publicInput data).interactionsWith
        SeamContChannel.toRaw
      = [ emittedSeamValue 1 (bootPushVal vb),
          emittedSeamValue (-1) (segPrevVal v0),
          emittedSeamValue (1 - v0.is_last_segment) (segLastVal v0),
          emittedSeamValue (-1) (segPrevVal v1),
          emittedSeamValue (1 - v1.is_last_segment) (segLastVal v1) ] := by
  rw [EnsembleWitness.interactionsWith_of_verifier_empty (by rfl)]
  simp only [mkFullWitness, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    mkTable_nil_interactionsWith, bootTable_interactionsWith, memTable_two_interactionsWith,
    List.nil_append, List.cons_append]

/-! ## Bridge: `BalancedInteractions` ignores the channel field.

`balanceOf` inspects only `.msg` and `.mult`. So a list of production seam
interactions and the boot-chain `bootList2` (which uses `SeamChannel5`) have the
same balance iff their `(mult, msg)` projections agree element-wise. -/

theorem balanceOf_proj (l : List (Interaction FGL)) (m : Array FGL) :
    balanceOf l m
      = (((l.map (fun i => (i.mult, i.msg))).filter (fun p => p.2 = m)).map
          (fun p => p.1)).sum := by
  simp only [balanceOf, List.filter_map, List.map_map]; rfl

theorem balancedInteractions_of_proj {as bs : List (Interaction FGL)}
    (h : as.map (fun i => (i.mult, i.msg)) = bs.map (fun i => (i.mult, i.msg)))
    (hbal : BalancedInteractions as) : BalancedInteractions bs := by
  refine ⟨?_, ?_⟩
  · have hlen : as.length = bs.length := by
      have := congrArg List.length h; simpa using this
    rw [← hlen]; exact hbal.1
  · intro m
    have hproj : balanceOf bs m = balanceOf as m := by
      rw [balanceOf_proj, balanceOf_proj, h]
    rw [hproj]; exact hbal.2 m

/-- The production `SeamMessage` value's `toElements` array equals the
    boot-chain's `seam5` 5-tuple. -/
theorem toElements_seamMessage (a b c d e : FGL) :
    (toElements ({ value_0 := a, value_1 := b, addr := c, step := d, segment_id := e }
        : SeamMessage FGL)).toArray = seam5 a b c d e := by
  simp [seam5, explicit_provable_type, ProvableStruct.componentsToElements,
    components, ProvableStruct.toComponents, Vector.toArray_cast,
    Vector.toArray_append]

/-- Map a boot row + two Mem segment rows onto `bootList2`'s free arguments. The
    pull-tags are the rows' `segment_id`s; the gate of seg1's push is
    `1 - v1.is_last_segment`. -/
@[reducible] def asBootList2 (vb : BootRow FGL) (v0 v1 : MemRow FGL) :
    List (Interaction FGL) :=
  bootList2
    vb.boot_value_0 vb.boot_value_1 vb.boot_addr vb.boot_step
    v0.previous_segment_value_0 v0.previous_segment_value_1 v0.previous_segment_addr
    v0.previous_segment_step v0.segment_id
    v0.segment_last_value_0 v0.segment_last_value_1 v0.segment_last_addr v0.segment_last_step
    v1.previous_segment_value_0 v1.previous_segment_value_1 v1.previous_segment_addr
    v1.previous_segment_step v1.segment_id
    v1.segment_last_value_0 v1.segment_last_value_1 v1.segment_last_addr v1.segment_last_step
    (1 - v1.is_last_segment)

/-- The full seam list projects onto `asBootList2` PROVIDED seg0 is non-last
    (`is_last_segment = 0`, so its push multiplicity is `1 - 0 = 1`, matching
    `bootList2`'s `pushMsg5`). seg1's gate stays free (= `1 - v1.is_last`). -/
theorem proj_eq (vb : BootRow FGL) (v0 v1 : MemRow FGL)
    (h0 : v0.is_last_segment = 0) :
    ([ emittedSeamValue 1 (bootPushVal vb),
       emittedSeamValue (-1) (segPrevVal v0),
       emittedSeamValue (1 - v0.is_last_segment) (segLastVal v0),
       emittedSeamValue (-1) (segPrevVal v1),
       emittedSeamValue (1 - v1.is_last_segment) (segLastVal v1) ]
        : List (Interaction FGL)).map (fun i => (i.mult, i.msg))
      = (asBootList2 vb v0 v1).map (fun i => (i.mult, i.msg)) := by
  simp only [asBootList2, bootList2, List.map_cons, List.map_nil,
    pushMsg5, pullMsg5, gatedMsg5, emittedSeamValue, h0, sub_zero,
    bootPushVal, segPrevVal, segLastVal, toElements_seamMessage]

/-! ## EXTRACTION: ensemble `BalancedChannels` → `bootList2` balance. -/

/-- From the seam channel's `BalancedChannel` (the `addChannel` conjunct of the
    full ensemble's `BalancedChannels`), extract the `bootList2` balance for the
    seam channel (seg0 non-last). We consume ONLY the seam channel's balance — the
    exact channel-balance trust class `addChannel` supplies — never any other
    channel's. -/
theorem asBootList2_balanced_of_seamBalance (vb : BootRow FGL) (v0 v1 : MemRow FGL)
    (publicInput : unit FGL) (data : ProverData FGL)
    (h0 : v0.is_last_segment = 0)
    (hseam : EnsembleWitness.BalancedChannel
      (mkFullWitness (length := length) (program := program) vb v0 v1 publicInput data)
      SeamContChannel.toRaw) :
    BalancedInteractions (asBootList2 vb v0 v1) := by
  rw [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith_allTablesWitness,
    mkFullWitness_interactionsWith] at hseam
  exact balancedInteractions_of_proj (proj_eq vb v0 v1 h0) hseam

/-! ## THE SEAM VALUE-EQUALITY, derived end-to-end from real-ensemble balance. -/

/-- From the real ensemble's SEAM `BalancedChannel` (the assumed channel-balance
    trust class, holding on the seam channel because it is in `ens.channels` via
    `addChannel`), `SeamTagChain.boot_chain_derived` forces — for `seg0` non-last
    and `seg1` the last segment — the cross-segment VALUE seam:
    `seg1.previous_segment_* = seg0.segment_last_*`. -/
theorem seam_value_equality (vb : BootRow FGL) (v0 v1 : MemRow FGL)
    (publicInput : unit FGL) (data : ProverData FGL)
    (h0 : v0.is_last_segment = 0) (h1 : v1.is_last_segment = 1)
    (hseam : EnsembleWitness.BalancedChannel
      (mkFullWitness (length := length) (program := program) vb v0 v1 publicInput data)
      SeamContChannel.toRaw) :
    v0.segment_id = 0 ∧ v1.segment_id = 1
      ∧ seam5 v1.previous_segment_value_0 v1.previous_segment_value_1
          v1.previous_segment_addr v1.previous_segment_step v1.segment_id
        = seam5 v0.segment_last_value_0 v0.segment_last_value_1
          v0.segment_last_addr v0.segment_last_step (v0.segment_id + 1) := by
  have hbalanced := asBootList2_balanced_of_seamBalance (length := length)
    (program := program) vb v0 v1 publicInput data h0 hseam
  rw [asBootList2, h1] at hbalanced
  simp only [show (1 : FGL) - 1 = 0 from by ring] at hbalanced
  obtain ⟨ht0, ht1, _hseam0, hseam⟩ := boot_chain_derived
    vb.boot_value_0 vb.boot_value_1 vb.boot_addr vb.boot_step
    v0.previous_segment_value_0 v0.previous_segment_value_1 v0.previous_segment_addr
    v0.previous_segment_step v0.segment_id
    v0.segment_last_value_0 v0.segment_last_value_1 v0.segment_last_addr v0.segment_last_step
    v1.previous_segment_value_0 v1.previous_segment_value_1 v1.previous_segment_addr
    v1.previous_segment_step v1.segment_id
    v1.segment_last_value_0 v1.segment_last_value_1 v1.segment_last_addr v1.segment_last_step
    hbalanced
  exact ⟨ht0, ht1, hseam⟩

/-! ## NON-VACUITY: a concrete balanced 2-NONZERO-segment witness over the REAL
    ensemble (the anti-laundering guard).

`seam_value_equality` quantifies over genuinely free rows; its antecedent must be
SATISFIABLE for it to say something. We exhibit the intended 2-segment chain —
two NONZERO `MemRow` segments + the boot endpoint — and PROVE its seam-channel
balance, transported from `SeamTagChain.goodBootList2_balanced`. -/

/-- The boot row of the intended chain: boot `(0,0,B,0)` at tag 0
    (`B = 335544320 =` ZisK's `internal_base_address`). -/
@[reducible] def goodBoot : BootRow FGL :=
  { boot_value_0 := 0, boot_value_1 := 0, boot_addr := 335544320, boot_step := 0 }

/-- seg0 (`MemRow`): segment 0, NON-last. prev = boot `(0,0,B,0)`; last
    `(1,0,100,5)` pushed at tag 1. The 13 base columns carry a real,
    `Spec`-satisfying read row at addr 100; the 10 seam columns hold this
    segment's boundary. -/
@[reducible] def goodSeg0 : MemRow FGL :=
  { addr := 100, step := 5, sel := 1, addr_changes := 1, step_dual := 0, sel_dual := 0,
    value_0 := 1, value_1 := 0, wr := 1, previous_step := 0, increment_0 := 0,
    increment_1 := 0, read_same_addr := 0,
    segment_id := 0,
    previous_segment_value_0 := 0, previous_segment_value_1 := 0,
    previous_segment_addr := 335544320, previous_segment_step := 0,
    segment_last_value_0 := 1, segment_last_value_1 := 0,
    segment_last_addr := 100, segment_last_step := 5,
    is_last_segment := 0 }

/-- seg1 (`MemRow`): segment 1, the LAST segment (`is_last_segment = 1`, its push
    gated off). prev = seg0.last `(1,0,100,5)` (THE SEAM); would-be last
    `(2,0,200,9)`. -/
@[reducible] def goodSeg1 : MemRow FGL :=
  { addr := 200, step := 9, sel := 1, addr_changes := 1, step_dual := 0, sel_dual := 0,
    value_0 := 2, value_1 := 0, wr := 1, previous_step := 0, increment_0 := 0,
    increment_1 := 0, read_same_addr := 0,
    segment_id := 1,
    previous_segment_value_0 := 1, previous_segment_value_1 := 0,
    previous_segment_addr := 100, previous_segment_step := 5,
    segment_last_value_0 := 2, segment_last_value_1 := 0,
    segment_last_addr := 200, segment_last_step := 9,
    is_last_segment := 1 }

/-- The intended chain's `asBootList2` is exactly `SeamTagChain.goodBootList2`. -/
theorem asBootList2_good : asBootList2 goodBoot goodSeg0 goodSeg1 = goodBootList2 := by
  rfl

/-- THE SATISFIABILITY WITNESS: the concrete 2-NONZERO-segment chain's seam
    channel BALANCES on the REAL `fullRv64imEnsemble`. This proves the seam
    conjunct of `BalancedChannels` (hence of `AcceptedTrace`) is INHABITED for a
    real multi-segment Mem trace — NOT vacuously true. -/
theorem good_seam_balancedChannel (publicInput : unit FGL) (data : ProverData FGL) :
    EnsembleWitness.BalancedChannel
      (mkFullWitness (length := length) (program := program)
        goodBoot goodSeg0 goodSeg1 publicInput data)
      SeamContChannel.toRaw := by
  rw [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith_allTablesWitness,
    mkFullWitness_interactionsWith]
  refine balancedInteractions_of_proj (as := goodBootList2) ?_ goodBootList2_balanced
  rw [← asBootList2_good]
  exact (proj_eq goodBoot goodSeg0 goodSeg1 (by rfl)).symm

/-- NON-VACUOUS instantiation: running `seam_value_equality` on the concrete
    balanced 2-nonzero-segment witness lands the tags at `(0,1)` and the SEAM
    holds — `seg1.previous_segment_* (1,0,100,5) = seg0.segment_last_* (1,0,100,5)`.
    Certifies non-vacuity END-TO-END on the REAL ensemble. We feed
    `seam_value_equality` ONLY the seam channel's balance
    (`good_seam_balancedChannel`), the exact `addChannel` conjunct — so the
    derivation rests on nothing beyond the channel-balance trust class. -/
theorem good_seam_holds (length : ℕ) (program : Program length)
    (publicInput : unit FGL) (data : ProverData FGL) :
    seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1) := by
  obtain ⟨_, _, hseam⟩ := seam_value_equality (length := length) (program := program)
    goodBoot goodSeg0 goodSeg1 publicInput data (by rfl) (by rfl)
    (good_seam_balancedChannel (length := length) (program := program) publicInput data)
  simpa using hseam

end ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom, NO
`native_decide`. The seam balance + value seam on the REAL ensemble are
kernel-only, NON-VACUOUSLY satisfied by a concrete 2-nonzero-segment witness. -/
#print axioms ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity.mkFullWitness_interactionsWith
#print axioms ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity.seam_value_equality
#print axioms ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity.good_seam_balancedChannel
#print axioms ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity.good_seam_holds
