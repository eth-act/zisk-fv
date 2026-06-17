import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.Channels.SegmentContinuation
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Mem-with-segment-continuation Clean component (XCAP #103 / XS-PR1, Step 1)

This is the **structural seam-channel-exposure** half of XS-PR1 (the framework
PR for the cross-segment Mem seam). It adds a NEW, self-contained Clean
component variant that — in addition to the dual MemBus emission of
`componentWithDualMemBus` — exposes the **segment-continuation channel**
(`ZiskFv/Channels/SegmentContinuation.lean`) by PULLing `previous_segment_*` and
PUSHing `segment_last_*` as RAW boundary tuples read off the row.

It is built on a NEW row type `MemSeamRow` that carries the 9 segment-boundary
columns as `Var` fields, so the seam tuple is reachable through the component's
`rowInputVar` (the precondition `VmTables.tables_channel`,
`build/clean-lean/Clean/Air/Vm.lean:51-53`, imposes). `MemRow` and
`componentWithDualMemBus` are LEFT UNTOUCHED, so the 28 merged ALU/shift
families and every `FullEnsemble/Balance.lean` projection stay byte-identical:
nothing in the live ensemble imports this module.

## What this module IS and IS NOT (XS-PR1 Step 1 / Step 2 boundary)

**IS:** the live Clean Mem layer's first ability to EXPOSE a
segment-continuation channel from row-local columns — the capability the plan
(PLAN_ENDGAME_XCAP §1, TL;DR) says the per-row component "structurally cannot"
do today. Additive, green, **0 PROJECT (`ZiskFv.*`) axioms** (kernel-only:
`propext`, `Classical.choice`, `Quot.sound`).

**IS NOT:** a derivation of the seam. The channel `Guarantees` is `True`
(matching `MemBusChannel`); the cross-segment fact
`seg.segment_last_* = next_seg.previous_segment_*` is a GLOBAL balance fact of
the migrated `SoundVmEnsemble`, derived via `exists_push_of_pull` (XCAP #103
validated go/no-go PoC). It is NOT, and at the row-emission layer cannot be,
derived from `permutation_every_row`: that constraint is a non-vanishing
condition on a Horner HASH (`im_direct_i * direct_gsum_i + 1 = 0`), carrying no
raw-tuple statement. The seam derivation + driver migration + verifier endpoints
are XS-PR1 Step 2, NOT this increment.

## Trust note

No axioms. The seam emission adds only the trivially-true channel guarantee
(`SeamContChannel.Guarantees := True`), exactly as the MemBus emission does.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)
open Air.Flat

/-- Mem row extended with the 9 segment-boundary columns needed to expose the
    raw segment-continuation seam tuple from `rowInputVar`. The first 13 fields
    mirror `MemRow`; the remaining 9 are `SegmentColumns`'s boundary/tag fields
    (`ZiskFv/Airs/Mem.lean:162-173`) that the seam channel carries RAW. -/
structure MemSeamRow (F : Type) where
  -- base MemRow columns
  addr : F
  step : F
  sel : F
  addr_changes : F
  step_dual : F
  sel_dual : F
  value_0 : F
  value_1 : F
  wr : F
  previous_step : F
  increment_0 : F
  increment_1 : F
  read_same_addr : F
  -- segment-boundary columns (the raw seam tuple components + tag)
  segment_id : F
  previous_segment_value_0 : F
  previous_segment_value_1 : F
  previous_segment_addr : F
  previous_segment_step : F
  segment_last_value_0 : F
  segment_last_value_1 : F
  segment_last_addr : F
  segment_last_step : F
  -- last-segment gating column: the outgoing PUSH of `segment_last_*` is
  -- multiplied by `(1 - is_last_segment)` so the final segment emits NO push
  -- (`mem.pil:241` `direct_gsum_1` gated `* (1 - is_last_segment)`). On the last
  -- segment the chain is terminated by the verifier's global END, not a push.
  is_last_segment : F
deriving ProvableStruct

/-- The base MemBus provider message read off a `MemSeamRow`
    (`mem_op = wr + 1`, `ptr = addr * 8`, `width = 8`, `timestamp = step`). -/
@[reducible]
def seamRowMemBusMessageExpr (row : Var MemSeamRow FGL) :
    ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL) :=
  { mem_op := row.wr + 1
    ptr := row.addr * 8
    timestamp := row.step
    width := 8
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- The dual MemBus provider message read off a `MemSeamRow`. -/
@[reducible]
def seamRowMemBusDualMessageExpr (row : Var MemSeamRow FGL) :
    ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL) :=
  { mem_op := 1
    ptr := row.addr * 8
    timestamp := row.step_dual
    width := 8
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- The incoming-boundary seam message PULLed by a segment (the raw
    `previous_segment_*` tuple, tagged with `segment_id`). Mirrors the
    `direct_gsum_0` tag (`ZiskFv/Airs/Mem.lean:1351-1358`). -/
@[reducible]
def prevSeamMessageExpr (row : Var MemSeamRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := row.previous_segment_value_0
    value_1 := row.previous_segment_value_1
    addr := row.previous_segment_addr
    step := row.previous_segment_step
    segment_id := row.segment_id }

/-- The outgoing-boundary seam message PUSHed by a segment (the raw
    `segment_last_*` tuple, tagged with `segment_id + 1`). Mirrors the
    `direct_gsum_1` tag (`ZiskFv/Airs/Mem.lean:1361-1368`). -/
@[reducible]
def lastSeamMessageExpr (row : Var MemSeamRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := row.segment_last_value_0
    value_1 := row.segment_last_value_1
    addr := row.segment_last_addr
    step := row.segment_last_step
    segment_id := row.segment_id + 1 }

/-- Mem constraints + dual MemBus emission + segment-continuation seam
    emission. The seam interactions use `emit` (NOT `pull`/`push`): both go into
    `channelsWithRequirements` (`assumeGuarantees = false`), keeping the seam OUT
    of `channelsWithGuarantees`. That is the decisive fix (PLAN §4 gotcha): a
    `pull` lands in `channelsWithGuarantees`, which `SoundEnsemble.subset_finished`
    would drag into `finished` — impossible for the both-pull-and-push seam. With
    `emit`, the seam channel joins `ens.channels` via `addChannel` with no
    soundness obligation; only its BALANCE is consumed (the same trust class as
    `trace.balanced`).

    The incoming boundary is emitted at multiplicity `-1` (a pull) tagged
    `segment_id`; the outgoing boundary at multiplicity `(1 - is_last_segment)`
    (a gated push) tagged `segment_id + 1` (`mem.pil:198/235/241`,
    `ZiskFv/Airs/Mem.lean:1357/1367`). On the last segment the gate zeroes the
    push, so it contributes nothing to balance (exercises `exists_push_of_pull`'s
    nonzero-push clause). -/
@[circuit_norm]
def memWithSeamAndMemBus (row : Var MemSeamRow FGL) : Circuit FGL Unit := do
  MemBusChannel.emit row.sel (seamRowMemBusMessageExpr row)
  MemBusChannel.emit row.sel_dual (seamRowMemBusDualMessageExpr row)
  SeamContChannel.emit (-1) (prevSeamMessageExpr row)
  SeamContChannel.emit (1 - row.is_last_segment) (lastSeamMessageExpr row)

/-- Elaborated `memWithSeamAndMemBus` circuit. Exposes both the MemBus
    provider emissions and the segment-continuation pull/push. -/
@[reducible] def memWithSeamAndMemBusElaborated :
    ElaboratedCircuit FGL MemSeamRow unit where
  name := "MemWithSeamAndMemBus"
  main := memWithSeamAndMemBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw, SeamContChannel.toRaw]
  -- Expose the SEAM interactions in detail (the new Step-1 capability); the
  -- MemBus interactions are covered by the requirements/guarantees lists, as in
  -- `Main.mainWithRomMemAndOpBus` (which exposes only its OpBus in detail). The
  -- seam interactions are `emitted` (NOT `pulled`/`pushed`): the incoming
  -- boundary at multiplicity `-1`, the outgoing at the gated `(1 - is_last)`.
  exposedChannels row _ :=
    expose SeamContChannel
      [ emitted (-1) (prevSeamMessageExpr row),
        emitted (1 - row.is_last_segment) (lastSeamMessageExpr row) ]
  channelsLawful := by
    simp [circuit_norm, memWithSeamAndMemBus, seamRowMemBusMessageExpr,
      seamRowMemBusDualMessageExpr, prevSeamMessageExpr, lastSeamMessageExpr,
      MemBusChannel, SeamContChannel]

/-- Mem (with dual MemBus + segment-continuation seam) as a Clean
    `GeneralFormalCircuit`. The Spec is trivial here (`True`): this Step-1
    increment delivers seam-channel exposure only — the per-row Mem Spec and the
    seam derivation are out of scope (Step 2). -/
def circuitWithSeamAndMemBus : GeneralFormalCircuit FGL MemSeamRow unit where
  main := memWithSeamAndMemBus
  localLength _ := 0
  output _ _ := ()
  Assumptions _ _ := True
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  ProverSpec _ _ _ := True
  -- The seam channel is DELIBERATELY absent from `channelsWithGuarantees`: it is
  -- emitted (`assumeGuarantees = false`), so it is a REQUIREMENT, never a
  -- guarantee. This keeps it out of the `subset_finished ⊆ finished` obligation
  -- (PLAN §4); the seam joins the ensemble via `addChannel` (no soundness
  -- obligation), and only its balance is consumed. MemBus stays a guarantee (it
  -- is a finished provider channel).
  channelsWithGuarantees := [MemBusChannel.toRaw]
  channelsWithRequirements := [MemBusChannel.toRaw, SeamContChannel.toRaw]
  exposedChannels row _ :=
    expose SeamContChannel
      [ emitted (-1) (prevSeamMessageExpr row),
        emitted (1 - row.is_last_segment) (lastSeamMessageExpr row) ]
  channelsLawful := by
    simp [circuit_norm, memWithSeamAndMemBus, seamRowMemBusMessageExpr,
      seamRowMemBusDualMessageExpr, prevSeamMessageExpr, lastSeamMessageExpr,
      MemBusChannel, SeamContChannel]
  soundness := by
    circuit_proof_start [MemBusChannel, SeamContChannel]
  completeness := by
    circuit_proof_start [MemBusChannel, SeamContChannel]

/-- Mem (with dual MemBus + segment-continuation seam) as a Clean
    `Air.Flat.Component`. NOT wired into `fullRv64imEnsemble` — that driver
    migration is XS-PR1 Step 2.

    NOTE (Step-2 handoff): the companion
    `componentWithSeamAndMemBus_interactionsWith_seam` lemma — the analogue of
    `componentWithDualMemBus_interactionsWith_memBus` projecting this
    component's `interactionsWith SeamContChannel.toRaw` to the raw pull/push
    pair — is deferred to Step 2, where the `SoundVmEnsemble` balance proof
    actually consumes it (and supplies the multi-channel `expose ++ expose`
    normalization context that keeps the `interactionsWith` computation
    tractable). It is NOT needed by this Step-1 capability increment. -/
def componentWithSeamAndMemBus : Air.Flat.Component FGL := ⟨ circuitWithSeamAndMemBus ⟩

/-- Project this component's `interactionsWith SeamContChannel.toRaw` to the raw
    `emitted` pull/push pair (the analogue of
    `componentWithDualMemBus_interactionsWith_memBus`). This is the Step-2 (L4)
    handoff: the seam-balance extraction over the real ensemble reduces each
    Mem-table row's seam contribution through this lemma. -/
theorem componentWithSeamAndMemBus_interactionsWith_seam :
    componentWithSeamAndMemBus.operations.interactionsWith SeamContChannel.toRaw =
      [ ((SeamContChannel.emitted (-1)
            (prevSeamMessageExpr componentWithSeamAndMemBus.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (1 - componentWithSeamAndMemBus.rowInputVar.is_last_segment)
            (lastSeamMessageExpr componentWithSeamAndMemBus.rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨SeamContChannel.toRaw,
      [ ((SeamContChannel.emitted (-1)
            (prevSeamMessageExpr componentWithSeamAndMemBus.rowInputVar)).toRaw)
        , ((SeamContChannel.emitted (1 - componentWithSeamAndMemBus.rowInputVar.is_last_segment)
            (lastSeamMessageExpr componentWithSeamAndMemBus.rowInputVar)).toRaw) ]⟩ ∈
    componentWithSeamAndMemBus.exposedChannels
  simp only [componentWithSeamAndMemBus, circuitWithSeamAndMemBus,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil, Channel.emitted]

end ZiskFv.AirsClean.Mem
