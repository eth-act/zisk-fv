import ZiskFv.AirsClean.Mem.SeamCircuit
import Clean.Air.Vm

/-!
# Real cross-segment Mem seam VM (XCAP #103 / XS-PR1, Step 2 — first green increment)

This module builds the REAL `memSegVm : VmTables` over the segment-continuation
channel (`ZiskFv/Channels/SegmentContinuation.lean`), hosting the boot/final seam
endpoint as a genuine VM-channel verifier (channel-balance class), with a
non-trivial multi-segment ensemble witness. It mirrors
`Clean/Examples/FibonacciWithChannels.lean`
(`fibonacciVm` / `fibonacciVerifier` / `fibonacciEnsemble`) exactly.

It reuses the REAL Step-1 row type and message builders from
`SeamCircuit.lean` — `MemSeamRow`, `prevSeamMessageExpr`, `lastSeamMessageExpr` —
so the seam tuples a segment PULLs/PUSHes are the genuine Mem segment-boundary
tuples `[value_0, value_1, addr, step, segment_id]` read off the row, NOT a model
tuple.

## What this module IS and IS NOT (the Step-2 boundary inside this increment)

**IS:** the first time the live Clean Mem layer hosts the segment-continuation
channel as a `VmTables` — a `SoundVmEnsemble` driver with a non-empty verifier
that carries the real boot endpoint (`mem.pil:253`: `is_first_segment *
segment_id = 0` ⇒ boot tag `0`; `mem.pil:269`: `previous_segment_addr = base
335544320`). Additive: a NEW file; nothing in `fullRv64imEnsemble`,
`FullEnsemble.lean`, or `Balance.lean` imports it, so the 28 construction families
stay byte-identical. **0 PROJECT (`ZiskFv.*`) axioms** (kernel-only: `propext`,
`Classical.choice`, `Quot.sound`).

**IS NOT:** the dual-bus host. The Step-1 `componentWithSeamAndMemBus` cannot be
hosted directly in a standalone `addVm` off `SoundEnsemble.empty`: `addVm`'s
`grts_subset_finished` obligation requires every VM table's
`channelsWithGuarantees ⊆ vm.channel.toRaw :: finished`, and with `finished = []`
that forbids the `MemBusChannel.toRaw` guarantee that the dual-bus component also
emits. Marking `MemBusChannel` `finished` (the Fibonacci `addFinishedChannel`
shape) is NOT honest in a standalone seam VM: it would assert a `SoundChannels`
(real MemBus provider/consumer balance) that no MemBus provider tables witness
here. So this increment hosts the SEAM-ONLY projection of the component
(`memSeamTable` below), which is the faithful seam sub-table of
`componentWithSeamAndMemBus` — identical `MemSeamRow` input, identical
`prevSeamMessageExpr` PULL / `lastSeamMessageExpr` PUSH, MINUS the two MemBus
emissions. Hosting the dual-bus component (so MemBus genuinely balances
alongside the seam) is exactly the deferred ensemble-migration increment; see
"## Deferred" at the bottom.

## Trust note

No project axioms. The boot/final seam endpoint is hosted as a real `VmTables`
verifier whose requirements follow unconditionally from its constraints
(`VmTables.verifier_requirements`) — a channel-balance fact, NOT a fresh
`ZiskFv.*` axiom. `SeamContChannel.Guarantees` stays `:= True`: the cross-segment
seam is a BALANCE fact (`exists_push_of_pull` over a `SoundVmEnsemble`), never a
channel guarantee. This mirrors the validated go/no-go PoC `tagged_seam_forced`.
-/

namespace ZiskFv.AirsClean.Mem.SeamVm

open Goldilocks
open Air.Flat
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)
open ZiskFv.AirsClean.Mem (MemSeamRow prevSeamMessageExpr lastSeamMessageExpr)

/-- Goldilocks has characteristic `GL_prime`, a large prime, so `ringChar ≠ 2`.
    `addVm_soundVmChannel_of_soundChannels` (via `SoundEnsemble.addVm`) needs it. -/
instance : Fact (ringChar FGL ≠ 2) := .mk <| by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  have h : ringChar FGL = GL_prime := ringChar.eq FGL GL_prime
  rw [h]; norm_num

/-! ## The boot seam endpoint.

The boot boundary any real Mem trace starts from: the first segment carries
`segment_id = 0` (`mem.pil:253` `is_first_segment * segment_id = 0`) and
`previous_segment_addr = 335544320` (`mem.pil:269`, the base address), with zero
value/step carry. This is the genuine `mem.pil` boot, carried RAW as a
`SeamMessage` (NOT a model tuple). -/
def bootSeam : SeamMessage FGL where
  value_0 := 0
  value_1 := 0
  addr := 335544320
  step := 0
  segment_id := 0

/-! ## The seam-only segment sub-table.

This is the faithful seam projection of the Step-1
`circuitWithSeamAndMemBus`: identical `MemSeamRow` input, identical seam PULL
(`prevSeamMessageExpr`, the raw `previous_segment_*` tuple tagged `segment_id`)
and seam PUSH (`lastSeamMessageExpr`, the raw `segment_last_*` tuple tagged
`segment_id + 1`), MINUS the two MemBus emissions (whose coexistence is the
deferred migration). One PULL + one PUSH = one VM transition.

We add NO algebraic link between the incoming and outgoing tuple in the row: the
cross-segment seam must come from CHANNEL BALANCE, not from this row (the
anti-vacuity discipline the validated go/no-go PoC `tagged_seam_forced`
established — balance forces the matching push; the segment-id tag selects which
push). -/
def memSeamTable : GeneralFormalCircuit FGL MemSeamRow unit where
  main row := do
    SeamContChannel.pull (prevSeamMessageExpr row)
    SeamContChannel.push (lastSeamMessageExpr row)
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ SeamContChannel.toRaw ]
  channelsWithRequirements := [ SeamContChannel.toRaw ]
  exposedChannels row _ :=
    expose SeamContChannel
      [ pulled (prevSeamMessageExpr row), pushed (lastSeamMessageExpr row) ]
  channelsLawful := by
    simp only [circuit_norm, prevSeamMessageExpr, lastSeamMessageExpr, SeamContChannel]
  ProverAssumptions _ _ _ := True
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [SeamContChannel]
  completeness := by
    circuit_proof_start [SeamContChannel]

/-! ## The verifier (non-empty), hosting the boot/final seam endpoint.

The public IO is the FINAL seam (the boundary the last segment carries OUT). The
verifier PULLs that final seam off the channel and PUSHes the boot seam,
closing the cycle boot → seg0 → … → final. Mirrors `fibonacciVerifier` exactly.
This is the channel-balance hosting of the boot endpoint: a real `VmTables`
verifier, NOT a `ZiskFv.*` axiom. -/
def memSeamVerifier : GeneralFormalCircuit FGL SeamMessage unit where
  main finalSeam := do
    SeamContChannel.pull finalSeam
    SeamContChannel.push (ProvableType.const bootSeam)
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ SeamContChannel.toRaw ]
  channelsWithRequirements := [ SeamContChannel.toRaw ]
  exposedChannels finalSeam _ :=
    expose SeamContChannel [ pulled finalSeam, pushed (ProvableType.const bootSeam) ]
  channelsLawful := by
    simp only [circuit_norm, SeamContChannel]
  ProverAssumptions _ _ _ := True
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [SeamContChannel]
  completeness := by
    circuit_proof_start [SeamContChannel]

/-! ## The VM tables.

Two seam segment sub-tables (seg0, seg1) form a NON-TRIVIAL 2-segment witness,
plus the bracketing verifier. Mirrors `fibonacciVm` exactly.

The structural `tables_channel`/`verifier_channel` obligations are discharged with
EXPLICIT seam pull/push witnesses (not `simp`): unfolding `exposedChannels` over
the 22-field `MemSeamRow` `varFromOffset`/`toElements` via `circuit_norm` blows up
whnf (a `simp` body times out even at 4000000 heartbeats), but membership in the
singleton `expose` list is `rfl` once the witnesses are pinned. -/
def memSegVm : VmTables FGL SeamMessage where
  channel := SeamContChannel
  tables := [⟨ memSeamTable ⟩, ⟨ memSeamTable ⟩]
  verifier := memSeamVerifier
  verifier_length_zero := by simp [circuit_norm, memSeamVerifier]
  tables_channel := by
    -- Both tables are `⟨memSeamTable⟩`; provide the seam pull/push as explicit
    -- witnesses so the membership is structural (`List.mem_singleton`), avoiding a
    -- full whnf of the 22-field `MemSeamRow` `varFromOffset`/`toElements`.
    intro table h_table
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_table
    rcases h_table with rfl | rfl <;>
      exact ⟨ prevSeamMessageExpr (varFromOffset MemSeamRow 0),
             lastSeamMessageExpr (varFromOffset MemSeamRow 0), List.mem_singleton.mpr rfl ⟩
  verifier_channel :=
    ⟨ varFromOffset SeamMessage 0, ProvableType.const bootSeam, List.mem_singleton.mpr rfl ⟩
  verifier_requirements env := by
    simp only [circuit_norm, memSeamVerifier, SeamContChannel]

/-! ## The VM ensemble.

`SoundEnsemble.empty.addVm memSegVm` — the standalone seam VM. The three `addVm`
side conditions (no existing table touches the seam channel; the VM tables'/
verifier's guarantees are the seam channel or finished; the VM tables' requirements
contain no finished channel) all discharge by `simp` against the seam-only
component, exactly as Fibonacci's final `addVm`. -/
def memSegEnsemble : SoundVmEnsemble FGL SeamMessage :=
  SoundEnsemble.empty FGL SeamMessage
    |>.addVm memSegVm
      (by simp [circuit_norm, memSegVm, memSeamTable, SeamContChannel])
      (by simp [circuit_norm, memSegVm, memSeamTable, memSeamVerifier, SeamContChannel])
      (by simp [circuit_norm, memSegVm, memSeamTable, memSeamVerifier, SeamContChannel])

/-- The seam VM ensemble is sound: `toFormal` gives a real `FormalEnsemble`. The
    boot/final seam endpoint is now hosted entirely through channel balance. -/
def memSegFormal : FormalEnsemble FGL SeamMessage :=
  memSegEnsemble.toFormal FGL (fun _ _ => True)
    (by simp [circuit_norm, memSegEnsemble, memSegVm, memSeamTable])

/-! ## Deferred (the ensemble-migration increment).

To host the DUAL-bus `componentWithSeamAndMemBus` (so `MemBusChannel` genuinely
balances alongside the seam) the ensemble must first finish `MemBusChannel` via a
real `SoundChannels` proof — i.e. include the MemBus provider/consumer tables that
make MemBus a balanced finished channel — BEFORE `addVm`. That is the disruptive
`fullRv64imEnsemble` migration (`SoundEnsemble → SoundVmEnsemble`, prepend the
seam tables, non-empty verifier, re-prove `Balance.lean`'s projections). It is
explicitly out of scope for this additive increment.

The downstream seam-derivation consumer (`exists_push_of_pull` over
`memSegEnsemble`, deriving `seg.segment_last_* = next_seg.previous_segment_*` from
balance + the `segment_id` tag pins) reuses the validated PoC `tagged_seam_forced`
shape; it is also deferred — this increment delivers only the hosted VM tables.
-/

end ZiskFv.AirsClean.Mem.SeamVm

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`) — i.e. 0 PROJECT (`ZiskFv.*`) axioms; Lean-kernel axioms present as
documented external trust. NO `sorry`, NO project axiom, NO `native_decide`. -/
#print axioms ZiskFv.AirsClean.Mem.SeamVm.memSeamTable
#print axioms ZiskFv.AirsClean.Mem.SeamVm.memSeamVerifier
#print axioms ZiskFv.AirsClean.Mem.SeamVm.memSegVm
#print axioms ZiskFv.AirsClean.Mem.SeamVm.memSegEnsemble
#print axioms ZiskFv.AirsClean.Mem.SeamVm.memSegFormal
