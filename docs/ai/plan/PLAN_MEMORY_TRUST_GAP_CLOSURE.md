# Plan: Memory Trust Gap Closure

## Summary

Close the soundness-critical load-memory trust gap currently represented by
`ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load`.

The prior `memory-trust-gap` branch made real progress, but it got inefficient:
it added useful byte-addressed replay machinery and theorem-shaped local load
proofs, then spent a large amount of code moving the same hard obligation
through progressively more specialized `OpEnvelope` and full-ensemble wrapper
objects. The proper closeout is not to keep extending that wrapper stack. The
proper closeout is to prove one canonical theorem:

```lean
MemoryTraceAgreement selectedSailState selectedMemEvent
```

from raw accepted execution data, selected load evidence, and accepted Mem trace
facts. Only after that theorem exists should it be threaded into load wrappers
and used to delete the axiom.

## Current Understanding

The local load proof problem is mostly solved in the old memory branch. The
durable work there includes:

- `ZiskFv/ZiskCircuit/MemTrace.lean`: byte-addressed `MemEvent`, replay
  semantics, `ReplayMemoryAgreement`, `MemoryTraceAgreement`, per-prefix replay
  induction, and read-event projection lemmas.
- `ZiskFv/ZiskCircuit/MemModel.lean`: local load correctness can be stated as a
  theorem consuming explicit `MemoryTraceAgreement`, instead of an arbitrary
  Sail state axiom.
- Load wrappers: enough experience exists to route load families through
  replay agreement rather than raw byte facts.
- FullEnsemble/Mem projection work: useful active primary/dual replay-row
  projection lemmas exist, especially around active selector-gated Mem rows.

The hard part remains unproved. In the old branch, the primary theorem still
takes a premise equivalent to:

```lean
env.AcceptedFullExecutionMemoryActiveReplayRowSplitTraceEnvelopeStateSelectionSourceAtEnvelope
```

That premise contains the real gap:

- active replay extraction;
- selected envelope Mem-row occurrence in the active Mem replay table;
- selected prefix-state equality between the Sail state before the load and the
  replay state after all earlier accepted Mem events.

So the old branch names the gap but does not close it.

## Non-Goals

- Do not continue adding compatibility wrappers or theorem variants whose only
  purpose is translating between equivalent memory evidence packages.
- Do not chase a zero-axiom trust ledger by hiding assumptions in constructor
  fields.
- Do not try to land the entire old memory branch as-is.
- Do not remove `row_models_sail_state_load` until the replacement theorem is
  genuinely proved from accepted execution data, or an explicit fallback trust
  boundary is intentionally added and documented.

## Strategy

Restart from current `main` in a fresh branch/worktree and selectively port only
the durable memory pieces from `.worktrees/memory-trust-gap`.

The branch diff should stay small enough to review. The rule of thumb is:
if a file only adapts between two public memory-evidence packages, do not port
it. If a file proves byte replay, Mem row projection, selected read agreement,
or local load correctness, consider porting it.

## Target Theorem

Introduce a canonical theorem shaped like this, with exact types adjusted to the
existing accepted/full-ensemble objects:

```lean
theorem memoryTraceAgreement_of_accepted_full_execution
    (raw : RawAcceptedExecutionMemoryData ...)
    (selected : SelectedLoadFromExecution ...)
    : ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement
        selected.sailState
        selected.memEvent
```

This theorem is the center of the project. Everything else should either:

- define the raw accepted data it consumes;
- prove a helper used by it;
- route its conclusion into existing load correctness.

If the repo lacks an adequate raw accepted-execution type, introduce one. It
must contain raw accepted trace/full-ensemble data, not pre-expanded semantic
facts such as `MemoryTraceAgreement`, selected prefix-state equality, or
read-value replay soundness.

## Work Plan

### 1. Start Clean

- [ ] Create a fresh branch/worktree from current `origin/main`.
- [ ] Copy this plan into that worktree's `docs/ai/plan/`.
- [ ] Set that worktree's `STATUS.md` to this plan.
- [ ] Confirm current explicit trust state before memory work:
  `aeneas_bridge_trust` and `row_models_sail_state_load` are expected in the
  global closure.

Verification:

```bash
lake build ZiskFv.Compliance
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

### 2. Port Durable Replay Core

- [ ] Port or recreate `MemTrace.lean` in a compact form:
  `MemEvent`, byte lanes, store replay, event replay, prefix replay,
  `ReadEventReplayAgreement`, and `MemoryTraceAgreement`.
- [ ] Keep names stable where the old branch already worked, unless current
  main makes a better name obvious.
- [ ] Avoid importing `Compliance/OpEnvelope` into the replay core.
- [ ] Prove the core replay lemmas with Lean LSP assistance.

Acceptance criteria:

- `lake build ZiskFv.ZiskCircuit.MemTrace` passes.
- The replay core contains no public `OpEnvelope`-specific source objects.

### 3. Make Local Load Correctness Theorem-Shaped

- [ ] Update `MemModel.lean` so load correctness consumes
  `MemoryTraceAgreement state (eventOfEntry e)`.
- [ ] Keep or restore `row_models_sail_state_load` temporarily as the explicit
  old trust boundary until all wrappers are retargeted.
- [ ] Update the local 1/2/4/8-byte projection lemmas to use the new theorem.
- [ ] Fix address semantics while doing this: the memory-bus pointer is the
  byte address, and the Mem AIR word address relation is `ptr = addr * 8`
  where applicable. Do not preserve the old `mem.addr = e.ptr` pin in active
  load proofs.

Acceptance criteria:

- Local load files build.
- A search for active legacy address pins is clean or limited to documented
  compatibility code.

Suggested scan:

```bash
rg -n "mem_legacy_addr|mem\\.addr .* = .*\\.ptr|row_models_sail_state_load" ZiskFv
```

### 4. Prove the Mem-Table Side

This is the extraction/AIR-heavy part. It should be done before attempting to
thread anything through the global theorem.

Prove, for the concrete mutable Mem table selected by the accepted full
ensemble:

- [ ] active primary replay-row projection;
- [ ] active dual replay-row projection for the pinned `dual_mem = 1` case;
- [ ] selector gating: inactive Mem rows do not emit active replay events;
- [ ] chronological active replay row list, primary then dual for each provider
  row when both are active;
- [ ] row order/nodup facts needed for selected cursor uniqueness;
- [ ] read-value soundness: a read event emits the bytes currently in replay
  memory;
- [ ] store-update soundness: a write event updates replay memory in the same
  byte-addressed shape as Sail memory;
- [ ] selected load provider-row occurrence in the concrete Mem table.

If current generated Lean does not expose enough Mem constraints to prove these
facts, expand `tools/pil-extract` narrowly for Mem table/global constraints.
Do not expand extraction speculatively. The extraction target is exactly the
facts above.

Acceptance criteria:

- A theorem exists that constructs an accepted chronological Mem replay trace
  from the concrete accepted Mem table, without assuming read replay soundness
  or ordering as fields.
- The theorem handles dual Mem rows.

### 5. Prove the Sail-Prefix Side

This is the actual hardest part.

Define or identify a memory-only execution timeline:

```lean
stateAt : List MemEvent -> SailState
```

Then prove:

- [ ] `stateAt []` agrees with the initial replay memory.
- [ ] Prior stores mutate `stateAt` memory exactly like `replayStoreEvent`.
- [ ] Prior loads do not mutate memory.
- [ ] The selected load's Sail state equals `stateAt priorEvents`.

The last bullet is the critical proof. It requires accepted execution order to
connect:

- Main row order;
- Mem event timestamps/order;
- the Sail state threaded through opcode execution;
- selected load envelope/event occurrence.

If the current repo does not expose enough accepted execution timeline data to
prove this, stop and make the missing timeline assumption explicit. Do not hide
it inside another `OpEnvelope` source object.

Fallback boundary, if needed:

```lean
axiom selected_load_sail_prefix_memory_timeline_trust :
  ... -> ReplayMemoryAgreement selectedSailState (replayEvents init priorEvents)
```

This fallback is still progress if it is narrower and more honest than
`row_models_sail_state_load`: it should talk about the selected Sail prefix
state and replay memory, not directly assert arbitrary load bytes for an
arbitrary state.

### 6. Prove the Canonical Agreement Theorem

Combine the Mem-table side and Sail-prefix side:

- [ ] selected event occurs as `priorEvents ++ event :: laterEvents`;
- [ ] event is a read;
- [ ] replay memory after `priorEvents` agrees with selected Sail state;
- [ ] read-event replay soundness gives the emitted bytes;
- [ ] therefore `MemoryTraceAgreement selectedSailState event`.

Acceptance criteria:

- The theorem conclusion is exactly the local proof's needed
  `MemoryTraceAgreement`.
- The theorem does not assume selected prefix-state equality or read replay
  soundness as raw fields unless those are explicitly named fallback trust
  boundaries.

### 7. Thread Through Load Wrappers

- [ ] Update LD, LBU, LHU, LWU, LB, LH, and LW wrappers to get
  `MemoryTraceAgreement` from the canonical theorem.
- [ ] Keep store wrappers unchanged except for shared helper type changes.
- [ ] Avoid adding new top-level compatibility theorem variants.
- [ ] Keep the public theorem boundary honest: either the canonical proof is
  fully internal, or any fallback memory timeline trust axiom appears in the
  global closure.

Acceptance criteria:

- Load equivalence theorems no longer depend on
  `row_models_sail_state_load`.
- `row_models_sail_state_load` can be deleted or left unused before deletion.

### 8. Remove or Replace the Axiom

Two acceptable outcomes:

1. Full closure:
   - delete `row_models_sail_state_load`;
   - remove `ZiskFv/ZiskCircuit/MemModel.lean` from
     `trust/allowed-axiom-files.txt` if it has no other trust declarations;
   - global closure should no longer contain the memory load axiom.

2. Honest narrower fallback:
   - delete `row_models_sail_state_load`;
   - add a narrower explicit timeline/replay trust axiom;
   - global closure should contain the new memory timeline boundary.

The second outcome is preferable to pretending the gap is closed if the
accepted Sail timeline is not currently extractable/provable.

### 9. Prune and Verify

- [ ] Delete obsolete memory evidence wrappers/adapters.
- [ ] Update `trust/trusted-base.md`.
- [ ] Regenerate trust ledgers.
- [ ] Update `STATUS.md`, `docs/ai/PROJECTS.md`, and this plan checklist.
- [ ] Run full verification.

Required verification:

```bash
lake build ZiskFv.Compliance
lake build ZiskFv
trust/scripts/regenerate.sh
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
rg -n "\\baxiom\\b|row_models_sail_state_load|mem_legacy_addr|mem\\.addr .* = .*\\.ptr" ZiskFv trust
nix run .#test
```

If `nix run .#test` is unavailable or too slow, record exactly why and what was
run instead.

## Decision Gates

### Gate A: Is Mem Extraction Enough?

After porting the replay core, audit whether generated/extracted Mem artifacts
expose:

- active selectors;
- primary/dual emitted rows;
- chronological order;
- same-address value carry;
- write-update value behavior;
- segment boundary carry-in/out;
- timestamp/address monotonicity.

If not, add focused extraction before writing more Lean adapters.

### Gate B: Is the Sail Timeline Enough?

Before threading through global compliance, audit whether the repo can identify
the selected Sail state as the state after executing exactly the prior accepted
memory events.

If not, add the narrow explicit timeline trust boundary. Do not continue by
adding another `AcceptedFullExecutionMemory...SourceAtEnvelope` wrapper.

### Gate C: Is the Branch Still Reviewable?

If the diff exceeds a small, focused memory slice before the canonical theorem
exists, stop and split:

- PR 1: replay core plus local load theorem shape;
- PR 2: Mem table extraction/projection proof;
- PR 3: Sail-prefix theorem and axiom retirement.

## What to Salvage From the Old Branch

Likely salvage:

- `ZiskFv/ZiskCircuit/MemTrace.lean`;
- theorem-shaped parts of `ZiskFv/ZiskCircuit/MemModel.lean`;
- byte-address row matching changes;
- active primary/dual Mem replay projection lemmas from
  `ZiskFv/AirsClean/FullEnsemble/Balance.lean`;
- narrow `tools/pil-extract` Mem changes if they directly expose needed facts.

Likely do not salvage directly:

- long chains of `zisk_riscv_compliant_program_bus_of_*` memory wrappers;
- public `OpEnvelope` source objects whose only purpose is to carry selected
  prefix-state equality;
- compatibility constructors that translate between equivalent memory evidence
  packages;
- stale trust-ledger/docs churn from the old zero-axiom attempt.

## Success Criteria

- Local load correctness consumes proved `MemoryTraceAgreement`.
- Selected load `MemoryTraceAgreement` is derived from accepted Mem replay plus
  selected Sail prefix state.
- `row_models_sail_state_load` is removed.
- Any remaining memory trust is narrower, explicit, and visible in the global
  axiom closure.
- The final diff is organized around one canonical theorem, not a family of
  wrapper variants.
