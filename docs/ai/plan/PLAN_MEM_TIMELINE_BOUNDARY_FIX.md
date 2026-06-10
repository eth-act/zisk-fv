# Plan: Byte-localize the Mem timeline boundary (PR #65 review fixes)

Follow-up to `PLAN_MEM_READ_DISCHARGE.md`. PR #65's review found the
architecture correct (single global `h_memory_timeline`, circuit-side
prefix-read soundness genuinely derived from generated Mem AIR facts, zero
trust-ledger drift, both gates green) but identified one soundness-of-claim
blocker and one must-remove file. This plan fixes both on the
`mem-read-discharge` branch before merge.

**Required reading before starting:**
[`trust/README.md#anti-laundering-terms`](../../../trust/README.md) and the
"Anti-laundering principle" section of `CLAUDE.md`. Use the canonical
glossary terms in all commits and PR text.

## Finding 1 (blocker): the residual boundary is unconstructible for real traces

`zisk/state-machines/mem/pil/mem.pil` line 9: *"Memory is sorted by address
and step"* — the Mem table's row order is **(addr, step)-major, not
execution order**. `activeMemReplayRowsOfTable` projects rows in table
order, so `MemoryTimelineEvidence.priorRows` is an **addr-sorted** prefix.

Two fields of `MemoryTimelineEvidence`
(`ZiskFv/ZiskCircuit/MemTrace.lean:1239`) are stated against that prefix
with whole-state / whole-map strength:

- `stateAtPrefix : state = stateAfterMemoryBusRows initialState priorRows`
  — full `SequentialState` equality after replaying the addr-sorted prefix;
- `initialAgreement : ReplayMemoryAgreement initialState acceptedReplay.initialMemory`
  where `ReplayMemoryAgreement` (line ~108) is two-sided
  `∀ addr, state.mem[addr]? = mem[addr]?` — exact domain-and-content
  equality at every address.

For a real execution, the pre-load Sail memory is
`init ⊕ time-prefix writes`, not `init ⊕ addr-sorted-prefix writes`. Any
program that writes a higher address before the selected load, or a lower
address after it, falsifies `stateAtPrefix`. The current consistency
witness (single row, `priorRows = []`) cannot detect this. Net effect: the
load arms of `zisk_riscv_compliant_program_bus` are conditioned on an
unconstructible hypothesis — the *constructibility* failure mode from the
anti-laundering principle — and the documented retirement path
("prove the whole-execution induction") is unprovable as stated.

**Why the fix is sound and small.** Load soundness only needs Sail/replay
agreement at the selected entry's 8 bytes. In (addr, step) order, all
same-address predecessors of the selected read are contiguous and
step-sorted, so `replayMemoryAfterBusRows initialMemory priorRows` at
`entry.ptr + 0..7` is exactly the last same-address smaller-step write —
the **time-correct** pre-load value. The circuit-side
`prefixReadAgreement` is untouched. Weakening the Sail-side fields to those
8 bytes makes the boundary satisfiable while remaining purely residual
timeline trust. This strictly *weakens* the caller-supplied boundary
(removes one data field and two Prop fields, adds one weaker Prop), so the
anti-laundering metric direction is favorable; all generated ledgers must
stay byte-identical.

### Step 1 — `ZiskFv/ZiskCircuit/MemTrace.lean`

- [x] Add a byte-local agreement predicate next to `ReplayMemoryAgreement`:

  ```lean
  /-- Sail/replay memory agreement restricted to the 8 bytes at `addr`. -/
  def ReplayMemoryAgreementOnBytes
      (state : SailState) (mem : Std.ExtHashMap Nat (BitVec 8))
      (addr : Nat) : Prop :=
    ∀ i : Nat, i < 8 → state.mem[addr + i]? = mem[addr + i]?
  ```

  Mark it `@[reducible]` if any doubt about hidden-promise visibility
  (per anti-laundering rule 5).
- [x] In `structure MemoryTimelineEvidence` (line ~1239): **delete** the
  fields `initialState`, `initialAgreement`, `stateAtPrefix`; **add**:

  ```lean
  stateBytesAtPrefix :
    ReplayMemoryAgreementOnBytes state
      (replayMemoryAfterBusRows acceptedReplay.initialMemory priorRows)
      entry.ptr.toNat
  ```

- [x] Add `memoryTraceAgreement_of_replayAgreementOnBytes` (byte-local
  sibling of `memoryTraceAgreement_of_replayAgreement` at line ~184):
  combine `state.mem[ptr+i]? = replayMap[ptr+i]?` with
  `ReadEventReplayAgreement replayMap (eventOfEntry entry)`
  (which already says `replayMap[ptr+i]? = some (byteAt i)`) to conclude
  `MemoryTraceAgreement state (eventOfEntry entry)`.
- [x] Reprove `MemoryTimelineEvidence.memoryTraceAgreement` (line ~1289)
  via the new lemma; `prefixReadAgreement` (line ~1255) is unchanged.
  Delete `MemoryTimelineEvidence.prefixStateAgreement` (whole-map version);
  audit remaining users first: `rg -n "prefixStateAgreement|stateAtPrefix|initialAgreement" ZiskFv`.
- [x] Keep `ReplayMemoryAgreement` itself — it is still used by the replay
  core internals (`EventReplayStep`, execution-trace lemmas). Only the
  *boundary structure* changes.

### Step 2 — `ZiskFv/AirsClean/FullEnsemble/Balance.lean` residual constructors

Update every constructor that threads the residual fields; drop the
`initialState` / `h_initialAgreement` / `h_stateAtPrefix` parameters and
add the single byte-agreement parameter:

- [x] `memoryTimelineEvidence_of_fullWitnessMemReplayBridge` (~line 6494).
- [x] `structure FullWitnessMemoryTimelineEvidence` (~line 6546) and its
  projection lemmas in the namespace block (~6571–6603).
- [x] `fullWitnessMemoryTimelineEvidence_of_rawSidecars` (~6614) and
  `fullWitnessMemoryTimelineEvidence_of_rawFacts` (~6663).
- [x] `FullWitnessGeneratedTimelineEvidence` and
  `fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`.
- [x] Circuit-side objects (`FullWitnessMemReplayBridge`,
  `MemTableGeneratedRowsBridge`, sidecar structures, all
  `acceptedMemoryReplayEvidence_of_*`) are **unchanged** — do not touch.

### Step 3 — extractor template `tools/pil-extract/src/main.rs`

The generated `Extraction.MemGeneratedArtifact` wrapper mirrors the
constructor signatures:

- [x] Update the emitted `buildTimelineEvidence` (~line 1590) and
  `buildTimelineEvidenceFromExtractedSidecarFacts` (~2511) signatures and
  the surrounding doc text (~2634) for the new residual parameters.
- [x] Update the renderer self-test assertions (~4140–4410) that
  `out.contains(...)` the old strings.
- [x] `cargo test` for pil-extract inside the flake, then
  `nix run .#populate` to regenerate `build/extraction/`; the
  `nix run .#test` gate compiles the regenerated wrapper after
  `lake build` — keep that ordering (it was fixed in `560dfa67`).

### Step 4 — consistency witness as a vacuity regression test

`trust/consistency/load_byte_agreement_witness.lean` (runs as semantic gate
check 5/5):

- [x] Rebuild the witness for the new structure shape.
- [x] **Extend it to a two-address scenario where addr order ≠ time order**,
  so the old whole-state boundary would have been unsatisfiable:
  rows `[w0, r1]` with `w0` = write at `ptr 0`, `timestamp 5` and `r1` =
  read at `ptr 8`, `timestamp 1` (addr-sorted, time-reversed). Select
  `r1` with `priorRows = [w0]`. Choose the witness state whose memory at
  bytes `0..7` does **not** contain `w0`'s written value (the load happens
  before that write in time) while bytes `8..15` agree with the replay.
  This typechecks only with the byte-local boundary — locking the fix in
  as a permanent gate check. Update `prefixReadSound` for the two-row
  list (the `r1` prefix replay must see `initialMemory` at bytes 8..15).

### Step 5 — docs

- [x] `trust/trusted-base.md` "Sail Memory Timeline": restate the residual
  fields (trace split, read tag, byte agreement at the selected entry
  after the accepted addr-sorted prefix); cite the (addr, step) sort
  (`zisk/state-machines/mem/pil/mem.pil` line 9) explicitly; restate the
  retirement path as the now-provable statement — whole-execution
  induction showing, for each selected load, that Sail memory at the
  entry's bytes equals the last same-address accepted write in step order
  (preload base case included); describe the two-address witness scenario.
- [x] Update `PLAN_MEM_READ_DISCHARGE.md` Phase C checklist and `STATUS.md`.
- [x] Update the PR #65 body paragraph describing the residual fields.

Verification completed for the implemented fix:

- `lake build` passed.
- `trust/scripts/check-all.sh` passed all 17 checks.
- `trust/scripts/check-all-semantic.sh` passed all 5 checks; the two-address
  Sail memory timeline witness prints no `sorryAx`.
- `lake exe trust-gate print-axiom-closure
  ZiskFv.Compliance.zisk_riscv_compliant_program_bus` emitted no closure lines;
  stderr only had the existing TrustGate `String.trim` deprecation warnings.
- `nix run .#test` passed all 8 steps.
- `git diff origin/main HEAD --stat -- trust/generated/` was empty.
- `rg -n "stateAtPrefix|prefixStateAgreement" ZiskFv` had no hits.
- `git ls-files AGENTS.md` was empty.
- `git diff --check` passed.

## Finding 2 (must-remove): private `AGENTS.md` committed at repo root

The branch added `AGENTS.md` — a copy of Cody's **private**
`~/ai-workflow/AGENTS.md` personal workflow conventions. Merging would
publish it to `eth-act/zisk-fv`.

- [x] `git rm AGENTS.md` (delete outright; the original lives outside the
  repo). Confirm nothing references it: `rg -n "AGENTS.md" --glob '!docs/ai'`.

## Verification (all required before declaring done)

```bash
lake build
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus  # must be empty
nix run .#test
git diff origin/main HEAD --stat -- trust/generated/   # must be empty
rg -n "stateAtPrefix|prefixStateAgreement" ZiskFv       # only intended remnants
git ls-files AGENTS.md                                  # must be empty
```

Anti-laundering self-check: no new axioms; no canonical `equiv_<OP>`
signature change; all five generated ledgers byte-identical; the boundary
diff visibly removes more obligation than it adds (one data field + two
whole-map Props out, one 8-byte Prop in); commit/PR text uses the glossary
terms (*promise discharge*, *trust ledger*, *constructibility*).

## Boundaries

- Work only on branch `mem-read-discharge` in this worktree; commit in
  small focused commits and push (the PR #65 branch).
- Do not add axioms, do not touch canonical theorem signatures, do not
  modify `OpEnvelope.lean` beyond doc comments (its
  `memoryTimelineEvidence` definition text is unchanged by the structure
  edit), do not refactor beyond the sites listed above.
- Do not delete the `memory-trust-gap` worktree/branch.
- If the byte-local reproof stalls anywhere, stop and report rather than
  re-strengthening the boundary or adding fields.
