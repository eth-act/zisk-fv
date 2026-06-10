# Plan: Discharge `LoadPromises.mem_read`

Supersedes `PLAN_MEMORY_TRUST_GAP.md` and `PLAN_MEMORY_TRUST_GAP_CLOSURE.md`
(both live only on the `memory-trust-gap` branch). This plan restates the goal
against current `main` (post PR #62/#63) and salvages the durable pieces of
`.worktrees/memory-trust-gap` while scrapping its wrapper stack.

## Assessment of the `memory-trust-gap` branch

Direct content diff vs current `origin/main`: 80 files, +21,860 / −1,024.

**Durable (salvage):**

| Piece | Size | What it is |
|---|---|---|
| `ZiskFv/ZiskCircuit/MemTrace.lean` | +1,085 | Byte-addressed replay core: `MemEvent`, `replayStoreEvent`, `replayEvents`, `TraceReplaySound`, prefix-cursor projection (`readEventReplayAgreement_of_trace_sound`), `MemoryBusRowsPrefixReadSound`, `byte_facts_of_event_agreement`. Real induction proofs, `OpEnvelope`-free. |
| `ZiskFv/Airs/Mem.lean` additions | +970 | Mem AIR machinery: `SegmentColumns`, `previous_row_step`, `delta_step`/`delta_addr`, `segment_every_row` — the generated constraints 0–23 bundled for ordering/continuity proofs. |
| `tools/pil-extract` Mem changes | ~126 lines | Narrow extractor extension exposing the Mem segment/global constraints the above consumes. |
| `ZiskFv/AirsClean/Mem/TraceSpec.lean` (targets only) | part of +650 | `GeneratedMemRows`, `GeneratedMemRowOrderFacts` (chronological order), `GeneratedMemReplayFacts` (initialMemory + prefixReadSound + initialAgreement) — correct statements of the proof obligations. |
| `FullEnsemble/Balance.lean` projections | part of +2,133 | `mem*ReplayEntriesOfRow`, active-selector gating, dual-row projection, `exists_mem_table_of_fullRv64im_witness` — table-side projection lemmas from the full-ensemble witness. |
| `MemModel.lean` re-theoremed | +120 | `mem_load_correct_of_provider_row` consuming `MemoryTraceAgreement` instead of 8 raw byte facts; byte-address row matching (`ptr = addr * 8` fix, dropping the legacy `mem.addr = e.ptr` pin). |

**Scrap (do not port):**

- The `AcceptedFullExecutionMemory*` family in `Compliance/OpEnvelope.lean`
  (+11,369) and `Compliance.lean` (+1,657): dozens of structures named by their
  provenance chain (`...ActiveReplayRowSplitTraceEnvelopeStateSelectionSourceAtEnvelope`)
  plus pairwise repackaging functions. Every one of them re-carries the same
  unproven leaf fields. Zero proof content.
- `AcceptedMemTrace`'s vestigial `storeReplaySound / eventOrderingSound /
  segmentCarrySound / dualEventsSound : Prop` placeholder fields.
- The branch's trust-ledger/docs churn (diverged baselines, old plan files).
- Compatibility constructors translating between equivalent evidence packages.

**Bottom line.** The branch proved the replay *core* and built the Mem AIR
*vocabulary*, but the four hard leaves are still assumed as structure fields:
(1) Mem-row order facts, (2) prefix-read soundness, (3) initial-memory
agreement, (4) selected-load prefix-state equality. The 13k-line wrapper stack
only renamed and re-routed them. (1) and (2) are provable from the Mem AIR;
(3) and (4) are the irreducible Sail-timeline boundary until a whole-execution
induction exists.

## Goal and trust decomposition

Discharge the original **promise hypothesis**
`LoadPromises.mem_read : LoadByteAgreement state e1` (formerly tracked as trust
class "Memory load byte agreement" in `trust/trusted-base.md`).

At plan start, `mem_read` was a per-load byte oracle: the constructor of any load
`OpEnvelope` arm asserts, with no provenance, that the circuit's load entry
bytes equal Sail memory. The **promise discharge** splits it into:

- **To prove (circuit side):** every read event in the accepted Mem trace
  returns the last value written at that address — derived from the extracted
  Mem AIR continuity/ordering constraints (same-address value carry, write
  update, segment carry, step ordering, dual rows). This is the
  `AcceptedMemoryReplayEvidence.prefixReadSound` field for the concrete
  accepted table.
- **Residual (one narrow visible boundary):** Sail memory at the selected load
  equals the replay of the prior accepted events from an initial memory that
  agrees with the initial Sail state — i.e. leaves (3)+(4). Stated **once,
  globally**, as a visible hypothesis on `zisk_riscv_compliant_program_bus` in
  the established `h_bridge : env.aeneasBridgeTrust` idiom. No new axiom; the
  global project-axiom closure stays at 0.

This is a genuine shrink: the trusted content drops from "arbitrary bytes per
load" to the named accepted-replay and Sail-memory timeline evidence. Full
closure of the residual boundary is a future whole-execution-induction
milestone, explicitly out of scope here.

## Architecture rules (guardrails against re-derailing)

1. **One global memory-evidence hypothesis.** A single
   `MemoryTimelineEvidence`-shaped object (working name; final name fixed in
   Phase C) appears once on the global theorem. No per-opcode memory source
   objects on `OpEnvelope`; load arms *consume* the global object, they do not
   carry memory evidence in constructor fields.
2. **No provenance-chain names.** Any new structure whose name concatenates
   more than two evidence stages is a smell; stop and restate.
3. **Hard budget:** `Compliance/OpEnvelope.lean` may grow by at most ~300
   lines across the whole plan. If a step seems to need more, the design is
   wrong — stop and re-plan.
4. Replay core stays `OpEnvelope`-free and `Compliance`-free.
5. No new axioms. The residual boundary is a theorem hypothesis. Any deviation
   requires a prior trust-class PR per `trust/trusted-base.md` rules.
6. Canonical `equiv_<OP>` signatures do not change shape; the discharge
   happens at `LoadPromises` (field removal) and the dispatch/Compliance layer
   (derivation). **Anti-laundering metric** must hold or shrink on
   `trust/generated/baseline-hypothesis-count.txt`; the wrapper
   **caller-burden ledger** diff must be net-negative (the `mem_read` lines
   leave).

## Work plan

### Phase 0 — Setup

- [x] Create branch + worktree `mem-read-discharge` from current
      `origin/main`, manually (`git worktree add`), not via agent isolation.
- [x] Copy this plan into the worktree; point its `STATUS.md` here.
- [x] Remove completed/superseded tracked planning and work-description docs
      (`PLAN_EXPLICIT_TRUST_BOUNDARY_REPAIR.md`, `PLAN_OP_ENVELOPE_GAP.md`,
      `docs/extraction/op-envelope-gap-plan.md`) and prune `PROJECTS.md` to the
      active stream.
- [x] `lake exe cache get` before proof/build work.
- [x] `nix run .#populate`; confirm `lake build ZiskFv.Compliance` and
      `trust/scripts/check-all.sh` green before any change.

### Phase A — Port the durable core (additive only, PR 1)

- [x] Port `MemTrace.lean`, trimmed: replay semantics, `TraceReplaySound`,
      prefix-cursor projection, `MemoryBusRows{ReadWrite,PrefixRead}Sound`,
      `eventOfEntry`/`storeEventOfEntry`, `byte_facts_of_event_agreement`.
      Drop the `Accepted*` packing variants and all `: Prop` placeholder
      fields.
- [x] Port the `Airs/Mem.lean` segment/ordering machinery and the
      `tools/pil-extract` Mem extraction changes; re-run extraction (warm
      pilout — no 17 GiB rebuild) and commit the extractor change.
- [x] Port `Mem/TraceSpec.lean` reduced to the three `Generated*` obligation
      statements plus their direct consumers; no packing chains.
- [x] Port the Balance.lean replay-row projection definitions and
      active/dual-selector lemmas actually referenced by Phase B.
- [x] Verify: `lake build`, V1 gate. No boundary or baseline changes expected.

### Phase B — Prove the Mem-table side (PR 2, the hard provable part)

Target theorem: for the concrete Mem table selected by the full-ensemble
witness, the projected replay-row list satisfies chronological
`GeneratedMemRowOrderFacts` and read events satisfy
`MemoryBusRowsPrefixReadSound` — **derived from `Valid_Mem` constraints, with
no assumed soundness fields**.

- [x] Same-address value carry from continuity constraints (constraints 0–23
      bundle).
- [x] Write-update soundness (written lanes replace, untouched lanes carry).
- [x] Segment boundary carry-in/out.
- [x] Dual-row (`dual_mem = 1`) event emission ordering, primary-then-dual.
- [x] Selector gating: inactive rows emit no events.
- [x] Resolve the proposed `Nodup` cursor-uniqueness requirement.
      Gate A found this was not an extraction gap: `mem.pil:392-397` explicitly
      allows read/read dual rows with `step_dual = step`, and the raw
      `MemoryBusEntry` replay row has no lane tag, so duplicate selected reads
      are valid. Replay soundness is prefix/list-position based and reads do
      not mutate memory, so `GeneratedMemRowOrderFacts` and the table-local
      order facts now require chronological order only. Verified with targeted
      MemTrace/TraceSpec/Balance/load-stack builds, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
      `nix run .#test`, and the timeline consistency witness.
- [ ] Prove full chronological row-order facts for the concrete projected Mem
      table from the Mem sorting/segment constraints.
      Partial: `activeMemReplayEntriesOfTableRow_chronological_of_memTableGeneratedRowsBridge`
      proves the local active-row part from `MemTableGeneratedRowsBridge` plus
      the new `MemTableGeneratedRangeFacts`. The theorem discharges
      primary-before-dual ordering from `mem.pil:397` when `sel_dual = 1`; rows
      with no selected dual are chronological by shape. Cross-row `Pairwise`
      order across provider rows remains open. Verified with LSP diagnostics,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Partial: `previous_primary_step_le_step_of_memTableGeneratedRowsBridge`
      and `previous_dual_step_le_step_of_memTableGeneratedRowsBridge` now
      discharge the adjacent-row same-address/non-boundary timestamp order
      cases from `segment_every_row`, `MemTableGeneratedRangeFacts`, and the
      previous row's dual selector. These are the two predecessor cases needed
      before lifting adjacent order to full table `Pairwise` order. Verified
      with LSP diagnostics, `lake build ZiskFv.AirsClean.FullEnsemble.Balance`,
      full `lake build`, `trust/scripts/check-all.sh`,
      `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.
- [ ] Prove `MemoryBusRowsPrefixReadSound` for the concrete projected Mem table
      from same-address carry, write update, segment carry, and chronological
      order.
      Current gap is now a named proof surface:
      `MemTableGeneratedRowsBridge` connects a Clean table's list positions to
      `rowAt mem idx` and `generated_every_row segment permutation mem idx`.
      `FullWitnessMemTableGeneratedRowsBridge` lifts that to the concrete
      full-ensemble witness. `MemTableGeneratedRangeFacts` now names the
      additional PIL range-check inputs needed to turn generated field
      equations into Nat timestamp order. These still have to be proved or
      supplied from extraction before the chronological and prefix-read proofs
      can be closed. Existing load/envelope surfaces only provide selected-row
      equalities such as
      `h_mem_row : eval memEnv memRowVar = rowAt mem r_mem`, not this whole-table
      bridge.
      Partial: the adjacent same-address read carry path is now projected to
      concrete bridged table rows. `read_same_addr_eq_one_of_memTableGeneratedRowsBridge`
      derives the generated `read_same_addr = 1` witness from the Clean row
      identity (`mem.pil:376`) when `addr_changes = 0` and `wr = 0`;
      `values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge`
      lifts the segment value-carry constraints to table rows; and
      `readEventReplayAgreement_after_previous_primary_write_memTableGeneratedRowsBridge`
      combines those with the replay-core theorem
      `readEventReplayAgreement_of_writeMemoryOfEntry_same` to prove the local
      previous-primary-write -> current-read byte agreement step. The same
      replay theorem also factors the intra-row primary-write -> dual-read case
      as `readEventReplayAgreement_after_primary_write_dual_read_of_row`.
      Verified with LSP diagnostics, LSP restart/build, `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Partial: read-preserving replay and read-to-read carry are now factored
      in the replay core as `replayMemoryAfterBusRow_eq_self_of_read` and
      `readEventReplayAgreement_of_entry_same`. Balance projects those generic
      facts to the bridged adjacent previous-primary-read -> current-read case
      with `readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge`,
      and to the same-row primary-read -> dual-read case with
      `readEventReplayAgreement_after_primary_read_dual_read_of_row`. Verified
      so far with clean Lean LSP diagnostics after an LSP build hook, `lake
      build ZiskFv.ZiskCircuit.MemTrace`, `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Partial: row-chunk composition toward the table-level induction is now
      factored. `MemTrace.lean` proves replay/read-soundness append lemmas
      (`replayMemoryAfterBusRows_append`,
      `memoryBusRowsReadWriteSound_append`, and
      `memoryBusRowsPrefixReadSound_append`), and `Balance.lean` proves
      `memoryBusRowsReadWriteSound_activeMemReplayEntriesOfRow_of_spec` for a
      single generated active replay chunk assuming only incoming soundness for
      any selected primary read. Verified so far with clean LSP diagnostics,
      `lake build ZiskFv.ZiskCircuit.MemTrace`, and `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Partial: first-read/address-change zero initialization is now explicit.
      `MemTrace.lean` defines `zeroedMemoryEntryOfEntry`,
      `zeroMemoryOfEntry`, and `zeroMemoryOfRows`, and proves
      `readEventReplayAgreement_of_zeroMemoryOfEntry` for zero-valued reads.
      `Balance.lean` projects the generated `addr_changes = 1, wr = 0`
      zero-value constraints to
      `readEventReplayAgreement_after_zeroMemoryOfEntry_primary_read_of_addr_change`
      and
      `readEventReplayAgreement_after_zeroMemoryOfEntry_memTableGeneratedRowsBridge`.
      Verified with clean Lean LSP diagnostics after an LSP build hook,
      `lake build ZiskFv.ZiskCircuit.MemTrace`, `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Partial: table-level row-chunk composition is now separated from the
      semantic selected-primary-read proof.
      `memoryBusRowsReadWriteSound_flatMap_activeMemReplayEntriesOfRow`
      composes row-local active replay soundness over any `flatMap`, and
      `memoryBusRowsReadWriteSound_activeMemReplayRowsOfTable_of_primary_reads`
      specializes that induction to `activeMemReplayRowsOfTable`. The remaining
      input is exactly the explicit prefix agreement for each selected primary
      read. Verified with clean Lean LSP diagnostics for
      `ZiskFv.AirsClean.FullEnsemble.Balance`, `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Partial: the table fold's remaining semantic input is now a named
      obligation,
      `ActiveMemReplayRowsOfTablePrimaryReadPrefixSound`, and
      `activeMemReplayRowsOfTablePrefixReadSound_of_primary_reads` derives
      `ActiveMemReplayRowsOfTablePrefixReadSound` from that obligation plus the
      generated row specs and table fold. Verified with clean Lean LSP
      diagnostics for `ZiskFv.AirsClean.FullEnsemble.Balance` and `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`, and
      `trust/scripts/check-all.sh`, and
      `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.
      Partial: generated row specs are now supplied to that theorem by the
      indexed bridge.
      `tableRow_specs_of_memTableGeneratedRowsBridge` converts table-row
      membership into the `Fin` index consumed by the generated row bridge, and
      `activeMemReplayRowsOfTablePrefixReadSound_of_memTableGeneratedRowsBridge`
      leaves only `ActiveMemReplayRowsOfTablePrimaryReadPrefixSound` as the
      remaining input. Verified with clean Lean LSP diagnostics for
      `ZiskFv.AirsClean.FullEnsemble.Balance` and `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`,
      `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.
      Partial: replay-core disjoint-write preservation is now explicit.
      `MemoryBusEntryByteDisjoint` states that two memory-bus entries have
      disjoint eight-byte ranges, and
      `readEventReplayAgreement_of_writeMemoryOfEntry_disjoint` proves that
      replaying a write to such a range preserves an existing read agreement.
      This is the core preservation fact needed to keep first-read/zero-byte
      justifications stable across prior rows at other addresses. Verified so
      far with clean Lean LSP diagnostics for `ZiskFv.ZiskCircuit.MemTrace`,
      `lake build ZiskFv.ZiskCircuit.MemTrace`, and `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`, both trust
      gates, and `nix run .#test`.
      Partial: replay-core disjoint preservation now lifts over raw replay
      prefixes. `readEventReplayAgreement_of_replayMemoryAfterBusRow_disjoint`
      and `readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint`
      preserve a read agreement while replaying prefix rows whose write ranges
      are byte-disjoint from the selected read entry. Verified so far with
      clean Lean LSP diagnostics for `ZiskFv.ZiskCircuit.MemTrace` and
      `lake build ZiskFv.ZiskCircuit.MemTrace`, and `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`, and
      both trust gates, and `nix run .#test`.
      Partial: the address no-wrap input is now named and projected.
      `Airs/Mem.lean` adds `addr_columns_in_range`, mirroring `mem.pil:109`
      (`col witness bits(29) addr`), plus
      `field_addr_times_eight_val_eq_of_lt` for the provider pointer
      conversion. `Balance.lean` extends `MemTableGeneratedRangeFacts` with
      `addrColumns` and proves that unequal internal Mem addresses give
      byte-disjoint primary/primary and primary/dual replay entries. Committed
      as `7db237da`. Verified with clean Lean LSP diagnostics for `ZiskFv.Airs.Mem` and
      `ZiskFv.AirsClean.FullEnsemble.Balance`, target builds for both modules,
      a successful full Lake build through the LSP build hook, and a regular
      full `lake build`; both trust gates and `nix run .#test` pass.
      Partial: replay-core zero-preload fold preservation is now factored.
      `readEventReplayAgreement_of_zeroMemoryOfRows_mem` proves that finite
      zero-preload memory satisfies a contained zero-valued read entry when
      every preload row is either same-pointer or byte-disjoint from it. This
      isolates list/fold bookkeeping before the prior-prefix proof.
      `Balance.lean` adds
      `readEventReplayAgreement_after_zeroMemoryOfRows_memTableGeneratedRowsBridge`,
      proving the table-shaped address-change selected-primary-read fact from
      `MemTableGeneratedRowsBridge` and `MemTableGeneratedRangeFacts`.
      Committed as `2655cc4d`. Verified with clean Lean LSP diagnostics for `ZiskFv.ZiskCircuit.MemTrace`
      and `ZiskFv.AirsClean.FullEnsemble.Balance`, target builds for both, and
      successful full Lake builds through the LSP build hook and regular
      `lake build`; both trust gates and `nix run .#test` pass.
      Partial: this slice lifts the table-shaped zero-preload fact through
      an arbitrary prior replay prefix when every prior active entry is
      byte-disjoint from the selected address-change read:
      `readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_disjoint_memTableGeneratedRowsBridge`.
      It also reduces that byte-disjointness premise to
      prior-prefix address separation with
      `readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_addr_ne_memTableGeneratedRowsBridge`.
      `Airs/Mem.lean` proves
      `previous_addr_lt_addr_of_addr_change_not_boundary_segment_every_row`
      from the generated address-change increment equation plus address and
      increment range checks, and `Balance.lean` projects it as
      `previous_addr_lt_addr_of_addr_change_not_boundary_memTableGeneratedRowsBridge`.
      The split/list bookkeeping is also discharged:
      `priorRows_mem_index_lt_of_split` converts
      `table.table = priorRows ++ providerRow :: laterRows` into indices
      strictly before the split point, and
      `readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_ne_memTableGeneratedRowsBridge`
      leaves only the indexed all-prior address inequality
      `∀ otherIdx, otherIdx.val < idx.val → mem.addr otherIdx.val ≠ mem.addr idx.val`.
      Verified with clean Lean LSP diagnostics for `ZiskFv.Airs.Mem` and
      `ZiskFv.AirsClean.FullEnsemble.Balance`, target builds, full
      `lake build`, `trust/scripts/check-all.sh`,
      `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.
      Latest completed slice exposes the fixed-column shape as
      `MemTableGeneratedFixedColumnFacts`, citing `mem.pil:86`
      (`SEGMENT_L1 = [1,0...]`), and uses it to lift adjacent Mem address
      order to all prior table rows. `previous_addr_le_addr_of_nonfirst_memTableGeneratedRowsBridge`
      proves adjacent monotonicity by splitting on the generated
      `addr_changes` bit; `addr_le_of_index_le_memTableGeneratedRowsBridge`
      iterates that adjacent fact; and
      `prior_addr_ne_of_addr_change_memTableGeneratedRowsBridge` proves the
      all-prior address inequality for a selected address-change row. The new
      `readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_change_memTableGeneratedRowsBridge`
      closes the concrete split-prefix zero-preload proof for selected
      address-change primary reads. Verified so far with clean Lean LSP
      diagnostics for `ZiskFv.AirsClean.FullEnsemble.Balance`, the target
      build, full `lake build`, `trust/scripts/check-all.sh`,
      `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.
      Latest completed slice factors the same-address predecessor step.
      `wr_eq_zero_of_sel_zero_memTableGeneratedRowsBridge` projects the
      generated `wr * (1 - sel) = 0` constraint for inactive rows.
      `readEventReplayAgreement_after_previous_selected_row_memTableGeneratedRowsBridge`
      proves that a selected previous row justifies the current same-address
      read after replaying the previous active row chunk, handling primary
      writes, replay-sound primary reads, and replay-neutral dual reads.
      `readEventReplayAgreement_after_previous_inactive_row_memTableGeneratedRowsBridge`
      handles inactive padding rows that carry address/value without emitting
      active replay entries, and
      `readEventReplayAgreement_after_previous_row_memTableGeneratedRowsBridge`
      packages the selected/inactive split as one predecessor lemma. Verified
      with clean Lean LSP diagnostics for
      `ZiskFv.AirsClean.FullEnsemble.Balance`,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
      Latest completed slice lifts that predecessor step through concrete
      split prefixes. `MemTrace.lean` now proves same-pointer zero-preload
      preservation, so an inactive predecessor row can use a later selected row
      at the same pointer as the preload witness. `Balance.lean` packages the
      split-prefix predecessor replay step and proves
      `readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_to_selected_memTableGeneratedRowsBridge`,
      a strong-induction theorem for same-address predecessors. The current
      reduced table-level theorem,
      `activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_memTableGeneratedRowsBridge_boundary_same_addr`,
      leaves exactly the row-0 same-address boundary input. Clean Lean LSP
      diagnostics pass for `ZiskFv.ZiskCircuit.MemTrace` and
      `ZiskFv.AirsClean.FullEnsemble.Balance`, and both touched target builds
      plus full `lake build`, both trust gates, and `nix run .#test` pass for
      commit `6e52f0d7`.
      Latest completed slice closes that explicit row-0 same-address
      boundary for first Mem segments. `Airs/Mem.lean` proves
      `addr_changes_eq_one_of_first_segment_boundary_segment_every_row` from
      `mem.pil:377`
      (`is_first_segment * SEGMENT_L1 * (1 - addr_changes) = 0`).
      `Balance.lean` projects it as
      `addr_changes_eq_one_of_first_segment_row_zero_memTableGeneratedRowsBridge`
      and derives the first-segment active-table prefix-read theorem under an
      explicit `segment.is_first_segment = 1` input. It also constructs
      `acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge`
      when the accepted row list is the active table projection, filling
      `AcceptedMemoryReplayEvidence.prefixReadSound` from concrete Mem-table
      facts. This intentionally leaves continuation segments to a separate
      initial-memory theorem carrying `previous_segment_*`. Verified so far
      with clean Lean LSP diagnostics for `ZiskFv.Airs.Mem` and target builds
      for `ZiskFv.Airs.Mem` and `ZiskFv.AirsClean.FullEnsemble.Balance`;
      axiom scans of the new first-segment theorems/constructor show no
      `sorryAx` (only the existing Clean component axiom class); the combined
      checkpoint `nix run .#test` passes, including full `lake build`, both
      trust gates, flake repro, cargo tests, and extraction tests. Committed as
      `15775597`.
      Existing full-witness code currently selects the Mem table but does not
      expose `segment.is_first_segment = 1`; generated-row, range,
      fixed-column, and segment-selector facts remain explicit bridge inputs.
      Continuation-memory slice `3773a889` starts the alternative closure path.
      `Airs/Mem.lean` proves that at a segment-boundary row,
      `addr_changes = 0` identifies `mem.addr` with
      `segment.previous_segment_addr`, and a same-address read carries both
      `previous_segment_value_*` chunks. `Balance.lean` defines
      `memPreviousSegmentReplayEntry` plus
      `previousSegmentInitialMemoryOfRows`, then proves
      `readEventReplayAgreement_after_previousSegmentInitialMemory_row_zero_memTableGeneratedRowsBridge`
      for the row-0 same-address continuation base. The same slice generalizes
      the split-prefix predecessor step and the table predecessor induction over
      an arbitrary initial memory, leaving the zero-memory theorem as a wrapper.
      Remaining continuation integration is now the seeded-memory
      address-change base: prove that the previous-segment seed is disjoint from
      those zero-valued reads or is safely overwritten by the finite zero
      preload. Verified with clean LSP diagnostics for `ZiskFv.Airs.Mem` and
      `ZiskFv.AirsClean.FullEnsemble.Balance`, target builds for
      `ZiskFv.Airs.Mem` and `ZiskFv.AirsClean.FullEnsemble.Balance`, and axiom
      scans showing no `sorryAx` in the new continuation declarations; the
      combined checkpoint `nix run .#test` passes, including full `lake build`,
      both trust gates, flake repro, cargo tests, and extraction tests.
      Latest completed continuation slice factors the address-change side of
      that remaining obligation. `Balance.lean` proves
      `readEventReplayAgreement_after_previousSegmentInitialMemory_splitPrefix_addr_change_same_addr_memTableGeneratedRowsBridge`,
      lifting address-change reads through the seeded initial memory when the
      previous-segment seed entry is byte-disjoint from the read. It also proves
      `activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge`,
      constructing the table-level selected-primary-read prefix obligation from
      an explicit seed-disjointness premise. Verified with clean LSP diagnostics
      for `ZiskFv.AirsClean.FullEnsemble.Balance`, the target build
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and axiom scans with
      no `sorryAx` in the new declarations.
      Latest completed range-closure slice removes that explicit
      seed-disjointness callback under a single extractor-facing input.
      `Airs/Mem.lean` proves
      `segment_previous_addr_lt_addr_of_addr_change_segment_every_row`, a
      boundary/general form of address-change strictness for the generated
      previous-address expression. `Balance.lean` proves
      `previous_segment_addr_le_addr_memTableGeneratedRowsBridge`,
      `previous_segment_addr_lt_addr_of_addr_change_memTableGeneratedRowsBridge`,
      and `previousSegmentSeedDisjoint_of_addr_change_memTableGeneratedRowsBridge`,
      then packages
      `activeMemReplayRowsOfTablePrimaryReadPrefixSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range`.
      It also lifts that to
      `activeMemReplayRowsOfTablePrefixReadSound_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range`
      and constructs
      `acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_range`,
      the continuation counterpart of the first-segment accepted replay
      constructor.
      The remaining local input is
      `segment.previous_segment_addr.val < 2^29`, which should be exposed from
      the PIL/extractor bridge rather than assumed as replay soundness. Verified
      with `lake build ZiskFv.Airs.Mem`,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and axiom scans with
      no `sorryAx` in the new declarations, including the continuation accepted
      replay constructor. The full checkpoint `nix run .#test` passes,
      including full `lake build`, both trust gates, flake repro, cargo tests,
      and extraction tests. Balance LSP currently has a stale imported view of
      the new AIR theorem, but the focused compiler target and an isolated
      `import ZiskFv.Airs.Mem` check both see it.
      Latest completed segment-range slice removes that raw 29-bit premise
      from the public continuation constructor surface. `Airs/Mem.lean` proves
      `previous_segment_addr_lt_two_pow_33_of_segment_every_row` from the
      generated `mem.pil:265` base-distance equation plus the `mem.pil:267-268`
      16-bit `distance_base` chunk ranges, and generalizes address-change
      strictness to consume that coarse bound. `Balance.lean` introduces
      `MemSegmentGeneratedRangeFacts`, proves
      `previous_segment_addr_lt_two_pow_29_of_memTableGeneratedRowsBridge` by
      combining the coarse segment bound with row-0 `SEGMENT_L1`, `addr_changes`,
      and `addr` range facts, and packages continuation prefix soundness plus
      accepted replay evidence from these segment range facts. It also proves
      `is_first_segment_eq_one_or_zero_of_memTableGeneratedRowsBridge` and
      `acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts`,
      which chooses the first-segment or continuation constructor from the
      generated segment selector on nonempty tables. Verified so far with
      `lake build ZiskFv.Airs.Mem`,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and axiom scans with
      no `sorryAx` in the new range/selector/accepted-replay declarations.
- [x] **Gate A check:** if a needed constraint is not in the extracted Lean,
      extend `tools/pil-extract` narrowly for exactly that constraint — never
      add an assumed field instead.
- [x] Name the table-to-`Valid_Mem` row-index bridge explicitly instead of
      hiding it in replay/timeline evidence.
      Implemented as `MemTableGeneratedRowsBridge` in
      `FullEnsemble/Balance.lean`, with projections to `GeneratedMemRows`,
      per-position `generated_every_row`, and local Clean `constraints_at`;
      `FullWitnessMemTableGeneratedRowsBridge` names the concrete
      full-ensemble obligation. Verified with `lake build
      ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
      `nix run .#test`.
- [ ] **Constructibility check:** every strengthened `Valid_Mem`-adjacent
      statement cites the PIL constraint it mirrors.
      Partial: `MemTableGeneratedRangeFacts` cites `mem.pil:110`,
      `mem.pil:122`, `mem.pil:384-385`, and the selector-gated
      `mem.pil:397`; the new local active-row chronology theorem cites that it
      does not assert cross-row table order.
      Partial: the new local prefix-read predecessor lemmas cite only the
      generated read-same-address identity, segment same-address/value carry
      constraints, the definitional eight-byte replay write, and the
      read-row no-mutation branch in `MemTrace.lean`; they do not introduce a
      replay-soundness field.
      Partial: the new row-chunk theorem is a pure composition wrapper over
      the already cited row spec booleans, selected dual implies selected
      primary, and the local write/read replay lemmas; it adds no generated
      constraint or replay assumption.
      Partial: the zero-preload bridge cites the generated row-spec
      `addr_changes * (1 - wr)` zero-value constraints for address-change
      reads and records the initial-memory construction explicitly, rather
      than hiding first-read bytes in a replay-soundness field.
      Partial: `addr_columns_in_range` and `MemTableGeneratedRangeFacts.addrColumns`
      now cite `mem.pil:109`; the no-wrap proof is a numeric consequence of
      that 29-bit bound and the Goldilocks modulus.
      Partial: the adjacent address-change order theorem cites `mem.pil:375`
      for the generated increment equation, `mem.pil:384-385` for increment
      range checks, and `mem.pil:109` for address no-wrap.
      Partial: the continuation seed-disjointness theorem cites the same
      generated address-change increment equation/range checks; its public
      segment-range wrapper now derives the required
      `segment.previous_segment_addr.val < 2^29` input from `mem.pil:265`,
      `mem.pil:267-268`, row-0 `SEGMENT_L1` (`mem.pil:86`), row-0
      address-change/continuity constraints, and row address range
      (`mem.pil:109`).
      Partial: `MemTableGeneratedFixedColumnFacts` cites the deterministic
      fixed-column declaration `mem.pil:86` (`SEGMENT_L1 = [1,0...]`) and
      keeps the fixed-column constructibility obligation explicit rather than
      hiding it in replay evidence.
      Partial: `FullWitnessMemReplayBridge` now packages the concrete
      full-witness Mem table, active-row equality, generated-row bridge,
      row-range facts, segment-range facts, fixed-column facts, and nonempty
      evidence; `acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge`
      feeds that package into the first/continuation selector constructor.
      This keeps the remaining extractor-facing facts explicit rather than
      hiding them as replay soundness. Verified with clean LSP diagnostics for
      the new spans, `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and
      axiom scans with no `sorryAx` in the new declarations.
      Partial: `memoryTimelineEvidence_of_fullWitnessMemReplayBridge` now feeds
      that accepted-replay constructor into `MemoryTimelineEvidence`: the
      accepted replay subobject is derived from the full-witness Mem replay
      bridge, while the trace split, selected-read tag, initial Sail agreement,
      and state-at-prefix alignment remain the deliberately residual timeline
      inputs. Verified with clean LSP diagnostics for the new span,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and an axiom scan
      with no `sorryAx`; the trust gate `trust/scripts/check-all.sh` also
      passes after updating the trust-retirement note.
      Audit: current Lean sources expose selected-load MemClean row bridges
      (`MemCleanFullEnsemble`) and the Rust witness populates the relevant Mem
      trace/range/segment values, but there is not yet a Lean object deriving
      the whole-table `FullWitnessMemReplayBridge` fields from an
      `EnsembleWitness`.
      Partial: `FullWitnessMemoryTimelineEvidence` is now the global
      memory-timeline source expected by `OpEnvelope.memoryTimelineEvidence`.
      It carries the concrete `FullWitnessMemReplayBridge` plus only the
      residual timeline fields, and coerces to the existing
      `MemoryTimelineEvidence` API consumed by load proofs. This means
      `AcceptedMemoryReplayEvidence.prefixReadSound` is no longer assumed
      directly by the global load boundary; it is derived from the full-witness
      replay bridge. Verified with LSP diagnostics and `lake env lean` for
      `Balance.lean`, `OpEnvelope.lean`, and the LDSD/Misc/Remaining dispatch
      files, plus `lake build ZiskFv.Compliance`,
      `trust/scripts/check-all.sh`, and `trust/scripts/check-all-semantic.sh`.
      Partial: `memOfTable` now projects the primary Mem columns of a concrete
      Clean Mem table into a `Valid_Mem` named-column view, with stage-2
      permutation columns supplied explicitly. The constructor
      `fullWitnessMemReplayBridge_of_memTable` builds the full-witness replay
      bridge from a witness-selected table plus the remaining generated/range/
      fixed-column facts, so table membership, component identity, row
      projection, row count, and accepted active-row equality are no longer
      independent replay-bridge fields. Verified so far with LSP diagnostics
      `lake env lean ZiskFv/AirsClean/FullEnsemble/Balance.lean`,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and axiom scans with
      no `sorryAx` in the new constructors.
      Partial: `segmentWithFixedL1` specializes the segment package to the
      deterministic fixed-column shape from `mem.pil:86`, and
      `fullWitnessMemReplayBridge_of_memTable_fixedL1` removes
      `MemTableGeneratedFixedColumnFacts` from the caller-facing bridge source.
      Verified with LSP diagnostics, `lake env lean
      ZiskFv/AirsClean/FullEnsemble/Balance.lean`,
      `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, and axiom scans with
      no `sorryAx` in the new fixed-column constructors.
      Partial: table nonemptiness is now derived from the nonempty active-row
      replay projection, which in turn follows from the selected-entry split
      used by timeline evidence. The constructor
      `fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows` consumes
      active-row nonemptiness instead of raw `0 < table.table.length`.
      Verified so far with LSP diagnostics and `lake env lean
      ZiskFv/AirsClean/FullEnsemble/Balance.lean`.
      Current sub-gap: derive the remaining generated/range facts for the
      witness-selected Mem table from concrete extraction/Clean witness data.

Known technical risk (R1): the Mem AIR orders rows by (addr, step), not
execution order. Read soundness only needs same-address predecessors, so prove
it per address group first; the bridge from addr-sorted table order to the
step-chronological event list is a separate permutation lemma. If that bridge
stalls, its statement joins the residual timeline boundary explicitly — do not
bury it in a structure field.

### Phase C — Boundary swap and discharge (PR 3)

- [x] Define the single residual object (final name decided here:
      `MemoryTimelineEvidence state entry`): existence of the accepted Mem
      row trace + initial Sail agreement + selected-prefix state equality for
      read cursors — exactly leaves (3)+(4), nothing provable inside it.
      Refined: the accepted replay part is now named separately as
      `AcceptedMemoryReplayEvidence`; until Phase B is closed it still carries
      `prefixReadSound`, while `MemoryTimelineEvidence` carries the selected
      split, initial-memory agreement, and state-at-prefix alignment.
- [x] Add the one visible hypothesis to `zisk_riscv_compliant_program_bus`
      next to `h_bridge`.
      Implemented as `h_memory_timeline : env.memoryTimelineEvidence`.
      Initially load arms required `Nonempty (MemoryTimelineEvidence state
      bus.e1)`; the boundary has now been strengthened so load arms require
      `Nonempty (FullWitnessMemoryTimelineEvidence state bus.e1)`, while
      non-load arms still require `True`. The full-witness source derives the
      accepted replay subobject from `FullWitnessMemReplayBridge` and coerces to
      the existing `MemoryTimelineEvidence` load-proof API. Verified with
      `lake env lean` on `Balance.lean`, `OpEnvelope.lean`, and the
      LDSD/Misc/Remaining dispatch files, plus
      `lake build ZiskFv.Compliance`, `trust/scripts/check-all.sh`, and
      `trust/scripts/check-all-semantic.sh`; the earlier bare-timeline
      boundary was verified with full `lake build`.
- [x] Remove `mem_read` from `LoadPromises`; in the load dispatch arms derive
      `LoadByteAgreement` = Phase B theorem + replay core + timeline
      hypothesis (`mem_load_correct_of_provider_row` consuming
      `MemoryTraceAgreement`).
      Implemented: `LoadPromises` now carries
      `memory_timeline : MemoryTimelineEvidence state e1` instead of
      `mem_read`; canonical load proofs and wrappers project
      `memory_timeline.memoryTraceAgreement` and derive byte agreement from the
      replay/timeline path. Load `OpEnvelope` constructors and the Aeneas
      extracted-shape bridge take memory-free `LoadStructuralPromises`;
      dispatch reconstructs canonical `LoadPromises` from the global
      `h_memory_timeline : env.memoryTimelineEvidence`, using the coercion from
      `FullWitnessMemoryTimelineEvidence` to `MemoryTimelineEvidence`, before
      calling the load theorems. Verified with the load-stack build,
      `lake build ZiskFv.Compliance`, full `lake build`,
      `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
      `nix run .#test`, and the updated timeline consistency witness.
- [ ] Port the `MemModel.lean` re-theoreming and the byte-address row-match
      fix (`ptr = addr * 8`); scan for legacy pins:
      `rg -n "mem_legacy_addr|mem\.addr .* = .*\.ptr" ZiskFv`.
      Partial: byte-addressed primary/dual Mem-row match predicates and Clean
      adapters are ported, `mem_load_correct_of_provider_row` now consumes
      `MemoryTraceAgreement`, and the Clean load bridge uses the byte-addressed
      provider theorem. The lower Clean load witness/discharge path no longer
      stores or passes the raw `mem.addr = e.ptr` compatibility pin; remaining
      hits are the legacy predicate definitions plus outer OpEnvelope/Aeneas
      compatibility inputs. Verified with targeted load/dispatch build, full
      `lake build`, and `trust/scripts/check-all.sh`.
- [x] Update the 7 load EquivCore/Wrapper files; stores untouched beyond
      shared types.
      Implemented for LB/LH/LW/LBU/LHU/LWU/LD: the canonical proofs and current
      wrappers use `MemoryTimelineEvidence.memoryTraceAgreement`; stores remain
      unchanged.
- [x] Update `trust/trusted-base.md`: retire "Memory load byte agreement",
      add the narrower "Sail memory timeline" boundary section with its
      retirement path (whole-execution induction).
- [x] `trust/scripts/regenerate.sh` + regenerate caller-burden; confirm the
      wrapper caller-burden diff is net-negative and hypothesis counts hold or
      shrink.
      Regeneration produced no generated-file diffs because canonical/wrapper
      theorem signatures stayed shape-compatible; `trust/scripts/check-all.sh`
      confirmed hypothesis-count and caller-burden ledgers still match.
- [x] `trust/consistency/` probe updates: the old byte-oracle witness file
      adapts to the new boundary; a false-probe must still fail to typecheck.
      The witness now constructs `AcceptedMemoryReplayEvidence` plus
      `MemoryTimelineEvidence` and derives `LoadByteAgreement` from them; the
      semantic gate label names the Sail memory timeline witness.

### Phase D — Cleanup

- [ ] Full verification: `lake build`, `check-all.sh`,
      `check-all-semantic.sh`, closure print, `nix run .#test`.
- [ ] Open PRs (1–3 may collapse into 2 if A stays small; never into 1).
- [ ] After landing: delete branch/worktree `memory-trust-gap` (ask first —
      destructive), remove its plan files from `docs/ai/PROJECTS.md` history
      notes.

## Decision gates

- **Gate A (extraction sufficiency):** checked inside Phase B per constraint;
  extraction is believed largely sufficient since the branch already extended
  the extractor.
- **Gate B (timeline):** fixed by design — the timeline is the declared
  residual boundary; no attempt to prove it in this plan.
- **Gate C (reviewability):** each PR stays a focused slice; if Phase B's diff
  outgrows review, split per constraint family.

## Anti-laundering self-check (required before declaring done)

Per `trust/README.md#anti-laundering-terms`: (a) the anti-laundering metric
shrank — hypothesis-count baseline holds/shrinks and the caller-burden ledger
diff is net-negative; (b) no new trust-ledger axiom at all; (c) the new
timeline structure and any new top-level `def` reviewed for hidden-promise
risk and marked `@[reducible]` when in doubt; (d) PR titles/bodies use the
canonical glossary terms (promise hypothesis, promise discharge, trust ledger,
caller-burden ledger, constructibility).

## Success criteria

- `LoadPromises` has no `mem_read` field; `LoadByteAgreement` is derived.
- Circuit-side replay soundness is a theorem from extracted Mem AIR
  constraints with no assumed soundness fields.
- Residual memory trust is exactly one named, visible global hypothesis,
  documented in `trust/trusted-base.md` with a retirement path.
- Global project-axiom closure remains 0.
- `Compliance/OpEnvelope.lean` net growth ≤ ~300 lines.
