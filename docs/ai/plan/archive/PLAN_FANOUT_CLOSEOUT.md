# PLAN — Fanout closeout: finish every issue the #115 workstream spawned

> **SUPERSEDED (2026-07-13)** by `PLAN_PROJECT_CLOSEOUT.md`. Streams 1–2 landed (PRs #250, #252;
> #220/#225/#245 closed). Streams 3–5 carry over there rescoped: #249 splits into row-level (S1)
> plus a new lookup-wiring extraction stream (S3) that derives `mem_replay_segment_ranges` instead
> of retaining it — owner ruling: completeness, no punts. The #74-ladder parking below is rescinded.

## Context

The #115 workstream (and its interleaved #219/#220 lane) is landing, but it fanned out satellite
issues along the way: #242 and #243 (filed as #115's Fork-A / #237 follow-ons), #245 (from #220's
successor-row fork), #249 (the certificate residues), the reopened #225's residual criterion, and
#226 (the upstream Clean limitation #243 hit). "Closed out" = all of those genuinely finished —
work done, not parked — plus the in-flight #220 tail. Explicitly OUT of scope: the #74 ladder
(#221/#222/#74), #184, the completeness axis, external checks (#77/#78), and hygiene backlog —
those were never this workstream's target and stay as they are (the Tier 1 milestone remains their
eventual bar, untouched by this plan).

**Owner rulings baked in (2026-07-09):** #226 is resolved fork-only — patch a pinned Clean fork
via flake.nix, NO upstream PR; #77/#78 optional/parked. Fork-protocol goal in force throughout;
one stream at a time; reviewer pass before every merge; V1 before every push.

## Execution checklist

- [x] Stream 1 / #220: land the heterogeneous multi-row ALU witness and close #220.
  - [x] Confirm #244 and #248 landed and #220 is open only for the multi-row criterion.
  - [x] Create `.worktrees/issue-220-multirow` from `origin/main` at `ffdae65c`.
  - [x] Spike and focused-build the general N-row register telescoping combinator.
  - [x] Generalize the BinaryAdd provider to row lists and migrate the singleton witnesses.
  - [x] Assemble the two-row BinaryAdd/Main tables via `ofRows` and balance the accepted trace.
  - [x] Bind the ADD/ADDI/JAL rows to Sail and apply `root_soundness`.
  - [x] Delete subsumed single-row special cases, verify, review, merge, and close #220.
- [x] Stream 2 / #245: split executed-step count from committed ROM length; verify, review, merge,
  and close #245.
  - Completed (2026-07-10): PR #250 is merged and #220 is closed; the isolated #245 worktree was
    bootstrapped from `origin/main`, with baseline `lake build` passing (9,040 jobs). The
    implementation keeps `AcceptedZiskTrace` execution-indexed with dependent committed-ROM
    `programLength`/`program` fields; all ROM/Main, boot-memory, and decode membership facts use
    that field, with no artificial ordering assumption between program and execution lengths.
    Degenerate, single-ADD, ADD-spin, and multi-row witnesses compile after migration. A concrete
    `AcceptedZiskTrace 1` / committed-ROM-length-2 ADD/JAL regression reuses the balanced real
    witness, reaches `root_soundness`, and proves the physical successor's JAL lookup is committed.
    Axiom hooks, baseline regeneration, focused/full Lake builds, V1/V2, production extraction,
    flake evaluation, and reviewer pass are green. Committed as `096c627`, merged as PR #252 at
    `af1c6f41`, and #245 is closed.
- [ ] Stream 3 / #249: burn down in-repo certificates, remove hand-pinned prev-step chains, verify,
  review, merge, and close #249. #225 is already closed; this landing must discharge its residual
  previous-step criterion without claiming to close it again.
  - In progress (2026-07-10): #245 is merged and closed. Static lookups can be composed directly
    into Main/Mem row constraints, but the segment `distance_base_*` values are unlinked
    `ProverData` sidecars. The plan is at a decision point: add a source-correlated sidecar/component
    model, or obtain owner-signed re-scope retaining `mem_replay_segment_ranges`; no unlinked range
    table is a valid derivation.
- [ ] Stream 4 / #243 and #226: pin the minimal Clean fork, derive cross-row Mem replay, verify the
  rebuilt pipeline, review, merge, and close both issues.
- [ ] Stream 5 / #242: extract MemAlignRom, prove the through-MemAlign timeline, verify, review,
  merge, and close #242.
- [ ] Final closeout: run final gates and residue searches; update trusted-base/README and all seven
  landed-work closing comments.

## End state (the checkable finish line)

#220, #225, #226, #242, #243, #245, #249 all CLOSED with landed Lean work (not bookkeeping);
`AcceptedZiskTrace` certificate fields reduced to: the original seven + whatever #242/#243/#249
cannot derive (each survivor named in trusted-base with a citation); all witnesses free of
hand-pinned prev-step chains; gates green on main; trusted-base and README reflect the end state.

## Stream order and rationale

Ordered to touch shared surfaces once: the parameter split (#245) early so later streams don't
re-churn witnesses; in-repo burn-down (#249) before the fork-based one (#243); the extraction-heavy
MemAlign work (#242) last, benefiting from everything prior.

### Stream 1 — finish #220: multi-row ALU (in flight; plan PLAN_L3_MULTIROW.md already ruled)
Spike the general N-row register telescoping combinator first; multi-row provider assembly via
`ofRows`; 3–4-instruction ALU + spin witness; subsumption rule (each general lemma deletes its
single-row special case in the same PR). Exit: #220 closes.

### Stream 2 — #245: split executed step count from committed ROM length
The surface change its issue body specifies: `AcceptedZiskTrace` (and `SailTrace`/`root_soundness`
plumbing) distinguish executed steps from `Program` length, so padded successor rows and realistic
programs (ROM longer than execution) are expressible without the spin-loop trick. Constraints from
the issue: preserve the root_soundness conclusion over executed steps; keep Main's per-row ROM
lookup over the full committed ROM; do NOT weaken `Decode_*` or the lookup to hide last-row
issues. Rebase/update the existing witnesses (degenerate, single-ADD, ADD-spin, Stream 1's) in the
same PR. This is a protected-surface stream: reviewer pass mandatory, binder baselines regenerated.
Exit: #245 closes.

### Stream 3 — #249: in-repo certificate burn-down (issue body has the full spec)
Derive and delete: `main_step_index_fixed` (fixed-column route, `segment_l1_fixed` precedent);
the within-row prev-step chain (removes hand-pins from all witnesses; closes #225's residual
criterion); `mem_replay_row/segment_ranges` (compose the static range tables from
`ZiskFv/AirsClean/RangeTables.lean` into the ensemble, as Binary/BinaryExtension already model
lookups). Any underivable survivor: named certificate + owner sign-off (decision request).
Exit: #249 closes; #225's already-closed residual criterion is met.

### Stream 4 — #243 via the fork: cross-row Mem package derived
1. Create the pinned Clean fork (github.com/codygunton or eth-act mirror) with the minimal patch
   letting one component carry channels + a transition; point `flake.nix` at it; `nix run
   .#populate`; note the fork in `nix/README.md` and `trusted-base.md` (build-input trust surface
   moves with flake.lock, as designed).
2. Give the composed Mem component a `Component.transition` carrying the generated cross-row
   constraints (the #163 Main-PC-handshake precedent); derive `mem_replay_constraints` from
   `constraints_hold`+`transitions_hold`; delete the field; update witnesses.
Exit: #243 closes; #226 closes annotated "resolved via pinned fork; upstream contribution
deferred per owner ruling".

### Stream 5 — #242: MemAlign-family read-soundness (the big one, last)
1. Extraction slice: MemAlignRom as a first-class extracted table (`tools/pil-extract` + wrapper +
   static-table modeling + populate). This is a *slice* of #108, scoped to MemAlignRom only —
   #108 itself stays open.
2. The through-MemAlign timeline argument: thread value agreement Main pull → MemAlignByte/
   ReadByte byte assembly → Mem-table aligned reads → accepted replay (consumes the residues
   enumerated in #242: `MemAlignLoadProviderRomValueFacts`, `MemAlignCoreLookupFacts`, branch
   pins), generalizing the #115 read-soundness endpoints beyond direct-Mem scope.
3. Budget TWO forks here (new-argument territory; both prerequisites are known-unknown-bearing).
Exit: #242 closes; the #115 scope amendment's deviation (1) is retired — read-soundness covers
all RV64IM memory accesses at single-segment scope.

## Dispositions (recorded during Stream 1, one comment each, pre-authorized)

#221/#222/#74/#184: remain open on the Tier 1 milestone, untouched. #108: remains open; Stream 5
notes its MemAlignRom slice on it. #77/#78: parked-optional per owner. Completeness (#182/#183/
#154), kernel purity (#75/#174), #172, hygiene (#116/#118/#127/#128/#186): untouched backlog.
#173: standing infra.

## Verification

Per stream: focused checks while iterating; V1 every push; V2 + `lake build` at stream landing;
`nix run .#test` before each merge; reviewer pass on every landing PR; `#print axioms` kernel-only
on new public theorems. Stream 4 additionally: full pipeline rebuild from the forked flake input
(populate + pilout cache still warm via cachix or rebuilt) before claiming green.
Final: all seven issues closed with landed-work closing comments; field-count reduction stated in
trusted-base; `git grep` shows no hand-pinned prev-step values in witness constructors.

## Relative sizing (no time estimates — ordering rationale only)

S1 and S2 are known-shape. S3 is moderate with one possible decision request. S4 carries
pipeline-rebuild risk (forked flake input). S5 is the largest and least certain (extraction slice
plus a genuinely new proof argument) — hence last, with two forks budgeted.

## Standing constraints

Anti-laundering per AGENTS.md; 0 project axioms; no escape hatches; one live branch per stream;
decision requests for any fork not pre-ruled here; STATUS.md + plan checklist current at every
checkpoint; the L-phase ledger in every report.
