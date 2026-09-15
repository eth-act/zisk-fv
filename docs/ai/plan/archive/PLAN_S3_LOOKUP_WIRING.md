# S3: Lookup-Wiring Extraction

**Status:** approved; PR 1 is awaiting review and PR 2a is approved to start
as a stacked capability PR. PR 2a does not change an accepted-trace field, a
HELD/legacy sidecar field, or a protocol-soundness application in an
accepted-trace bridge.

**Stream:** Project Closeout S3, in
`.worktrees/issue-249-certificate-burndown` on
`issue-249-range-provider-bridge`, stacked on PR 1
`issue-249-lookup-wiring-plan` at `608d16bb`.

**Objective:** extract the actual stage-2 lookup wiring and its cross-AIR
global-sum linkage, represent it as surrogate-channel emissions, and use the
existing lookup/permutation protocol-soundness class to derive the HELD
`mem_replay_segment_ranges` fact from balance.  Deleting that caller-supplied
promise hypothesis closes #249.  The same faithful route must also cover the
MULH/MULHSU indexed-range residue and complete the legacy Mem-sidecar
lifecycle audit.

## Boundaries

- S3 derives facts from selected-table data, live constraints, recognised
  wiring, and balance.  It does not introduce a project axiom, `sorry`,
  `native_decide`, an allowlist change, a weakened obligation, or a new
  caller-supplied promise hypothesis.
- A recognised wiring record is an extraction artefact, not a proof of the
  logUp/permutation argument.  The existing protocol-soundness class is the
  only trust class used for that latter step; S3 adds cited applications of it,
  not a new kind of trust.
- `Table.fromStatic` proves a table's data membership.  It cannot by itself
  prove that an unmodelled Mem sidecar was sent to that table.  The segment
  range route must therefore include the recognised channel and its balance;
  a detached static lookup would be anti-laundering.
- `MemAlignRom` is a virtual PIL AIR and is not a S3 proof target.  S3 makes
  the wiring/static-table route reusable by S4, which remains responsible for
  first-class virtual-table extraction under #108/#242.
- **Binding rider (owner-approved):** a hint is a search witness only.  Before
  any manifest tuple or surrogate emission is accepted, the generated
  constraint term must equal the standard template instantiated with that
  hint's tuple AST.  Hint content that lacks that equality is not emitted.  If
  the equality cannot be checked for Mem c24/c25/c26, stop with their complete
  rendered terms and hint payloads.

## Execution Checklist

- [x] Pre-S4 detour #268, Phase 1 (analysis only): investigate the historical
  `gsum_debug_data` stub and Arith c61/c62/c64 before attempting the Binary
  consumer route.  Disposition: the old F-only stub is already replaced by
  typed, kernel-linked Mem hints; c61 is a zero-tail-compressed
  proves-operation form; c62 adds the assumes-side `x - (0 - m)` spelling;
  and c64 is the cross-AIR global-sum finalizer.  All are benign and outside
  the present direct/two-hint templates, not a ZisK defect.  Exact extracted
  terms and citations: `docs/ai/notes/NOTE_268_LOOKUP_WIRING_DISPOSITIONS.md`.
  Decision gate: report this result before Phase 2; do not consume the old
  renderer or bypass a checked template link.
- [x] Pre-S4 detour #268, Phase 2 route audit (superseded by the approved
  mixed-template capability below): initially blocked without Lean changes.
  `BinaryExtension` messages 0--7 and Binary messages 0--6 have validated
  bus-table links, but Binary message 7 is the final `mode64` bus-125 lookup
  in `binary.pil:121-124`, retained only in unlinked mixed c10 with the
  operation-bus tuple. The manifest has no c10 hint/template/link. Do not
  synthesize it from the Clean row or consume unlinked c10; an
  owner-approved, kernel-checked mixed bus-125/bus-5000 c10 template and a
  policy for the absent hint are required before a finished-channel provider
  route can retire `bin_table_consumer_wf`. This is a recognizer-coverage
  blocker, not a ZisK defect. Evidence:
  `docs/ai/notes/NOTE_268_LOOKUP_WIRING_DISPOSITIONS.md`. No new caller
  premise, `ProverAssumptions` soundness use, canonical-binder change, defect
  carve-out, or upstream filing.
- [x] Pre-S4 detour #268, Phase 2 implementation: the owner approved
  one generic, exact `derivedMixed2` template for Binary c10 only. Its empty
  hint list is explicit provenance for the constraint-derived bus-125 and
  bus-5000 tuples, and the generated `constraint_Binary_10 =
  template_Binary_10` example closes by `rfl`. The live Binary cross-check
  binds the derived bus-125 tuple to `lookupMessage7`; Binary and
  BinaryExtension now have negative consumer components paired with exact
  static provider slices in local finished-channel ensembles. Full Lake,
  aggregate-root/Sail prerequisites, V1, V2, `nix run .#test`, and flake
  reproducibility are green; independent review approved with no blocker.
  Documentation cleanup was replayed unchanged as `4a3c403c`; after #266
  squash-merged to `main` as `31176427`, PR #270 was safely rebased to that
  base, force-pushed with a lease after V1 again passed 16/16, and retargeted
  to `main`. It retains `Closes #268` and the recorded trust-surface note.
  It subsequently merged as `28ed2773`; the issue-268 pre-S4 detour is
  complete.
- [x] Refresh generated artefacts with `nix run .#populate` and
  `lake exe cache get`.
- [x] Survey generated mixed constraints, hint rendering, the live Clean
  models, range tables, and pilout global-sum linkage.
- [x] Record the extractor limitation and the exact decision gate below.
- [ ] PR 1 (active): add the lossless lookup-wiring extraction spike and its
  tests; update extractor notes and add the row-zero-saturation warning.
  Checkpoint: the generated Lean consistency module is kernel-green for the
  discovered Mem c24-c32 and Arith c49-c60/c63 links. It retains raw tuple
  ASTs, then applies only neutral syntax normalization before the standard
  template `rfl` equality; no generator-side fallback is used. It also
  retains emitted-AIR unlinked constraints without hint payloads (including
  Mem c33) and reports non-emitted AIRs as absent. Regeneration and focused
  checks are green; V1, full Lake, V2, and `nix run .#test` are green. Commit
  `608d16b` is pushed as PR #259. GitHub currently reports no branch checks;
  owner review is pending. PR 2 preparation may proceed read-only only.
- [x] PR 2a (complete; PR #263 remains open): add the capability only: recognised surrogate range
  channel, `SpecifiedRanges` static provider backed by `RangeTables`, a
  source-linked selected-table expression bridge, generated-wiring main-Lake
  integration, and a concrete balanced-witness membership demonstration. No
  accepted-trace, HELD-field, or legacy-sidecar changes. Checkpoint: the
  provider, Mem consumer, bus-103 finishing order, and the 12-table
  `SingleAddWitness` (with empty range balance) are implemented; fresh
  focused verification is in progress after invalidating stale Lake
  artifacts. D2's
  table-resident raw cells plus the indexed transition bridge suffice; no
  Clean D3 patch is required. The inherited implementation was checkpointed
  unchanged as `975b58b1`; focused repair now starts with its raw-cell
  materialization reduction before rebuilding dependent witnesses. Fresh
  focused targets are green for it, `Mem.RangeWiring`, and the three migrated
  witnesses. The design needs no source change, but a true source build
  repaired stale-artifact-hidden local demo reductions in `Mem.RangeWiring`.
  **Owner ruling (2026-07-16):** the completeness issue was self-inflicted:
  the Mem consumer used typed `pull` plus `channelsWithGuarantees`; it has no
  local `fromStatic` lookup. Mirror Main's negative consumer emission and
  requirement channel, leaving `ProverAssumptions` unchanged. The provider's
  static lookup and finished-channel balance own membership. PR 2b must use
  accepted-witness constraints/balance, never `ProverAssumptions`, to derive
  segment facts. This is now implemented: the source consumer is `emit (-1)`
  with a requirement channel; `ProverAssumptions` is unchanged; bus 103 is
  finished after provider and consumer. `RangeWiring` binds all four checked
  links to materialized raw cells and canonical `ProverData` keys. The new
  two-table concrete witness is non-empty (`distance_base[0] = 7`), derives
  the matching static-provider counterpart from its actual balance, and then
  proves the 16-bit membership fact. Fresh focused source builds, the root
  import, and all three migrated witness targets are green. The implementation
  is committed as `47f577d` (`feat: bridge Mem range source to static provider`); V1
  (`trust/scripts/check-all.sh`) has passed, the branch is pushed, and PR 2a
  is open as #263 against PR #259. Before requesting merge, run full Lake and
  V2, `nix run .#test`, and independent review. PR 2b stays blocked on #259.
  The first full-Lake run exposed a canonical table-projection omission: its
  generated-transition equivalence dropped the new source-bridge conjunct.
  Follow-up commit `66774df` retains that conjunct; its focused target and
  the rerun full Lake build are green. V2, `nix run .#test`, and independent
  review remain before a merge request. V2's first invocation needs the root
  `ZiskFv.olean` that default full Lake does not produce, so build `ZiskFv`
  explicitly before the valid rerun. Independent review found and focused
  repairs now address the proof-carrying generated-link/raw-cell/key binding
  and the acceptance theorem's provider-requirement use; rerun all landing
  gates after follow-up commit `cd8291a`. The output-filtered Lake invocations
  proved to be partial progress rather than completed gates: the real terminal
  build exposed a stale eleven-table MemBus flatMap in `AddAddiSpinWitness`
  that omitted the newly empty `SpecifiedRangesSlice` table and timed out
  attempting to unify the wrong list. It is repaired as a twelve-table
  reduction and the focused target is green. The real terminal full Lake
  build is now green (9,053 jobs, including root `ZiskFv.olean`) and V2 has
  passed all 16 semantic checks. `nix run .#test` passed all eight stages,
  including its embedded V1/V2 and flake-repro check; standalone V1 has also
  passed all 16 checks. Final review then identified that the generated-hint
  list and raw/key bridge still needed a single proof-carrying binding. The
  repair binds each generated Mem constraint index and exact AirValue slot AST
  (11–14) to the raw cell and canonical key; focused RangeWiring and
  acceptance-witness builds pass. Independent review approves the repair with
  no remaining finding and the final terminal full Lake build is green. Rerun
  V2 and Nix before pushing the repairs and requesting merge. Final V2 passed
  all 16 checks, final Nix tests passed all eight stages, and final standalone
  V1 passed all 16 checks. The narrow repair commits are `fecb790`, `4167ba0`,
  and `0d58075`; they are pushed and #263 now records final Lake, V1, V2,
  Nix, and independent-review approval. It stays open without merge or rebase.
- [x] PR 2b (open as #265, stacked on PR #263): use the checked PR 2a capability to
  derive and delete `mem_replay_segment_ranges`, update `trusted-base.md`, and
  close #249 on eventual merge. The derivation is restricted to accepted-witness
  constraints, transitions, and finished bus-103 balance—not
  `ProverAssumptions`; it contains no ensemble/provider/expression-bridge shape work.
  Checkpoint: `memReplaySegmentRanges` now derives both `distance_base` chunks
  from the D2 indexed transition source bridge, bus-103 balance, and the static
  `SpecifiedRangesSlice` provider; the accepted-trace field and every known
  constructor occurrence are deleted. The coherent deletion is committed as
  `7193fa5`; focused acceptance/provider/witness and root Lake builds are
  green, independent review approved with no blocker, V1 and V2 passed all 16
  checks, and `nix run .#test` passed all eight stages. Its PR body restates
  the completeness-only trust boundary. Stop for owner sequencing.
- [x] PR 3 (complete; PR #266 remains open, stacked on #265): lifecycle audit found the five legacy
  fields only in `AcceptedZiskTrace` and four vacuous constructor populations;
  no live consumer exists. Commit `8294942` deletes the fields and all five
  vacuous populations; focused accepted-trace/witness + degenerate-fixture
  builds are green. The Arith provider's existing
  in-component `fromStatic` lookup is selected for plain row cells. The new
  MULH/MULHSU balance-provider and construction layers derive shared Arith
  facts from provider `FullSpec`, without new caller premises and while
  preserving c46's separate source citation. Focused targets and the aggregate
  root build are green; standalone V1 passed all 16 checks before the first
  push. Commits `8294942` and `f48202c` are pushed on
  `issue-249-arith-lookup-completion`, stacked on #265. The required full
  Lake build is green (9,057 jobs), and V2 passed all 16 checks with unchanged
  canonical binders and axiom-closure baselines. `nix run .#test` passed all
  eight stages, including its embedded V1/V2 and flake-repro checks.
  Independent review found one stale trusted-base constructor note that named
  the deleted legacy sidecars. Commit `4cd87d7` corrects it and standalone V1
  again passed all 16 checks; final review approved the current head with no
  remaining finding. PR #266 is open based on #265; its body records the
  trusted route and final verification. The stack remains open.

## Surveyed Facts

### Extraction contract

`tools/pil-extract/src/main.rs` now emits a challenge-mixed *constraint* in
the single-field specialisation `Circuit F F C`; it does not skip-stub that
constraint.  Its comment at `main.rs:619-624` is explicit about this.  The
separate `render_hint_operand` path (`main.rs:948-955`) still substitutes `0`
for any hint operand transitively containing `Challenge`, `AirValue`, or
`AirGroupValue`, because `BusEmissionSpec.value` is `F`-typed.  Thus “stubbed”
below means **hint-slot stubbed**, not omitted mixed constraint.

`bus-emissions` defaults to bus 5000.  `--bus-id 0` exposes all hints for one
AIR, but the checked-in generated `Extraction/Buses.lean` presently contains
only the operation-bus subset.  `clean-component` deliberately omits the
stage-2 accumulator columns and mixed constraints, replacing only its one
supported interaction kind (operation or memory bus) with a Clean channel
push.  It has no generic range, ROM, virtual-table, or cross-AIR-gsum emitter.
`docs/extraction/extractor-notes.md` still describes the older mixed-constraint
skip/stub behaviour and must be reconciled with the current source in PR 1.

### Constraint-family table

The “shape” column classifies the generated source, not the PIL protocol.
Every standard `std_sum` family retains its debug comment, but the Lean term is
already algebraically expanded.  A raw text matcher for
`im * mix(tuple) + sel = 0` is therefore not a sound implementation plan.

| AIR family | Constraint artefact | Hint/wiring artefact | Render shape and recogniser feasibility |
|---|---|---|---|
| `Main` | Emitted in `Extraction/Main.lean` with mixed constraints. | Current operation-bus hints are F-typed and emitted. | `std_sum` expansion with preserved debug lines; structural-hint route is feasible, raw expression matching is not the primary route. |
| `Mem` | Emitted: constraints 24–33 are `std_sum.pil:590`, `:599`, `:656`, `:696`. | Range/direct segment sidecar slots are stubbed to `0`; see exact target below. | Not a direct `im * mix + sel` rendering: clusters, recurrence, direct inverses, and final gsum aggregation are distinct shapes.  Feasible only through a lossless hint plus constraint-link manifest. |
| `MemAlign` | Emitted with its mixed `std_sum` constraints. | No general range/ROM wiring artifact; its virtual ROM is absent. | Same expanded standard family.  Reusable recogniser target, but no S3 MemAlignRom discharge. |
| `MemAlignByte` | Emitted with mixed constraints. | Existing Clean memory-bus push covers only its supported bus shape. | Expanded standard family; structural hint route feasible. |
| `MemAlignReadByte` | Emitted with mixed constraints. | Existing local static byte lookup is F-only; no stage-2 generic wiring. | Expanded standard family; structural hint route feasible. |
| `MemAlignWriteByte` | Emitted with mixed constraints. | Existing Clean memory-bus push covers only its supported bus shape. | Expanded standard family; structural hint route feasible. |
| `Arith` | Emitted: c49–64 are mixed; c46 (`arith.pil:262`) is F-only and emitted separately. | `--bus-id 0` renders the range hints (bus 330) and Arith-table hint (331) as F expressions, but no checked-in all-bus generated module exists. | Standard cluster/recurrence/direct forms are expanded.  The range tuples are structurally available; link them to c49–64 rather than parse those terms. |
| `Binary` | Emitted with mixed constraints. | Operation-bus hint is emitted. | Expanded standard family; structural hint route feasible. |
| `BinaryAdd` | Emitted with mixed constraints. | Operation-bus hint is emitted. | Expanded standard family; structural hint route feasible. |
| `BinaryExtension` | Emitted with mixed constraints. | Operation-bus hint is emitted. | Expanded standard family; structural hint route feasible. |
| `Dma*` (12 AIRs), `Rom`, `RomData`, `InputData`, `Add256`, `ArithEq`, `ArithEq384`, `Keccakf`, `Sha256f`, `Poseidon2`, `Blake2br`, `SpecifiedRanges`, `VirtualTable0`, `VirtualTable1` | Absent from `build/extraction/Extraction/`; no generated mixed-constraint classification is available. | Absent from the generated wiring surface. | Out of S3's proof scope.  PR 1 must make the manifest enumerator report these as absent rather than silently treating absence as “no lookup”. |

The current pilout has 35 AIRs.  The ten generated files above are the full
current mixed-constraint artefact set.  “Absent” does not assert that the PIL
AIR has no lookup; it asserts that the current extractor did not emit an
artefact from which S3 can safely recognise one.

### Mem: held range target and global-sum wiring

`MemAirFacts.md` gives the exact mutable-Mem target:

- Hints 884, 886, 888, and 890 are `Range Check` assumes-side bus-103
  lookups for `distance_base[0]`, `distance_base[1]`, `distance_end[0]`, and
  `distance_end[1]`.  The two `distance_base` entries are the held
  `MemSegmentGeneratedRangeFacts.distanceBaseChunks` source
  (`mem.pil:267-268`); the matching end values are at `mem.pil:285-286`.
  Current hint rendering gives each target value `0` because it is an
  `AirValue`.
- Hints 895 and 897 (`l_increment` and `h_increment`) and 900 (the
  `sel_dual`-gated delta) are ordinary F-valued range hints.  S1a already
  composed their `mem.pil:384-385,397` equivalents into live `Mem` with
  `Table.fromStatic` and deleted `mem_replay_row_ranges`.
- `Mem.constraint_24_every_row` and `constraint_25_every_row` are the two
  cluster product equations.  For example, c24's preserved source is
  `std_sum.pil:590 (im_cluster*(((Zisk.gsum_e[5])+std_gamma)*((Zisk.gsum_e[6])+std_gamma)))-((-1*((Zisk.gsum_e[6])+std_gamma))+((Zisk.gsum_s[6])*((Zisk.gsum_e[5])+std_gamma)))`.
  c26 is the accumulator recurrence at `std_sum.pil:599`; c27–32 are six
  direct inverse equations at `std_sum.pil:656`; c33 is the final link
  `std_sum.pil:696 __L1__'*((Zisk.gsum_result-gsum)-sum(im_direct))`.
- c33 renders `Zisk.gsum_result` and the direct columns as `Circuit.exposed`.
  This is where the per-AIR accumulator reaches the cross-AIR aggregate.  No
  separate generated global-sum module exists; the extractor must emit the
  exposed-slot/global-result mapping with the per-AIR family rather than leave
  it implicit.

### Range and existing Clean routes

`ZiskFv/AirsClean/RangeTables.lean` constructively defines the scalar tables
`rangeTable1/4/7/8/16/17/22/24/29/32/40` and the 2-column
`arithRangeTable`.  The live `Mem` component already has
`distanceBaseRangeLookups` using `Table.fromStatic rangeTable16`, but its
arguments are arbitrary expressions; it is not connected to the sidecar
range-check channel and therefore does not discharge the held fact.

`ArithMul` and `ArithDiv` already compose row-local Arith-table, chunk,
carry, and indexed static lookups.  `ArithMul.Circuit` consumes c46 directly
from `arith.pil:262`; `ArithMul.Bridge.full_spec_of_carry_chain_and_arith_table`
still takes `h_table`, `h_c46`, `h_chunk_ranges`, `h_carry_ranges`, and
`h_indexed_ranges` explicitly because the global lookup wiring is absent.
The S3 target is to source those shared lookup facts from recognised channels
and balance, never to add them as per-opcode caller promises.

`MemAlignRom` is declared as `virtual MemAlignRom()` in `zisk/pil/zisk.pil:110`
and has no matching current pilout AIR or `Extraction/MemAlignRom.lean`.
Current MemAlign bridges explicitly carry the ROM residue.  S4 can reuse
S3's manifest and static-range composition, but S3 must not pretend that the
virtual table has been extracted.

## Design Proposal

### Lossless wiring manifest and recogniser

PR 1 should add a generated, typed `LookupWiring` artefact rather than extend
the F-only `BusEmissionSpec` with another lossy escape hatch.  Each entry must
retain:

1. AIR/group/index; hint id; PIOP; assumes/proves side; bus id; multiplicity
   AST; ordered slot ASTs; and the original slot names.
2. The expression field type at every leaf (`F`, challenge, `AirValue`, or
   `AirGroupValue`) without substituting `0`.
3. Links to the exact accumulator constraint indices and preserved PIL debug
   lines, including the `std_sum.pil:696` global-result/exposed-slot link.
4. An explicit `absent` result for every AIR omitted by the current generator.

The recogniser consumes this manifest, not an algebraically normalised Lean
term.  It recognises a protocol family only when the structured hint tuple and
the linked cluster/recurrence/direct/final constraint set match a verified
standard template.  It then emits a surrogate channel message containing the
tuple, multiplicity, lookup id, PIOP side, and provenance.  The exact macro
template may be normalised internally, but it must be validated against the
linked extracted constraints; no theorem may infer a lookup tuple merely from
an inverse equation.

This is deliberately narrower than the metaplan's shorthand
`im * mix(tuple) + sel = 0`: that form describes the protocol family, while
the actual Mem cluster c24/c25 and recurrence c26 do not render in that simple
surface form.  The retained Horner AST supplies the ordered
`alpha`/`gamma` compression witness without reverse-engineering expanded
arithmetic.  A new top-level recognition definition is data-only and should
be marked `@[reducible]` unless review establishes that it cannot hide a
promise.

#### Binding acceptance test

For every recognised entry, the extractor must first construct the standard
template from the hint's typed tuple AST, selectors, accumulator columns,
challenge references, and global/exposed inputs.  It must then check equality
against the linked extracted constraint expression.  The linked constraint is
the binding authority; the hint merely locates the candidate tuple.  A
successful manifest entry records the constraint id and validation method;
there is no “unvalidated hint” variant available to a surrogate emitter.

PR 1 prefers a generated Lean consistency module whose definitions reuse the
same expression renderer as the generated constraint module and close the
instantiation equality with `rfl` (or a kernel-checked `decide` where the
expression representation is decidable).  The spike must measure this for
Mem and Arith.  Only if generated Lean equality is demonstrably too expensive
may the extractor run the comparison itself; that fallback must name the exact
normalisation/comparison in `docs/extraction/extractor-notes.md`, emit its
input/output provenance, and retain the same no-emission-on-failure rule.

### Protocol-soundness citations

The surrogate channel only names the relationship extracted from pilout.  The
step from balanced surrogate channels to membership/lookup facts uses the
existing lookup/permutation protocol-soundness class documented by the current
operation- and memory-bus bridges; it must not claim that field equalities
alone prove logUp soundness.

For every new application, `trust/trusted-base.md` will list: the AIR, hint
id, side, bus id, generated manifest entry, accumulator constraint ids, and
PIL source line(s).  The first required citation is Mem range hints
884/886/888/890 plus `mem.pil:267-268` (and the corresponding end citations);
the linked accumulator sources are c24–33 at `std_sum.pil:590/599/656/696`.
Arith will cite its range/Arith-table hint ids and linked c49–64, while c46
keeps its separate `arith.pil:262` citation.  This expands the documented
application inventory, not the trust taxonomy.

### Range-table composition

The recogniser will map a range wiring entry to a typed surrogate range
channel `(range-id, value, multiplicity, provenance)`.  A small
`SpecifiedRanges` slice maps recognised range ids 102/103/104 and the Arith
range ids to the constructive `RangeTables` static tables.  The component
route then has two parts:

1. For row inputs, keep S1a's local pattern: the live component emits
   `lookup (Table.fromStatic table) value`, and component soundness projects
   the range fact.
2. For Mem segment sidecars, use the recognised assumes-side range message and
   full-ensemble balance to select the matching static provider row.  Then use
   `Table.fromStatic rangeTable16` membership to prove the selected
   `distance_base_*` bounds.  The source expression must be the selected
   table's canonical ProverData/fixed-schema view, not an
   `AcceptedZiskTrace` field or a detached `SegmentColumns` argument.

The same bridge supplies Arith's selected lookup facts.  It leaves the
existing c46 local assertion intact, while deriving the currently explicit
lookup/range premises from the recognised channel and static table.

## Deletion Order

1. Land the lossless manifest spike and prove the Mem range entry links to
   the extracted constraints and selected source.  No accepted-trace field is
   touched in this PR.
2. Compose the Mem range channel through balance, derive
   `MemSegmentGeneratedRangeFacts`, delete `mem_replay_segment_ranges` from
   `AcceptedZiskTrace` and every constructor, and update `trusted-base.md`.
   This is the #249 close condition.
3. Audit the five unconsumed legacy fields
   `mem_replay_segment`, `mem_replay_permutation`, `mem_replay_gsum`,
   `mem_replay_im0`, and `mem_replay_im1`.  The expected result is deletion:
   their data remains only as selected-table internal ProverData needed by the
   recognised family, never as accepted-trace fields.  The audit must show no
   remaining consumer before deletion; if a real consumer remains, name it
   and request a decision rather than retaining a field indefinitely.
4. Use the same recognised static range route to discharge the remaining
   MULH/MULHSU indexed-range/Arith-table premise path.  This includes the
   global source of the lookup facts, not a second local copy of c46 or the
   already-constructed static table.

## PR Decomposition and Verification

**PR 1 -- extractor spike and provenance.** Add the lossless manifest,
per-AIR absence reporting, template-link tests for Mem and Arith, and a source
regeneration test proving that no ExtF operand becomes `0` in the new output.
Its required acceptance test instantiates each standard template with the
candidate hint tuple and proves/checks equality to the linked generated
constraint; a hint alone cannot populate a manifest or surrogate emission.
Prefer a generated Lean `rfl`/`decide` consistency module.  A demonstrated
performance fallback may be generator-side only when extractor notes identify
the exact check and generated provenance.
Synchronise `docs/extraction/extractor-notes.md`.  Add the one-line warning to
`docs/clean-fork-divergences.md` that Lean's `row - 1` saturates at row zero
and each imported PIL negative rotation must carry its row-zero gate.  This PR
does not add a new protocol application or remove a field.

**PR 2a -- range capability and witness-shape bridge.** Compose the recognised
surrogate range channel and a `SpecifiedRanges`-slice static provider backed
by `RangeTables` into the full ensemble. Build a source-linked expression
bridge so a recognised emission carries selected-table values resident in
`ProverData`; first evaluate a table-resident representation under D2 before
any Clean change. Bring the generated wiring modules into the main Lake build
and demonstrate one `ProverData`-sourced value pushed on the recognised range
channel, balanced against the static provider in a concrete witness, with the
provider counterpart and membership fact derived from that actual balance.
This PR pays all ensemble and witness shape churn; it changes neither
`AcceptedZiskTrace` nor a HELD/legacy sidecar field.

**PR 2b -- Mem range derivation and deletion.** Stacked on PR #263, use only
the landed PR 2a capability to derive the canonical selected-table segment
ranges, delete `mem_replay_segment_ranges`, update its trusted-base row from a
HELD caller-supplied promise hypothesis to a derived fact, and close #249.
No provider, expression-bridge, or ensemble/witness shape work belongs here.

### PR 2a Ruling and Feasibility Gate (2026-07-16)

**Verified facts.** `FullEnsemble` contains and balances only the operation
and memory channels. `SpecifiedRanges` is an explicit absent-AIR result in
`LookupWiring`; it has no extracted constraint family, live Clean component,
or range channel/provider in the ensemble. `RawChannel.Consistent` is the
existing derived Clean protocol-soundness facility, but it applies only after
both interaction sides participate in that balanced ensemble. A
`Table.fromStatic` lookup alone proves static membership; it cannot establish
that the live Mem sidecar value was sent to that table.

Mem c29/c30 have kernel-checked template links to the `distance_base_*` hint
ASTs, but the linked terms are direct inverse equations rather than range
membership. `Extraction.LookupWiring` and `MemGeneratedConstraintBridge` are
generated modules outside the main Lake dependency graph. Moreover, the Clean
expression language has no `ProverData` term, while the selected Mem segment
reads `distance_base_*` from shared `ProverData`. No maintained path currently
connects those linked AirValues to a live range interaction. PIOP sign
orientation and c33's global-sum relationship must also be validated against
the actual provider before a balance claim can be made.

**Owner ruling.** The source-linked provider/expression bridge spike is
approved as PR 2a. It must materialise Mem AirValues as expressions tied to
selected-table data, source-link the needed `SpecifiedRanges` provider rows
and range interactions, validate PIOP sign and c33/global-sum wiring, and
then compose both actual sides through finished-channel balance and the
provider's static requirements.
Try the smaller table-resident route under D2 first. If a Clean extension is
needed, it is a third minimal upstream-shaped fork facility documented as D3
in `docs/clean-fork-divergences.md`; stop and report concrete design options
before making a large or invasive patch. A hand-written static provider, a
detached `Table.fromStatic` lookup, or a new caller-supplied promise hypothesis
is not an acceptable substitute. #249 remains open. PR 2b is blocked until
PR #259 merges.

**PR 3 -- lifecycle and Arith completion.** Remove the five legacy
accepted-trace sidecar fields after the consumer audit and source the
MULH/MULHSU shared lookup/range facts from the same recognised wiring.  Keep
the F-only c46 source and its citation separate from the challenge-mixed
family.  A failure to delete a field or source a premise is a decision request,
not a scope reduction.

Iterate with focused extractor/Lean targets.  Before each push run
`trust/scripts/check-all.sh`; at each landing run the pinned full `lake build`,
`trust/scripts/check-all-semantic.sh`, required baseline regeneration, and
`nix run .#test`.  Review the staged diff for the anti-laundering principle:
the accepted-trace trust surface must shrink, and no new caller-supplied
promise hypothesis may appear.

## Risks and Decision Gates

| Risk | Evidence | Required response |
|---|---|---|
| Raw constraint matching is over-strong or incomplete. | Mem c24 is `im_cluster * (m5 + gamma) * (m6 + gamma) - (...) = 0`, not the simple recogniser surface; c26 also contains the prior accumulator. | Use the structural hint and template link.  If the link cannot be checked, stop with the complete rendered c24/c25/c26 text and hint payload; do not infer a tuple from normalised algebra. |
| Hint data becomes an unpinned source of truth. | `gsum_debug_data` is metadata and the current hint renderer is lossy. | Require the instantiated-template equality before manifest emission.  A failed or absent equality emits nothing and is a decision request, never a fallback tuple. |
| ExtF data is silently erased. | `render_hint_operand` currently returns `0` for challenge/AirValue/AirGroupValue; Mem's held `distance_base_*` hints are affected. | The spike must preserve typed ASTs and reject a stubbed target.  Any design that keeps `BusEmissionSpec` as the sole source is a no-go. |
| Cross-AIR balance is unbound. | `std_sum.pil:696` maps each AIR's final accumulator to `Zisk.gsum_result` through exposed slots, but there is no generated global module. | Emit and test the exposed/global mapping before applying protocol soundness; otherwise request a decision with the extracted c33-equivalent text. |
| A virtual table is mistaken for an extracted AIR. | `MemAlignRom` is virtual and absent from the pilout extraction. | Keep it absent in S3 and schedule first-class static data extraction in S4/#108. |
| Existing Arith local soundness is mistaken for global lookup fidelity. | c46 and local `Table.fromStatic` operations exist, while `full_spec_of_carry_chain_and_arith_table` still takes shared lookup/range premises. | S3 must source those shared facts through recognised balance or report the exact remaining premise; no per-opcode binder may be added. |
| Row-zero rotation changes a copied recurrence. | Generated c26 uses `row - 1`; Lean saturates subtraction at zero. | PR 1 documents the gate.  Any new recurrence bridge must prove the PIL selector/fixed-column row-zero guard rather than rely on informal indexing. |

## Planning Checkpoint

**Surveyed facts:** generated mixed constraints now exist for ten AIRs;
ExtF-tainted wiring hints are still lossy; Mem's held range target is exactly
hints 884/886 with `mem.pil:267-268`; global aggregation is carried by the
`std_sum.pil:696` exposed result link; and MemAlignRom is absent because it is
virtual.

**Design proposal:** a lossless typed wiring manifest plus a template-linked
recogniser, surrogate channels, static-table composition, and cited use of the
existing protocol-soundness class.

**Open decision gate:** no raw generated Mem constraint currently has the
metaplan's simple textual recogniser shape.  PR 1 must demonstrate a verified
structural hint-to-constraint template link.  If it cannot, stop with the
concrete c24/c25/c26 render and hint payload for owner direction; do not
silently substitute a weaker or caller-provided route.

**Owner riders recorded (2026-07-15):** template-link equality is PR 1's
acceptance test and binds every emitted tuple to its linked constraint; hint
data is search-only.  Generated Lean `rfl`/`decide` consistency is preferred.
Generator-side validation is permitted only on a demonstrated Lean-cost
failure and must be documented with its exact check in extractor notes.
