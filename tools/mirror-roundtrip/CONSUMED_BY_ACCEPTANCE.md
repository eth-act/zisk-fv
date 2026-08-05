# Is a #304 mirror consumed by acceptance, or fidelity-only?

Issue: eth-act/zisk-fv#304 follow-up (verification-hole track). Companion to
`tools/mirror-roundtrip/README.md`. Reproduced by:

```bash
python3 tools/mirror-roundtrip/consumed_check.py          # this report's data, regenerated
python3 tools/mirror-roundtrip/consumed_check.py --json PATH.json
```

Python 3 standard library only; no Lean build, no network; nothing under `ZiskFv/`
is read as anything other than text and nothing under it is written.

## Correction (#304 review): the resolver was not actually strict

An earlier version of this report claimed **36 CONSUMED / 10 FIDELITY-ONLY**,
with "all 46 classified findings resolve identically under both [the strict and
the loose] pass." That "strict" pass was not, in fact, namespace-strict:
`resolve()`'s first step did an unqualified `idx.suffix_map.get(token)` lookup,
and `suffix_map` held every dotted suffix of every declaration's fully-qualified
name — including the bare last segment — for every declaration in the tree.
Concretely, a bare reference like `Spec`, read anywhere in the reachability
closure, matched **all** declarations named `Spec` regardless of namespace (at
the time of writing, ~10 of them, one per AIR), and this unqualified match ran
*before* any namespace-aware resolution, so the "strict" pass was already this
over-broad — the review's exact diagnosis.

`consumed_check.py`'s `resolve()` is now namespace-strict: every step is an
**exact** `fqn_map` lookup of a fully-constructed candidate name (the token
itself if fully qualified; the token prefixed by the reading declaration's own
namespace or an ancestor of it, longest first; an `open X (token)` alias; a
blanket `open X` namespace) — never a suffix match against unrelated
namespaces. A bare token that names nothing in scope this way is UNRESOLVED,
which is the safe direction for this tool: it can make a mirror look more
FIDELITY-ONLY than it is, never more CONSUMED. `suffix_map` and the `suffixes()`
helper are gone; a `_selfcheck()` runs on every invocation and asserts that a
bare `Spec` read inside `ZiskFv/AirsClean/Mem/Circuit.lean` resolves to exactly
`ZiskFv.AirsClean.Mem.Spec`, not the other ~9 unrelated `Spec`s.

**Measured impact.** Forward-reachability from the same 9 root files/44
declarations dropped from 1082 to 805 (of 8690 declarations now indexed,
tree drift since the original report) — a real, ~26% reduction, confirming the
old pass was over-reaching by a wide margin in the *general* graph. Against the
46 classified findings specifically, exactly **one** verdict flips: Arith's
`ArithDiv/Spec.lean:FullSpec` was wrongly CONSUMED and is now correctly
FIDELITY-ONLY (concrete mechanism: `ArithMul/Circuit.lean` genuinely references
its own bare `FullSpec`, i.e. `ZiskFv.AirsClean.ArithMul.FullSpec`; the old
resolver's unqualified suffix match let that single reference also mark the
unrelated `ZiskFv.AirsClean.ArithDiv.FullSpec` reachable, purely because both
share the bare last segment `FullSpec`). Corrected headline: **35 CONSUMED / 11
FIDELITY-ONLY**, 0 loose-only, 0 not-located — see "Headline numbers" below.

The qualitative conclusion does **not** flip wholesale: most of this report's 46
classified findings were already resolved through an unqualified reference
within the SAME namespace as the target (e.g. `Main/Circuit.lean`'s `Spec :=
fun row _ _ => Spec row.core`, read inside `ZiskFv.AirsClean.Main`, resolving to
`ZiskFv.AirsClean.Main.Spec`), which the buggy resolver also got right, just for
the wrong (unqualified) reason. The bug's damage was concentrated in the wider,
unclassified reachability graph (the 1082 → 805 swing) and in the one
classified finding that happened to collide on a shared bare segment. That is a
real correction, not a rounding error, and every number in this report below is
regenerated from the fixed resolver — but it is not the "massively different"
outcome a first read of the bug report might suggest. See "Method" and "Method
limitations" below for what the fix actually changed.

## The question

`check_mirrors.py` (#304/#305) welds a handwritten mirror predicate to the
generated constraint it canonically restates: an `Iff.rfl`-checked polynomial
equality. That is a **fidelity** fact — the mirror says the same thing the
generated constraint says. It is not a **consumption** fact: `Iff.rfl` typechecks
identically whether or not the mirror's own name is mentioned by anything else in
the build. `ZiskFv/AirsClean/MemMirrorWeld.lean`'s `ExtractedMemTrace` is the
standing example — matched perfectly against 34 generated Mem constraints, and
referenced by nothing but that one weld file.

This asks the other question: is the mirror predicate itself reachable, by a
forward reference walk, from the two declarations that jointly say what an
**accepted** ZisK trace is —

* `ZiskFv.Compliance.AcceptedZiskTrace` — `ZiskFv/Compliance/AcceptedZiskTrace.lean`
  plus its own `ZiskFv/Compliance/AcceptedZiskTrace/*.lean` companion files
  (`MainTable.lean`, `MemAlignRanges.lean`, `MemAlignRom.lean`, `MemProviders.lean`,
  `MemSegmentRanges.lean`, `MemTable.lean`, `Spec.lean`) — the companions import the
  base file and derive further certificates about what "accepted" implies, notably
  `AcceptedZiskTrace.spec_holds` (`Spec.lean`), which is how a table's `Spec` field
  (where a mirror typically lives) enters the picture even though it is not a raw
  struct field of `AcceptedZiskTrace`;
* `ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble`, declared alongside
  `fullRv64imSoundEnsemble` and `witness_spec_of_constraints` in
  `ZiskFv/AirsClean/FullEnsemble.lean`.

Nine files, 44 top-level declarations, are the roots. Everything a mirror needs to
reach to be **CONSUMED** is one of those 44 declarations, or something forward-
reachable from them.

## Why `AcceptedZiskTrace`'s fields alone are not enough context

`AcceptedZiskTrace`'s four constraint-shaped fields —

```
constraints_hold                    : witness.Constraints
channels_balanced                   : witness.BalancedChannels
transitions_hold                    : witness.TransitionConstraints
cyclic_successor_transitions_hold   : witness.CyclicSuccessorTransitionConstraints
```

— are stated against `Air.Flat.Table`/`Ensemble` definitions in Clean
(`build/clean-lean/Clean/Air/{FlatComponent,FlatEnsemble}.lean`), not against
anything in `ZiskFv/`. `Table.Constraints table := ∀ row ∈ table.table,
table.component.operations.ConstraintsHold (table.environment row)` — this is the
`assertZero` sequence each AIR's `circuit.main` actually emits, i.e. `Constraints`
IS the trace's checked polynomial gates. `Table.Spec`/`Component.Spec` is a
*different* field of the same `GeneralFormalCircuit` — `component.circuit.Spec` —
and is where a `Valid_<AIR>`/`Spec`-style mirror predicate can be wired in as the
circuit's semantic postcondition. `AcceptedZiskTrace` does not carry `witness.Spec`
as a field at all; it is **derived**, not assumed:

```lean
-- ZiskFv/Compliance/AcceptedZiskTrace/Spec.lean
@[reducible] def AcceptedZiskTrace.spec_holds (trace : AcceptedZiskTrace n) : trace.witness.Spec :=
  ZiskFv.AirsClean.FullEnsemble.witness_spec_of_constraints
    trace.witness trace.constraints_hold trace.channels_balanced
```

So a mirror can be part of what "accepted" implies through either of two routes,
both counted here: it is literally in an AIR's `circuit.main` assertion list (feeds
`Constraints` directly — the strongest form), or it is (part of) an AIR's
`circuit.Spec` field (feeds `witness.Spec`, reachable via `spec_holds`). Verified
directly for `Mem`:

```lean
-- ZiskFv/AirsClean/Mem/Circuit.lean:77 (componentWithDualMemBus's circuit)
Spec := fun row _ _ => Spec row      -- `Spec` here is ZiskFv.AirsClean.Mem.Spec
```

## Method

A textual, name-based forward-reachability graph, not an elaborated call graph
(building one would need Lean itself). `tools/mirror-roundtrip/consumed_check.py`:

1. Parses every `.lean` file under `ZiskFv/` into top-level declarations (reusing
   `survey.declarations`'s boundary rule: a line starting a keyword in
   `survey.DECL_KEYWORDS`, behind optional attributes/`open ... in`/privacy
   modifiers, runs to the next such start). Separately, in the same linear pass,
   tracks the `namespace`/`section`/`end` stack and the `open X` / `open X (a b
   c)` directives active at each point, so each declaration gets a best-effort
   fully-qualified name and an alias table.
2. Seeds a worklist with the 44 declarations physically in the 9 root files.
3. Pops a declaration, tokenizes its body, resolves each token the way Lean
   itself would resolve it: a fully-qualified token is an **exact** top-level
   name; a relative token is resolved by prefixing it with the reading
   declaration's own namespace or an ancestor of it (longest first) and doing an
   exact lookup, then by the file's explicit `open X (token)` aliases, then by a
   blanket `open X` namespace — and adds every newly-reached declaration to the
   worklist. A bare token naming nothing reachable this way is UNRESOLVED, never
   a match against "every declaration ending in that segment" (see the
   correction above). A declaration is **CONSUMED** iff it ends up in the
   visited set.
4. A separate, looser pass additionally falls back to an ambiguous bare-name match
   (the same approximation `survey.reference_counts` already uses for "unreachable
   mirror") when the precise resolution finds nothing, purely to flag cases the
   precise walk might have missed through a resolution gap. At the current tree
   it changes no verdict among the 46 classified findings (0 "loose-only"
   reclassifications) — meaningfully so now that the strict pass is actually
   strict; under the pre-fix resolver this same "0" was not informative, since
   the strict pass it was being compared against was already over-matching in
   the same direction as the loose one.

This shares `survey.reference_counts`'s soundness property and its limit: a
**positive** reachability claim is only as good as the textual resolution that
produced it (two same-named declarations in unrelated namespaces could in
principle be confused if one is genuinely in scope of the other, e.g. via a
wildcard `open`); a **negative** one — nothing in the closure names this
declaration, under either resolution pass — is conclusive in the direction that
matters for a FIDELITY-ONLY verdict. Every FIDELITY-ONLY finding below was
additionally checked by direct source reading (not just the mechanical pass); see
"Verified, not just mechanical" below.

## Scope classified

* every `survey.CLASSIFICATION` entry whose class is a mirror class
  (`survey.MIRROR_CLASSES`) — 40 entries, the #304 inventory itself;
* `survey.DELEGATED` — 1 entry, an out-of-root mirror a root mirror reaches
  (`ZiskFv.Airs.Mem.segmentResidualEveryRow`);
* 5 additional pre-Clean `ZiskFv/Airs/Mem.lean` declarations the #304
  `MemMirrorWeld.lean` docstring names by hand (`Valid_Mem`, `segment_every_row`,
  `permutation_every_row`, `core_every_row`, plus `segmentResidualEveryRow` again
  under its own name) — outside `survey.CLASSIFICATION`'s own scope
  (`ZiskFv/AirsClean/**` only) but squarely inside what this task asked about;
* every top-level declaration of the six `*MirrorWeld.lean` files themselves (241
  declarations at the current tree; the count moves as the weld files grow, and
  is orthogonal to the resolver fix) — the weld theorems and the
  `Extracted*`/probe scaffolding they introduce.

Not reclassified here: `survey.py`'s NEAR_* declarations (already out of the #304
round trip's own scope, for a declared reason each) and the ~25 `NEAR_BUS`
`FullEnsemble/Balance/*` declarations — those are ensemble/channel-balance
machinery, not constraint mirrors, though several of them *are* on the
reachability path (see "The Balance/* layer" below) and none is fidelity-only in
the same sense.

## Headline numbers

| | count |
| --- | --- |
| declarations indexed under `ZiskFv/` | 8690 |
| root declarations (9 files) | 44 |
| forward-reachable from the roots | 805 (9.3% of all `ZiskFv/` declarations) |
| mirror-class findings classified | 46 (40 `CLASSIFICATION` + 1 `DELEGATED` + 5 `EXTRA`) |
| **CONSUMED** | **35** |
| **FIDELITY-ONLY** | **11** |
| CONSUMED (loose-only, ambiguous, needs manual check) | 0 |
| not located in tree (stale entry) | 0 |
| `*MirrorWeld.lean` declarations | 241 |
| … of which reachable from the acceptance surface | **0** |

(Previously reported, under the pre-fix over-matching resolver: 36 CONSUMED / 10
FIDELITY-ONLY, forward-reachable 1082. See the correction above.)

## Per-AIR breakdown

`C` = CONSUMED, `F` = FIDELITY-ONLY. Every verdict below resolves identically
under the (now namespace-strict) strict pass and the loose (ambiguous-fallback)
pass — i.e. none of these 46 needs the ambiguous fallback to be reachable, and
none is reachable only through it.

| AIR | mirror | class | verdict |
| --- | --- | --- | --- |
| Arith | `ArithMul/Spec.lean:Spec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:C46Spec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:DivModeSpec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:DivBoundarySpec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:DivInverseSumSpec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:DivScopeSpec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:DivWModeSpec` | MIRROR | C |
| Arith | `ArithMul/Spec.lean:SharedDivBlockSpec` | MIRROR_COMPOSITE | C |
| Arith | `ArithMul/Spec.lean:FullSpec` | MIXED_COMPOSITE | C |
| Arith | `ArithDiv/Spec.lean:Spec` | MIRROR | C |
| Arith | `ArithDiv/Spec.lean:FullSpec` | MIXED_COMPOSITE | **F** |
| Binary | `Binary/Spec.lean:Spec` | MIRROR | C |
| Binary | `Binary/Bridge.lean:constraints_at` | MIRROR_VALIDATOR | **F** |
| BinaryAdd | `BinaryAdd/Circuit.lean:CoreFacts` | MIRROR | C |
| BinaryAdd | `BinaryAdd/Circuit.lean:ComponentSpecFacts` | MIXED_COMPOSITE | C |
| BinaryAdd | `BinaryAdd/Bridge.lean:constraints_at` | MIRROR_VALIDATOR | **F** |
| Main | `Main/Spec.lean:Spec` | MIRROR | C |
| Main | `Main/Spec.lean:AddressSpec` | MIRROR | **F** |
| Main | `Main/Spec.lean:SourceSpec` | MIRROR | **F** |
| Main | `Main/Circuit.lean:RomBoolSpec` | MIRROR | **F** |
| Main | `Main/Circuit.lean:MainRomAddressGuard` | MIRROR_BUILDER | C |
| Main | `Main/Circuit.lean:MainRomSourceGuard` | MIRROR_BUILDER | C |
| Main | `Main/Circuit.lean:pcHandshakeBetween` | MIRROR_2ROW | C |
| Main | `Main/Circuit.lean:sourceCCopyBetween` | MIRROR_2ROW | C |
| Main | `Main/Circuit.lean:transitionBetween` | MIRROR_COMPOSITE | C |
| Main | `Main/Circuit.lean:pcHandshakeTransition` | MIRROR_ENV | C |
| Main | `Main/Bridge.lean:constraints_at` | MIRROR_VALIDATOR | **F** |
| Main | `Main/CrossRow.lean:pc_handshake_at` | MIRROR_VALIDATOR | **F** |
| Mem | `Mem/Spec.lean:Spec` | MIRROR | C |
| Mem | `Mem/Bridge.lean:constraints_at` | MIRROR_VALIDATOR | **F** |
| Mem | `Mem/GeneratedTransition.lean:generatedTransition` | MIRROR_COMPOSITE | C |
| Mem | `Airs/Mem.lean:segmentResidualEveryRow` (DELEGATED) | — | C |
| Mem | `Airs/Mem.lean:Valid_Mem` (EXTRA) | — | C |
| Mem | `Airs/Mem.lean:segment_every_row` (EXTRA) | — | C |
| Mem | `Airs/Mem.lean:permutation_every_row` (EXTRA) | — | C |
| Mem | `Airs/Mem.lean:core_every_row` (EXTRA) | — | C |
| MemAlign | `MemAlign/Spec.lean:Spec` | MIRROR | C |
| MemAlign | `MemAlign/Circuit.lean:transitionRows` | MIRROR_2ROW | C |
| MemAlign | `MemAlign/Circuit.lean:cyclicSuccessorTransitionRows` | MIRROR_2ROW | C |
| MemAlign | `MemAlign/Circuit.lean:transition` | MIRROR_ENV | C |
| MemAlign | `MemAlign/Circuit.lean:cyclicSuccessorTransition` | MIRROR_ENV | C |
| MemAlignByte | `MemAlignByte/Spec.lean:Spec` | MIRROR_MIXED | C |
| MemAlignByte | `MemAlignByte/Bridge.lean:constraints_at` | MIRROR_VALIDATOR | **F** |
| MemAlignReadByte | `MemAlignReadByte/Spec.lean:Spec` | MIRROR_MIXED | C |
| MemAlignReadByte | `MemAlignReadByte/Bridge.lean:constraints_at` | MIRROR_VALIDATOR | **F** |

## The pattern

Every AIR's core `Spec` — the mirror wired straight into that AIR's live
`component.circuit.Spec` field (`fun row _ _ => Spec row` or a conjunction
containing it, e.g. Arith's `FullSpec row ∧ SharedDivBlockSpec row`) — is
CONSUMED, for all nine AIRs that have one. So is every mirror feeding a
`Component.transition`/`cyclicSuccessorTransition` field (Main's
`pcHandshakeBetween`/`sourceCCopyBetween`/`transitionBetween`/
`pcHandshakeTransition`, MemAlign's four), and every `MIRROR_BUILDER` mirror
folded into the honest-row construction the circuit's `assertZero`s run against
(Main's `MainRomAddressGuard`/`MainRomSourceGuard`). This is the expected shape:
the thing actually checked by an accepted trace is exactly what its Spec/
transition fields say, and that is where the "real" mirror lives.

Three systematic exceptions, all FIDELITY-ONLY, and none is what "welded but
consumed by nothing" usually looks like (dead code) — all are verified below to
be **used, just not by acceptance**:

### 1. The whole `MIRROR_VALIDATOR` family (`constraints_at` over `Valid_<AIR>`, `pc_handshake_at`)

Six declarations, one per AIR that has this validator layer (Binary, BinaryAdd,
Main, Mem, MemAlignByte, MemAlignReadByte) — **all six** are FIDELITY-ONLY. This
is a second, parallel mirror layer per AIR: `Bridge.lean`/`CrossRow.lean` restate
the same constraints over `Valid_<AIR>`-indexed row accessors (a trace-level
interface, not the Clean row record), proved *from* the AIR's live
`ConstraintsHold`. None of that family is part of `component.circuit.Spec` for any
AIR.

Checked what each one is used for instead of just reporting "not found":

* `Main.pc_handshake_at` has exactly one consumer outside `ZiskFv/AirsClean/**`:
  `ZiskFv/Compliance/MainTransition.lean`, which derives
  `AcceptedZiskTrace.mainTransition_to_next_pc` — a theorem *about* an accepted
  trace, but one that lives one level downstream of `AcceptedZiskTrace`'s own
  directory (it imports `AcceptedZiskTrace.MainTable`, it is not part of the
  group `AcceptedZiskTrace.lean`'s own docstring describes), feeding the
  per-opcode `h_nextPC_matches` construction that `ZiskFv/Soundness.lean`'s
  `root_soundness` ultimately needs. Used, by the soundness *proof*, not by the
  acceptance *definition*.
* `Mem.constraints_at` has one consumer outside its own `Bridge.lean`:
  `ZiskFv/AirsClean/FullEnsemble/Balance/RowsBridgeFacts.lean`
  (`constraints_at_of_memTableGeneratedRowsBridge`, line 987) — a file that *is*
  imported by an acceptance-surface root (`AcceptedZiskTrace.lean` imports it
  directly), but that one theorem is not itself on the path any root declaration's
  body actually walks; the file is large (1000+ lines) and only part of it is
  currently exercised from `AcceptedZiskTrace`'s own derivations. A live,
  reachable neighbor of the acceptance surface, not (yet) inside it.
* `Binary.constraints_at`, `BinaryAdd.constraints_at`, `MemAlignByte.constraints_at`,
  `MemAlignReadByte.constraints_at` have **no consumer anywhere** outside their own
  defining `Bridge.lean` file (confirmed by grep: each of those four AIRs'
  `Bridge.lean` is the *only* file mentioning `constraints_at` for that AIR — not
  even that AIR's own `*MirrorWeld.lean` cites it). These four are closer to
  genuinely unused scaffolding than to "used downstream" — flagged here as the
  weakest members of the FIDELITY-ONLY set.

### 2. Main's `AddressSpec`, `SourceSpec`, `RomBoolSpec`

Verified directly against `ZiskFv/AirsClean/Main/Circuit.lean`: the live
component's `Spec` field (line 690, `circuitWithRomMemAndOpBus`, the one
`FullEnsemble.lean` composes) is

```lean
Spec := fun row _ _ => Spec row.core
```

— only the base `Spec` (already CONSUMED above). `AddressSpec`, `SourceSpec` and
`RomBoolSpec` are each proved *derivable* from `ConstraintsHold` by a standalone
theorem in the same file
(`addressSpec_of_mainWithRomAndMemBus_constraints`,
`sourceSpec_of_mainWithRomAndMemBus_constraints`,
`romBoolSpec_of_mainWithRomAndMemBus_constraints`), but none of the three is
folded into the ensemble's own `Spec`/`Constraints` obligation. Checked what
consumes the derivation instead:

* `AddressSpec` and `SourceSpec` are each consumed by several files under
  `ZiskFv/Compliance/TraceLevelExport/**` — the root-soundness construction layer
  (`RomDecodeBinding.lean`, `RomDecodeBindingOps.lean`, `RowDataArithMem.lean`,
  `StepStrongControlStore.lean`, `StepStrongLoadMext.lean`). Used, by the
  soundness proof, not by the acceptance definition — the same shape as
  `pc_handshake_at` above.
* `RomBoolSpec` has **no consumer under `ZiskFv/Compliance/**` at all**. Its only
  reference outside `Main/Circuit.lean` itself is `ZiskFv/AirsClean/MainMirrorWeld.lean`
  (the orphaned weld). Of the three, `RomBoolSpec` is the one with no live
  downstream use anywhere in the tree today.

### 3. Arith's `ArithDiv/Spec.lean:FullSpec`

The one finding whose verdict the resolver fix actually changed (C → F; see the
correction at the top of this report). `ArithDiv.FullSpec`'s body (`Spec row ∧
ArithTableSpec row ∧ IndexedRangeSpec row`) reads its own sibling `Spec` — a
same-namespace reference, correctly resolved either way — but `FullSpec` itself
is not one of `ArithDiv`'s live `component.circuit.Spec` fields; that role for
the div/rem AIRs is filled by `ArithMul`'s `FullSpec ∧ SharedDivBlockSpec`
(`ArithMul/Circuit.lean:631`, already CONSUMED above), a *different* declaration
in a *different* namespace that happens to share the bare name `FullSpec`. That
sharing is exactly what the old resolver's unqualified suffix match confused.

Checked what actually consumes `ArithDiv.FullSpec` instead: `ArithDiv/Bridge.lean`
projects `FullSpec (rowAt v r)` for a P4 construction, and it flows from there into
`ZiskFv/Compliance/ConstructionDiv.lean`, `ConstructionDivu.lean`,
`ConstructionDivuw.lean`, `ConstructionMulh.lean`, `ConstructionMulhsu.lean`,
`ConstructionMulhu.lean`, `ConstructionMulw.lean`, `ConstructionRemu.lean`,
`ConstructionRemuw.lean`, `OpBusProviderMatch.lean`, `SharedBundles.lean`, and
the `TraceLevelExport`/`Wrappers` construction layer. Same shape as the other
two exceptions: used by the soundness *proof*, not by the acceptance
*definition*.

### The Mem `Valid_Mem` family is a different, *consumed* story

Do not conflate `Mem.Bridge.lean`'s `constraints_at` (FIDELITY-ONLY, above) with
the pre-Clean `ZiskFv/Airs/Mem.lean` mirrors the `MemMirrorWeld.lean` docstring
names — `Valid_Mem`, `segment_every_row`, `permutation_every_row`,
`core_every_row`, `segmentResidualEveryRow`. These are a *different* declaration
family (older namespace, `ZiskFv.Airs.Mem`, not `ZiskFv.AirsClean.Mem`), and all
five are **CONSUMED**: they are exactly what
`ZiskFv/Compliance/AcceptedZiskTrace/MemSegmentRanges.lean`,
`MemProviders.lean` and `FullEnsemble/Balance/RowsBridgeFacts.lean` thread through
to unpack `AcceptedZiskTrace`'s `MutableMemPresent`/`mem_replay_*` machinery. So
for Mem specifically there are two parallel "indexed by a trace accessor" mirror
layers: the old one is load-bearing for the memory-replay direction of
acceptance; the new Clean-side one (`Bridge.lean`'s `constraints_at`) is not (yet)
wired into it.

## The `*MirrorWeld.lean` files: uniformly fidelity-only, and orphaned outright

None of the six weld files (`ArithMirrorWeld.lean`, `BinaryMirrorWeld.lean`,
`MainMirrorWeld.lean`, `MemAlignByteMirrorWeld.lean`, `MemAlignMirrorWeld.lean`,
`MemMirrorWeld.lean`) is imported by anything else checked in:

```bash
$ grep -rn "import ZiskFv.AirsClean.<Name>MirrorWeld" ZiskFv trust Tests
# (no output, for every one of the six)
```

So every one of their 241 top-level declarations is FIDELITY-ONLY by
construction, independent of the reachability walk (which agrees: 0/241
reachable — confirmed again against the fixed resolver; this conclusion is
import-based, not resolver-based, so it was never at risk from the #304-review
bug). This includes the mechanically-derived weld-internal defs
`ExtractedMemRow`, `ExtractedMemTrace`, `MemProbe`, `rowMainValue`,
`traceMainValue`, and their five siblings' equivalents, plus every `constraint_N_weld`,
`spec_weld`/`segment_weld`/`permutation_weld`, and the two `*_pinned` instance-pin
theorems. **This is exactly the pattern the task named as the standing example**
(`ExtractedMemTrace`) — and it generalizes cleanly to all six weld files, with no
exception. The weld files are, in full, a fidelity check: nothing they define is
part of what "accepted" means, and nothing outside them names anything they
define.

This is architecturally deliberate, not a gap: a weld file's entire job is to
kernel-check an `Iff.rfl` between a pre-existing mirror (defined elsewhere, e.g.
`Mem.Spec`) and the generated constraints. Its own scaffolding (the
`Extraction.Circuit` instances, the probe circuits) exists only to state that
`Iff.rfl`, never to be consumed by anything downstream — and it is the
pre-existing mirror it welds (`Mem.Spec`, `Valid_Mem`/`segment_every_row`, etc.)
whose OWN consumption status is the real question, answered per-AIR above.

## The Balance/* layer, for context (not reclassified)

`ZiskFv/AirsClean/FullEnsemble/Balance/*` holds ~25 `NEAR_BUS` declarations
(channel/interaction/replay predicates, not constraint mirrors — out of
`survey.CLASSIFICATION`'s own mirror scope). Several are directly on the
reachability path: `AcceptedZiskTrace.lean` imports `RowsBridgeFacts.lean` and
`TableProjections.lean` directly, and the companion files import
`MemBusRowBridges.lean` and the rest of `Balance/`. This is the plumbing that
makes `channels_balanced`/`MutableMemPresent`/`mem_replay_*` operational, and
(unlike the mirror findings above) is squarely part of the acceptance surface —
it is reported here only so the ~25 NEAR_BUS names are not mistaken for an
omission.

## Answering the task's specific questions

* **Which welded constraints are fidelity-only?** All content of all six
  `*MirrorWeld.lean` files (241 declarations, 0 reachable) — see above. Among the
  *pre-existing* mirrors a weld cites (as opposed to weld-owned scaffolding), the
  `MIRROR_VALIDATOR` family is fidelity-only for every AIR that has one (Binary,
  BinaryAdd, Main, Mem, MemAlignByte, MemAlignReadByte), Main's
  `AddressSpec`/`SourceSpec`/`RomBoolSpec` are fidelity-only despite being
  matched/weld-covered by #304/#296, and (post resolver-fix) so is Arith's
  `ArithDiv.FullSpec`.
* **Are the Main/Mem welds we care about consumed or fidelity-only?** The weld
  *files* are fidelity-only, full stop (nothing imports them). The mirrors they
  weld are a mix: `Main.Spec`/`Mem.Spec` (the mirrors that actually flow into
  `fullRv64imEnsemble`, per each weld file's own docstring) are CONSUMED;
  `Main.AddressSpec`/`SourceSpec`/`RomBoolSpec` and `Mem.Bridge.constraints_at`
  are FIDELITY-ONLY (though the first two of Main's three, and the old-namespace
  `Mem`/`Airs` family, are genuinely used one layer downstream, in the soundness
  proof rather than the acceptance definition).

## Method limitations (measured, not just disclosed)

* **Textual, not elaborated.** No instance resolution, no unfolding, no macro
  expansion. A mirror consumed only through an instance argument Lean would infer
  without a literal name appearing in source would be invisible to this pass. No
  case of that was found in the 46 classified findings (0 loose-only
  reclassifications), but the tool cannot rule it out in general.
* **Under-matching by design, not over-matching.** `resolve()` only accepts an
  EXACT `fqn_map` lookup of a fully-constructed candidate name (the token as
  given, or prefixed by the reading declaration's own/an ancestor namespace, an
  `open` alias, or a blanket `open` namespace). A bare token matching no real
  in-scope declaration this way is UNRESOLVED, not a hit against every
  declaration sharing that bare last segment across unrelated namespaces — that
  bare-suffix match was a real bug (see the correction at the top of this
  report), confirmed to have wrongly marked `ArithDiv.FullSpec` CONSUMED via its
  bare-name collision with the genuinely-consumed `ArithMul.FullSpec`. This is
  still a heuristic, not kernel-verified: it is a name-based textual pass, not an
  elaborated call graph, so it can in principle still under-report (miss a real
  reference the tokenizer or namespace tracking mishandles) but cannot
  over-report a CONSUMED verdict through a cross-namespace name collision, which
  was the specific failure mode fixed here.
* **Ambiguity is upper-bounded, not resolved.** The separate loose pass's
  bare-name fallback (used only when the strict, namespace-aware resolution
  finds nothing, and reported separately as "consumed only via ambiguous
  bare-name fallback, manual check needed") is the same approximation
  `survey.reference_counts` already accepts; it changes no verdict among the 46
  classified findings under the fixed resolver, which is now meaningful evidence
  the namespace/`open` tracking is doing real work — not, as previously claimed,
  evidence measured against a strict pass that was itself already over-matching.
* **Every FIDELITY-ONLY verdict above was independently checked by reading
  source**, not accepted from the mechanical pass alone: `Main/Circuit.lean`'s
  actual `Spec` field text, `ArithMul/Circuit.lean`'s actual `Spec` field text
  (for `ArithDiv.FullSpec`), and a direct `grep` of who else names each
  `constraints_at`/`AddressSpec`/`SourceSpec`/`RomBoolSpec`/`FullSpec`. The
  CONSUMED verdicts were spot-checked the same way for `Mem.Spec` and
  `ArithMul`'s `FullSpec`/`SharedDivBlockSpec` composition, not exhaustively for
  all 35.
* **Scope is `survey.CLASSIFICATION`'s mirror classes plus a small named
  addendum**, not "every Prop under `ZiskFv/`". `NEAR_*` and `NEAR_BUS`
  declarations are not reclassified (see "The Balance/* layer" above for why that
  is a scope choice, not an oversight).
