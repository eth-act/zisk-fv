# Is a #304 mirror consumed by acceptance, or fidelity-only?

Issue: eth-act/zisk-fv#304 follow-up (verification-hole track). Companion to
`tools/mirror-roundtrip/README.md`. Reproduced by:

```bash
python3 tools/mirror-roundtrip/consumed_check.py          # this report's data, regenerated
python3 tools/mirror-roundtrip/consumed_check.py --json PATH.json
```

Python 3 standard library only; no Lean build, no network; nothing under `ZiskFv/`
is read as anything other than text and nothing under it is written.

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
3. Pops a declaration, tokenizes its body, resolves each token against the global
   index — trying an exact/suffix FQN match, then the declaration's own or an
   enclosing namespace, then its file's explicit `open` aliases, then a blanket
   `open X` namespace — and adds every newly-reached declaration to the worklist.
   A declaration is **CONSUMED** iff it ends up in the visited set.
4. A separate, looser pass additionally falls back to an ambiguous bare-name match
   (the same approximation `survey.reference_counts` already uses for "unreachable
   mirror") when the precise resolution finds nothing, purely to flag cases the
   precise walk might have missed through a resolution gap. **At HEAD it changes
   no verdict**: all 46 classified findings resolve identically under both passes
   (0 "loose-only" reclassifications) — the precise walk is not silently
   under-reaching here.

This shares `survey.reference_counts`'s soundness property and its limit: a
**positive** reachability claim is only as good as the textual resolution that
produced it (two same-named declarations in unrelated namespaces could in
principle be confused); a **negative** one — nothing in the closure names this
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
* every top-level declaration of the six `*MirrorWeld.lean` files themselves (225
  declarations) — the weld theorems and the `Extracted*`/probe scaffolding they
  introduce.

Not reclassified here: `survey.py`'s NEAR_* declarations (already out of the #304
round trip's own scope, for a declared reason each) and the ~25 `NEAR_BUS`
`FullEnsemble/Balance/*` declarations — those are ensemble/channel-balance
machinery, not constraint mirrors, though several of them *are* on the
reachability path (see "The Balance/* layer" below) and none is fidelity-only in
the same sense.

## Headline numbers

| | count |
| --- | --- |
| declarations indexed under `ZiskFv/` | 8674 |
| root declarations (9 files) | 44 |
| forward-reachable from the roots | 1082 (12.5% of all `ZiskFv/` declarations) |
| mirror-class findings classified | 46 (40 `CLASSIFICATION` + 1 `DELEGATED` + 5 `EXTRA`) |
| **CONSUMED** | **36** |
| **FIDELITY-ONLY** | **10** |
| `*MirrorWeld.lean` declarations | 225 |
| … of which reachable from the acceptance surface | **0** |

## Per-AIR breakdown

`C` = CONSUMED, `F` = FIDELITY-ONLY. Every verdict below resolved identically
under the strict and the loose (ambiguous-fallback) pass.

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
| Arith | `ArithDiv/Spec.lean:FullSpec` | MIXED_COMPOSITE | C |
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

Two systematic exceptions, both FIDELITY-ONLY, and neither is what "welded but
consumed by nothing" usually looks like (dead code) — both are verified below to
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

So every one of their 225 top-level declarations is FIDELITY-ONLY by
construction, independent of the reachability walk (which agrees: 0/225
reachable). This includes the mechanically-derived weld-internal defs
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
  `*MirrorWeld.lean` files (225 declarations, 0 reachable) — see above. Among the
  *pre-existing* mirrors a weld cites (as opposed to weld-owned scaffolding), the
  `MIRROR_VALIDATOR` family is fidelity-only for every AIR that has one (Binary,
  BinaryAdd, Main, Mem, MemAlignByte, MemAlignReadByte), and Main's
  `AddressSpec`/`SourceSpec`/`RomBoolSpec` are fidelity-only despite being
  matched/weld-covered by #304/#296.
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
* **Ambiguity is upper-bounded, not resolved.** The loose pass's bare-name
  fallback is the same approximation `survey.reference_counts` already accepts;
  it changed no verdict here, which is itself evidence the namespace/`open`
  tracking is doing real work, not evidence that ambiguity cannot occur elsewhere
  in `ZiskFv/`.
* **Every FIDELITY-ONLY verdict above was independently checked by reading
  source**, not accepted from the mechanical pass alone: `Main/Circuit.lean`'s
  actual `Spec` field text, and a direct `grep` of who else names each
  `constraints_at`/`AddressSpec`/`SourceSpec`/`RomBoolSpec`. The CONSUMED verdicts
  were spot-checked the same way for `Mem.Spec` and `ArithMul`'s `FullSpec`/
  `SharedDivBlockSpec` composition, not exhaustively for all 36.
* **Scope is `survey.CLASSIFICATION`'s mirror classes plus a small named
  addendum**, not "every Prop under `ZiskFv/`". `NEAR_*` and `NEAR_BUS`
  declarations are not reclassified (see "The Balance/* layer" above for why that
  is a scope choice, not an oversight).
