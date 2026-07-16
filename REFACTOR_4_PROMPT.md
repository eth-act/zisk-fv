# Task: Phase 2.3 + 2.4 remainder — finish the wrapper-surface shrink

## Situation

**The tree delivered with this prompt is the current source of truth.** If it arrived as a
tarball attached to a continue prompt, replace your entire working tree with the tarball's
contents before doing anything else — your prior local repository state (including your own
earlier commits) is outdated and must not be trusted.

Sandbox limitations, pre-acknowledged: no git branch history; no `zisk` submodule, so
trust check 13 cannot run for you — defer exactly that check, every other gate is
mandatory. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`, `flake.lock`,
or `ZiskFv/Audit.lean`.

## Done vs. remaining

Your previous turn's RTYPE/ITYPE work is integrated in this tree: eleven opcodes'
wrapper + canonical surfaces consume `StaticBinaryRTypeEvidence` /
`StaticBinaryProviderEvidence` (`ZiskFv/Compliance/SharedBundles.lean`), assembled from
the `DerivedRowFacts` seam (`opProviderRowFacts`, `staticBinarySub/Logic/
CompareProviderRowFacts`, `registerWriteLanes`, `mainRowPins`). Branch was verified
binder-free. This turn is the remainder you tabled: items 3–8, 10–11 of the previous
work order, renumbered below. The same recipe applies: family evidence package (extend
`SharedBundles.lean`), family provider specialization at the seam (extend
`DerivedRowFacts.lean`), shrink every wrapper + canonical surface in the family, update
Construction/Dispatch/StepStrong callers.

## Numbered work order

Acceptance per item: every seam-derivable binder (`providerTable`, `providerRow`,
membership, component/spec, `h_match`, `h_lane_rd`, `pins`) removed from each wrapper and
canonical surface in the family — or a precise blocker note naming file, theorem, and the
failing derivation; zero new caller-supplied hypotheses; before/after parameter counts
recorded per theorem; build green, commit, proceed to the next item.

1. **Shift family** — add the BinaryExtension `shiftStaticLookupComponent` provider
   specialization at the seam and a shift evidence package; shrink the twelve
   BinaryExtension wrapper/canonical surfaces.
2. **ADD_RTYPEW family** — add the BinaryAdd provider specialization; shrink ADD, ADDI,
   ADDW, ADDIW, SUBW and their BinaryAdd/static-Binary alternative surfaces
   (`equiv_ADD_via_binaryadd` included).
3. **DIVU family** — add the ArithMul provider specialization; shrink the DIVU-family
   surfaces.
4. **Remaining family** — the `Dispatch/Remaining.lean` ops (M-extension and others):
   reuse the ArithMul specialization where applicable; shrink each wrapper/canonical
   surface, or blocker-note the specific ops whose provider shape genuinely differs.
5. **Misc family** — same recipe.
6. **NoMemOrSimple family** — same recipe.
7. **LDSD family** — loads/stores: remove exactly the binders that ARE seam-derivable
   (pins, rd lane where applicable, op-bus provider facts); any binder tied to the
   memory timeline that is genuinely not seam-derivable gets a precise blocker note and
   stays. Do not force it; do not weaken anything.
8. **Cleanup** — delete every `main_request_*` balance-rebuild lemma that is now
   consumer-free (verify zero consumers first, keep any that still have one); likewise
   any per-family loose-parameter helper superseded by the evidence packages.
9. **Final sweep** — complete per-family before/after parameter-count table covering
   BOTH turns' families; `trust/generated/` byte-for-byte unchanged; full `lake build`,
   `trust/scripts/check-all.sh` (minus check 13), `trust/scripts/check-all-semantic.sh`
   all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified blocker
note. A clean build or a committed chunk is a checkpoint, not a stop condition: after
finishing an item, proceed immediately to the next. Committing and reporting with items
silently unattempted is a failed turn. If an item is blocked, skip it, document the precise
blocker (file, theorem, error), and continue with the next item. Your previous turn
delivered items 1–2 of twelve and stopped with time remaining — this turn's standard is
all nine items attempted.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- Everything is T0: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched and passing.
- Every removed binder must be **proved** from accepted-trace facts via the seam — never
  moved into a broader premise, a strengthened validator, or a new caller-supplied
  hypothesis. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`. No file under `trust/generated/` may change; no baseline created.
- The `EquivCore/<Op>.lean` core theorem statements and the legacy `m : Valid_Main`
  parameter are out of scope (Phase 3 owns that layer).
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` with: a per-item status table for
items 1–9 (done / blocked+why / not reached); per-theorem before/after parameter counts;
the evidence-package design used per family; and exact gate results.
