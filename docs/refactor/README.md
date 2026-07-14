# zisk-fv architecture review & refactor plan

This directory is a **written architecture review and refactor proposal**. It
contains no code changes. It is grounded in a read of the current tree
(`ZiskFv/`, the vendored `Clean` package under `.lake/packages/Clean`, and
`trust/`) at the `Initial commit` revision.

The goal set by the engagement:

1. Redesign the **top-level theorem API** (`root_soundness` /
   `root_completeness`) for maximum explicitness and auditability.
2. Re-architect the **proofs below** for maintainability, extensibility, and
   correctness — with particular attention to whether the `Clean` circuit
   library is used *idiomatically* (upstream `Verified-zkEVM/clean`
   conventions as the north star).

## Start here

[**`FINAL-PLAN.md`**](FINAL-PLAN.md) is the consolidated, self-contained final
plan/overview: it folds this README and documents `01`–`07` into one narrative
(headline conclusions, as-is architecture, Clean idioms, the root-API redesign,
the proof-architecture refactor, inconsistencies, root-stability discipline,
upstream-Clean tracking, and the sequenced roadmap). Read it first; the numbered
documents below remain as the detailed backing for each section.

## How to read this

| Document | Contents |
| --- | --- |
| [`FINAL-PLAN.md`](FINAL-PLAN.md) | **The consolidated final plan/overview — start here.** Everything below, folded into one document. |
| [`01-architecture-map.md`](01-architecture-map.md) | The layer cake as it actually is: data flow from Sail + PIL to the two root theorems, where the mass lives, and the per-opcode multiplicity problem. |
| [`02-clean-idioms-and-usage.md`](02-clean-idioms-and-usage.md) | Upstream Clean idioms (`FormalCircuit`, `GeneralFormalCircuit`, `ProvableType`, `Air.Flat`, `FormalEnsemble`, `OrderedChannels`, `Vm`, `circuit_norm`), how the project uses them, what is idiomatic, and where it diverges. |
| [`03-root-theorem-api.md`](03-root-theorem-api.md) | Concrete redesign of the two root theorems: unify the two stacked soundness statements, name the trust surface, and give an auditable `root_completeness` skeleton. Includes Lean sketches. |
| [`04-proof-architecture-refactor.md`](04-proof-architecture-refactor.md) | The per-opcode layer collapse, the legacy `Airs` ↔ `AirsClean` unification, promise/trust-ledger rationalization, and the reusable abstractions to introduce. |
| [`05-inconsistencies-and-correctness.md`](05-inconsistencies-and-correctness.md) | Documented-vs-actual drift, naming/vocabulary debt, and correctness-relevant smells to check, each with a location. |
| [`06-roadmap.md`](06-roadmap.md) | A sequenced, build-green, incrementally-landable plan with effort/risk and measurable exit criteria. |
| [`07-root-stability-and-upstream-clean.md`](07-root-stability-and-upstream-clean.md) | **(Read after `03`/`06`.)** How to run the refactor without destabilising the root statement (a T0/T1/T2 change-tier discipline, an equivalence-bridge protocol, and a `#print axioms` golden test), plus a concrete assessment of upstream `Verified-zkEVM/clean`: the fork base (~mid-May 2026), the 6 local Clean patches, and the incoming PRs of interest (#398 zero-multiplicity channels, the `Vm.lean` overhaul, autoelaborate/#425, Lean 4.29, witgen-ir). Supersedes `03`/`06` where they conflict on sequencing. |

## Executive summary

The project is large and, at the two seams that matter most, **more idiomatic
than the request feared**: the Clean ensemble seam
(`AirsClean/FullEnsemble` → `Compliance/AcceptedZiskTrace`) genuinely uses
Clean's `FormalEnsemble` / `SoundEnsemble` / `TableSoundness` machinery, and the
per-component circuits (e.g. `AirsClean/BinaryAdd`) are written as
`GeneralFormalCircuit`s with `ProvableStruct` rows, `assertZero`/`lookup`/channel
`push`, and `circuit_proof_start`. That is the right foundation.

The problems are **structural and above the Clean seam**, and they are what make
the audit surface opaque:

1. **Two stacked root soundness statements.** `root_soundness`
   (`ZiskFv/Soundness.lean`, per-step, over `AcceptedZiskTrace`) is the
   advertised headline, but it is *implemented on top of* the older
   `zisk_riscv_compliant_program_bus` (`ZiskFv/Compliance.lean`, per-arm, over
   `OpEnvelope`): each `TraceLevelExport/StepStrong*` step *constructs* an
   `OpEnvelope.<op>` value and invokes the old theorem. An auditor must
   understand *both* statements and the glue between them. The trust ledger
   still names the *old* one as "the global Lean theorem"; the READMEs name the
   *new* one. (See `05`.)

2. **Two parallel circuit models of the same AIRs.** A legacy record model
   (`Airs/`, the `Valid_<AIR>` records — `Valid_Main` alone is referenced by
   **299 files**) coexists with the Clean model (`AirsClean/`). They are stitched
   together by per-opcode `Bridge.lean` adapters (`rowAt`, `spec_of_valid`). The
   whole equivalence/compliance stack is written against the *legacy records*,
   not the Clean components, so the idiomatic Clean layer is bridged *into* a
   non-idiomatic one rather than being the spine. (See `01`, `02`.)

3. **~7–9 near-parallel per-opcode layers.** Each of ~63 opcodes recurs as a
   separate file in `Airs/`, `AirsClean/<Op>/`, `EquivCore/<Op>`,
   `Equivalence/<Op>`, `Compliance/Wrappers/<Op>`, `Compliance/Construction<Op>`,
   and an `OpEnvelope` arm, plus a `TraceLevelExport/StepStrong*` case. Adding or
   auditing one opcode means touching all of them. This is the dominant
   maintainability and extensibility cost. (See `01`, `04`.)

4. **A bespoke "promise / caller-burden / forbidden-shape" trust discipline**
   substitutes for what Clean's ensemble soundness is designed to deliver. The
   canonical `equiv_<OP>` theorems carry large surfaces of caller-supplied
   hypotheses ("promises"), policed by hand-maintained ledgers
   (`trust/forbidden-param-shapes.txt`, `baseline-*-caller-burden.txt`). This is
   an impressive discipline, but it is a *symptom*: the hypotheses exist because
   the top statement does not derive them from the accepted-trace / balanced-
   channel facts the way `FormalEnsemble.soundness` + VM-channel soundness are
   meant to. (See `02`, `04`.)

5. **Documentation has drifted from the code** in ways that directly mislead an
   auditor (dependency direction, opcode counts, "sum type" vs conjunction
   dispatch, which theorem is the headline). Concrete list in `05`.

### The three highest-leverage recommendations

- **R1 — Unify the soundness endpoint (API).** Make `root_soundness` the *only*
  advertised soundness theorem, restate `zisk_riscv_compliant_program_bus` as a
  clearly-internal per-arm lemma, and give `root_soundness` a single named
  **trust-surface record** (channel-balance, boot memory seed, Aeneas bridge,
  defect exclusion) so the entire trusted premise set is visible in one place.
  See `03`.

- **R2 — Make the Clean component model the spine; demote `Airs/` records to a
  thin generated view (or delete).** Drive the equivalence stack off the Clean
  `GeneralFormalCircuit` `Spec`s directly, so `Bridge.lean` adapters and the
  duplicate `Valid_<AIR>` modeling disappear. This is the single change that most
  reduces total surface and makes "idiomatic Clean" true end-to-end. See `04`.

- **R3 — Collapse the per-opcode stack behind per-*shape* abstractions.** Replace
  ~63×N opcode files with ~12 shape families (R-type/I-type/branch/shift/load/
  store/…) each carrying one parametric equivalence theorem and one `Promises`
  bundle; generate the opcode instances. See `04`. (This extends, and partly
  supersedes, the existing `simplification-suggestions.md`.)

### Relationship to `simplification-suggestions.md`

The repo already has a tactical `simplification-suggestions.md` (line-count-
oriented: collapse `dispatch_X`, thread `Promises`, rename `_from_trust`). Those
are good and consistent with this plan, but they operate *within* the current
architecture. This review is one level up: it targets the architecture itself
(the two stacked roots, the two circuit models, the per-opcode multiplicity, and
the idiomatic-Clean question). Where they overlap, this document notes it.

### A note on correctness

Nothing here asks to weaken a theorem or expand trust. Every recommendation is
either (a) a *restatement* that exposes an existing premise more honestly, or
(b) a *derivation* that removes a caller-supplied hypothesis by proving it. The
one hard rule from `AGENTS.md` — "promise discharge must reduce caller-supplied
trust, never rename it" — is the correctness invariant for the whole refactor,
and each step in `06` is annotated with its trust-ledger effect.
