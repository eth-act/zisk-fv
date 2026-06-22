# PLAN — Architecture Clarification

A legibility refactor of the two public theorems and their support tree, plus the
durable record of the architecture inspection + naming decisions behind it.

- Branch: `arch-clarify` (worktree `.worktrees/arch-clarify`), based on
  `origin/issue-114-extraction` = **main + PR #121** (8834dec1). Rebase onto
  `origin/main` once #121 merges. Warm `.lake` + symlinked `build/` reused from the
  #121 worktree.
- Status: **S0–S3 done, committed, green** (front door + completeness renames).
  S4+ paused at Cody's request to discuss architecture more.

## Goal

A human opens ONE file, sees the project's results under clear parallel names,
reads each hypothesis's meaning + whether it's discharged, sees the honest scope,
and descends ≤2–5 legible levels before hitting detail. **Clarity only**: this
refactor discharges no trust residual and does NOT merge the two theorems.

---

# Part I — Architecture as it stands today (the map)

## The two results (no Lean edge between them)

The project proves **two separate** things. `ZiskFv.Compliance` does NOT import
`ZiskFv.Completeness`; there is no dependency edge, so they cannot be honestly
fused into one theorem (that would manufacture a connection that doesn't exist).

```
   SOUNDNESS                                   COMPLETENESS
   "circuit post-state = Sail post-state,      "every Sail-executable RV64IM word
    per opcode"                                  is decoded/lowered/covered by ZisK"
   Compliance.zisk_riscv_compliant_program_bus  Completeness.Rv64im.<endpoint>
   (ZiskFv/Compliance.lean:95)                  (ZiskFv/Completeness/Rv64im.lean:5919)
```

## Soundness tree (top → detail)

1. `zisk_riscv_compliant_program_bus (env : OpEnvelope …) (h_bridge) (h_memory_construction)
   (h_known_bugs) : env.exec_eq` — `Compliance.lean:95`.
   - `env.exec_eq` = a 12-way conjunction: the 2 trust residuals + 10 per-family
     `exec_eq_<family>`. For any concrete arm exactly ONE family fires; the other
     9 are definitionally `True`.
   - `OpEnvelope` = a ~65-arm inductive (one constructor per opcode-route, each
     bundling that opcode's witness inputs + "promise" proof fields).
2. 10 per-family dispatchers `Compliance/Dispatch/*` — pure routing
   (`cases env; exact Equivalence.<Op>.equiv_<OP> …; | _ => trivial`).
3. 63 canonical `equiv_<OP>` (`Equivalence/<Op>.lean`) — public per-opcode
   statements, gate-pinned to `ZiskFv.Equivalence.<File>.equiv_<OP>`.
4. The real Sail↔circuit proofs (`EquivCore/<Op>.lean`, ~32k lines) — the math.

## Completeness = THREE disconnected fragments (none wired to each other or to soundness)

- **real, partial** — the Clean per-AIR `completeness` obligations in
  `AirsClean/*/Circuit.lean` (**125 genuine proofs**; 42 trivially `True`). Clean's
  `completeness` = "honest inputs yield an accepting row." Scope = row-local
  (Arith unsigned-only, Binary via table-index). THIS is the witness-construction
  work; it is real.
- **typed contract** — `zisk_riscv_completeness` (was `rv64im_completeness`):
  decode coverage, parameterized over an abstract `Rv.Interface` whose 8 fields
  are uninterpreted predicates **never instantiated in-tree**; all 6 hypotheses
  discharged in the external Aeneas harness. A contract, not a standalone proof.
- **orphaned** — `Completeness/Rv64im/SailDecode.lean` (188 real Sail theorems;
  would-be discharge of the `sailExecutable` hypothesis; nothing depends on it).

## Per-opcode tower (legibility findings)

3 nominal layers but only `EquivCore` is substantive. `Equivalence/<Op>` is a
near-pure restatement (49/63 are `rw [state_effect_via_channels_eq_bus_effect_2];
exact Compliance.equiv_<OP> …`, a `rfl`-bridge). For And/Or/Xor/Andi/Ori/Xori/Sub
the wrapper is **dead** and the doc comments **lie** (claim a wrapper call that
isn't there).

## Naming/structure problems (the legibility audit)

- No front door; `ZiskFv.lean` was a flat import dump. **(fixed: S1)**
- `equiv_<OP>` means 3 different things (canonical / wrapper / EquivCore lemma).
- Clean name `Equivalence` sits on the thinnest layer; the real proofs hide under
  jargon `EquivCore`.
- `Compliance` triple-name: file `Compliance.lean` (holds the theorem) beside dir
  `Compliance/` (holds dispatch+wrappers), both namespace `ZiskFv.Compliance`.
  Also semantically wrong — "compliance" = soundness ∧ completeness, which we do
  not prove.
- `AirsClean` falsely implies `Airs` is legacy; both are live + co-required.
- dir ≠ namespace: `RowShape/` → namespace `Trusted` (declares no axioms);
  `Bits/` → namespace `PackedBitVec`.
- RHS has 3 names: `bus_effect` / `state_effect_via_channels` / "channel-balance".

---

# Part II — What is actually claimed (honesty findings)

These are about *what the theorems mean*, independent of naming.

## The `exec_eq` "tautology" — a cosmetic wart, NOT a soundness hole

The conclusion `env.exec_eq` repeats two of its own hypotheses
(`aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`) as conjuncts 1–2,
discharged by `exact h_bridge` / `exact h_memory_construction`. The theorem is
correctly proved; the math (10 family conjuncts) is real. The only issue: the
conclusion *reads* as if it establishes the bridge/memory facts when it merely
passes them through. Fix = stop echoing them (S9). Harmless, removable.

## Real soundness coverage is 54/63, not 63

`h_known_bugs : NoKnownDefect env` is provably `False` on signed
MUL/MULH/MULHSU and signed DIV/DIVW/REM/REMW, so those 7 arms close vacuously —
soundness makes NO claim there. Invisible from a green build (→ S9 adds checked
`example`s exhibiting the satisfiable defect shape). These are real ZisK circuit
defects (one has a Docker repro, codygunton/zisk#5).

## The 3 soundness assumptions — conditional hypotheses, correctly passed as args

In Lean a hypothesis is either a function argument (theorem is conditional on it)
or derived. These ARE function arguments — the right design. "Is anything proven
about them?" = "does any caller supply a real proof, discharging them?" Answer:
**no, not in the build `lake build` certifies.** Each has *reduction* scaffolding
(off the global theorem's path) that factors it into a crisp residual:

- `aeneasBridgeTrust` — per-arm concrete decoded Main-AIR column values (e.g. BEQ:
  `is_external_op=1 ∧ op=OP_EQ ∧ m32=0 ∧ set_pc=0 ∧ store_pc=0 ∧ jmp_offset2=4`).
  Reduction: `*OfExtractedShape` + `RowProvenance` pin-lemmas prove it follows
  from a `MainRowProvenance` whose `extractedRow` fields match. Residual = "the
  Aeneas decoder emitted such a row" — assumed; the decoder is **proven elsewhere
  (Aeneas Lean) but not imported** (4.28-vs-4.30 toolchain split); checked by the
  external `check-aeneas-*` gates. **Gap kind: LINKAGE.**
- `memoryTimelineConstructionEvidence` — loads only (`True` on 56 arms): a
  generated mem-replay trace contains the read row, prefix-aligned. Reduction:
  `loadMemoryTimelineEvidence_of_constructionEvidence` (axiom-clean) yields the
  timeline evidence the load cores need. Residual = the replay-trace existential
  (`GeneratedMemReplayFacts` + alignment); the would-be producer
  (`FullWitnessGeneratedTimelineEvidence`) bottoms out in assumed generated-row
  facts and the whole-execution replay induction **does not exist**. **Gap kind:
  OPEN PROOF.**
- `NoKnownDefect` — claim-WEAKENING (the 54/63 carve-out), not a discharge.

Non-vacuity: the antecedents are satisfiable (concrete column values; a real
replay existential), so the theorem is a genuine conditional, not vacuous — but
that's argued only in prose today (→ S9 adds inhabitation `example`s to make it
machine-checked).

## Completeness honesty

The standalone `zisk_riscv_completeness` is a typed contract (uninstantiated
Interface; 6 external obligations) — NOT a proof of ZisK completeness. The real
witness construction is the separate Clean per-AIR `completeness` (Part I). The
"Soundness"-named completeness predicates implied a Lean tie that does not exist
(→ fixed in S3: `SoundnessInput → RowInput`, `ziskRowInputAvailable` + INFORMAL
docstring).

---

# Part III — Naming decisions (finalized vocabulary)

| current | → | note / status |
|---|---|---|
| `rv64im_completeness` | `zisk_riscv_completeness` | DONE (S3) |
| `Interface.ziskSoundnessInput` | `ziskRowInputAvailable` | DONE (S3) |
| `*SoundnessInput*` family | `*RowInput*` | DONE (S3) |
| soundness `zisk_riscv_compliant_program_bus` | `zisk_riscv_soundness` (file → `Soundness.lean`) | S10 (heaviest gate) |
| `EquivCore/` (real proofs) | `SpecVsCircuit/` | S5 |
| `Compliance.equiv_<OP>` (wrapper) | `<op>_soundness_of_witness` | S6 |
| `OpEnvelope` | `OpcodeWitness` | S11 (deferred) |
| `state_effect_via_channels` / "channel-balance" | `circuitPostState` | S8 |
| `Defects.NoKnownDefect` | `OutsideKnownDefectRegion` | S4 |
| binder `h_known_bugs` | `h_avoid_known_bugs` | S4 (aligns w/ existing `AvoidKnownBugs`) |
| namespace `Trusted` (in `RowShape/`) | `RowShape` | S4 |
| namespace `PackedBitVec` (in `Bits/`) | `Bits` | S4 |
| `OpEnvelope.aeneasBridgeTrust` | `aeneasRowFacts` | S4 — **least sure** (old name already conveys "Aeneas bridge, assumed") |
| `OpEnvelope.memoryTimelineConstructionEvidence` | `loadReplayPrefix` | S4 |

Open micro-decisions (defaults in **bold**):
- `aeneasBridgeTrust → aeneasRowFacts`: **keep proposed**, or leave old name?
- `Compliance` namespace: **keep internal** (rename only file+theorem), or rename
  the 78-file namespace too? (highest churn, low marginal clarity since Top.lean
  already gives clean names.)

Parallel public names confirmed: `zisk_riscv_soundness` / `zisk_riscv_completeness`.

---

# Part IV — Non-goals (explicit)

- Not discharging `aeneasBridgeTrust` (toolchain-blocked import) or
  `memoryTimelineConstructionEvidence` (replay induction open). They stay honest
  conditional hypotheses — named + documented.
- Not fusing soundness + completeness into one theorem.
- Not changing the canonical `equiv_<OP>` count or moving them out of the
  `ZiskFv.Equivalence.<File>.equiv_<OP>` shape the gate pins.

---

# Part V — Gate-coupling map (what each rename must regenerate)

- `zisk_riscv_completeness` side: **gate-free** (only docs reference it).
- 63 canonical `equiv_<OP>`: pinned by NAMESPACE+PREFIX
  (`bin/TrustGate/CanonicalTheorems.lean`; `check-floor.sh ≥63`;
  `check-uniformity.sh`; `check-clean-integration.py`). Files renamable; theorems
  must stay `ZiskFv.Equivalence.<File>.equiv_<OP>`. Merged content → `lemma`s.
- soundness theorem name: backtick Name literal in `bin/TrustGate/Main.lean`
  (2 arms) + `regenerate.sh` heredoc + `baseline-zisk-riscv-compliant.txt` header
  + `theorem-keep-list.txt` + `dead-code-entry-points.txt` + 2
  `trust/consistency/global_theorem_instantiation_{add,ld}.lean` witnesses.
- caller-burden ledgers (`baseline-caller-burden.txt`,
  `baseline-wrapper-caller-burden.txt`) diff on type snippets → ANY rename of a
  referenced type (EquivCore, Trusted, OpEnvelope fields, residuals) needs regen.
- `OpEnvelope` inductive + route constructors pinned in
  `check-clean-integration.py` + `trust/op-envelope-route-constructors.txt`.
- All gate-pinned files are CODEOWNER-protected (`@codygunton`); regen mechanical.

---

# Part VI — Execution checklist + progress

Verification per step: `check-all.sh` (L1, seconds) + `lake build` after every
step; `check-all-semantic.sh` (L2) + baseline regen via `regenerate.sh` after
steps touching theorem shapes/names; commit per step.

- [x] **S0. Baseline** — warm `.lake`; `lake build` green (2.2s); gate L1+L2 green.
- [x] **S1. Front door** — `ZiskFv/Top.lean` (`zisk_riscv_soundness` /
      `zisk_riscv_completeness` + assumption tables + scope + caveats); lead import
      of `ZiskFv.lean`. (commit fcf15bed)
- [x] **S2. Honesty docstrings** — `exec_eq` echoed-hypothesis note; per-binder
      docstrings on the soundness theorem; moved misfiled README. (fcf15bed)
- [x] **S3. Completeness renames (gate-free)** — endpoint → `zisk_riscv_completeness`;
      `SoundnessInput → RowInput`; `ziskRowInputAvailable` + INFORMAL docstring;
      doc refs. (commit 5e452181)
- [ ] **S4. Low-risk semantic renames (ledger regen)** — `PackedBitVec → Bits`;
      `Trusted → RowShape` (drop dead `Transpiler` if unused); `NoKnownDefect →
      OutsideKnownDefectRegion` + binder `h_known_bugs → h_avoid_known_bugs`;
      `aeneasBridgeTrust / memoryTimelineConstructionEvidence → aeneasRowFacts /
      loadReplayPrefix`. Update 2 consistency witnesses; regen caller-burden ledgers.
- [ ] **S5. `EquivCore` → `SpecVsCircuit`** — dir + namespace + imports + per-op
      lemma refs (`equiv_<OP>_of_*` → `<op>_sail_eq_circuit_of_*`). Regen
      `baseline-caller-burden.txt`, `baseline-equiv-axiom-deps.txt`. (high churn)
- [ ] **S6. Wrapper rename** — `Compliance.equiv_<OP>` → `<op>_soundness_of_witness`;
      delete dead And/Or/Xor/Andi/Ori/Xori/Sub wrappers + fix lying comments; regen
      wrapper ledger.
- [ ] **S7. Fuse Equivalence layer** — merge each wrapper's discharge into
      `Equivalence/<Op>.lean` as a local `lemma`; delete emptied Wrappers files;
      canonical `theorem equiv_<OP>` stays gate-pinned. Regen 4 baselines.
- [ ] **S8. `circuitPostState`** — `state_effect_via_channels → circuitPostState`
      (+ bridge); update 49 literal-RHS files + per-family `exec_eq` Props; JAL/AUIPC
      keep `(route.channels)`; add accept-name to `check-uniformity.sh`.
- [ ] **S9. Honesty-shape fix** — split `exec_eq` into `channelBalanceHolds` +
      `trustResidual`; root concludes `channelBalanceHolds` (drop echo arms); bundle
      3 hyps into `SoundnessAssumptions` at Top; add checked witnesses (per-defect
      satisfiable `Blocks` `example`s; `OpcodeWitness`+`SoundnessAssumptions` and
      trivial-`Interface` inhabitation; one `SailDecode` seam). Regen binder +
      closure baselines; update 2 consistency witnesses. (CODEOWNER review)
- [ ] **S10. Soundness rename + file move** — `zisk_riscv_compliant_program_bus →
      zisk_riscv_soundness`; `Compliance.lean → Soundness.lean`. Edit 2 TrustGate
      Name literals + 5 trust artifacts + 2 witnesses; `regenerate.sh`; repoint
      Top.lean. (heaviest gate; CODEOWNER review)
- [ ] **S11. (Deferred/optional)** — `OpEnvelope → OpcodeWitness`; `Airs/AirsClean`
      nesting (`Airs/Extracted` + `Airs/Clean`); dedupe two `OP_ADD` constants; full
      `Compliance` namespace rename.

---

# Part VII — Open architecture questions (for discussion, beyond rename/fuse)

Deeper than the mechanical plan; these are genuine design forks worth talking
through before/while executing S4+:

1. **The two-tree disconnect.** Soundness and completeness share no spine. Leave
   them as two documented siblings (current plan), or invest in a real unifying
   "ZisK implements RV64IM" statement (needs a concrete `Rv.Interface` + an actual
   edge)? What would the target statement even be?
2. **What completeness should be.** Three fragments today (Clean per-AIR
   constructibility / decode-coverage contract / orphaned SailDecode). Is the
   abstract-Interface contract the right shape, or do we commit to building +
   discharging a concrete Interface? Should the per-AIR Clean completeness be
   aggregated into a project-level statement?
3. **`OpEnvelope` as the soundness interface.** A 65-arm sum bundling per-op
   witnesses+promises. Is the sum the right abstraction, or is it scaffolding the
   Endgame `AcceptedTrace → OpEnvelope` work is meant to retire? How does this
   clarification relate to that trajectory (and to the trace-level export already
   on main, #61/#112)?
4. **`Airs` vs `AirsClean`.** Two representations of one AIR set. Inherent, or is
   one migrating to the other (the Clean migration)? Should we commit to one
   representation rather than nest both?
5. **Trust-residual end state.** `aeneasBridgeTrust` (LINKAGE gap — dischargeable
   by importing the Aeneas Lean once the toolchain split is resolved) vs
   `memoryTimeline` (OPEN proof — replay induction). Should the clarification set
   these up for eventual discharge, and how does that interact with the
   `SoundnessAssumptions` bundling (S9)?
6. **Relationship to the Endgame roadmap.** P4 (construction sweep) / P5
   (trace-level export, on main) / P6 (OpEnvelope retirement) already exist. Does
   this clarification serve, conflict with, or reorder that campaign?

---

## Acceptance

Each step: `lake build` green + gate L1 + (where relevant) L2 green, baselines
regenerated + reviewed, committed. End state: a newcomer opens `ZiskFv/Top.lean`,
sees `zisk_riscv_soundness` + `zisk_riscv_completeness` with documented conditional
assumptions + honest scope, and descends ≤2–5 legible levels before detail.
