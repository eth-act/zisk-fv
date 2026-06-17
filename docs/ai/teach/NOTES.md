# Teaching notes — preferences & working state

## Workspace
- Lives **inside the `review` worktree** at `docs/ai/teach/` (user's choice,
  overriding the main-checkout path). Do not touch the project's own
  `STATUS.md` / `docs/ai/plan/` — the teaching state is self-contained here.

## Learner calibration
- **Expert** in Lean 4, formal verification, RISC-V / zkVM domain. Do NOT
  re-teach those.
- **Novice only** about *this repo's* structure — self-rated "just the gist"
  of the top-level pipeline (knows the pieces exist, can't draw the flow).
- Is the **primary author** of the repo (built lightly-supervised with AI).

## Priorities (from kickoff)
1. **Proof structure** — "I have the actual structure of the proofs in mind
   most of all."
2. **Build system + CI** sanity — secondary but explicitly in scope.
- "Everything is on the table" for re-architecting — no part is sacred.

## Teaching style
- Direct, succinct, honest. No wasteful INTRO/SUMMARY framing (global AGENTS.md).
- **No wall-time estimates** anywhere (user finds them wrong + distracting).
- Lessons: Tufte-flavoured, beautiful, printable, self-contained HTML.
- Ground every claim in the real tree + in-repo docs; cite paths. Never
  parametric guesses about this repo.

## Lesson plan (provisional, proofs-first)
- [x] 0001 — The Territory Map (top-down: two arcs + trust gate + build/CI).
- [x] 0002 — One opcode (ADD) end-to-end; layered discharge; promises relocate to OpEnvelope.
- [ ] 0003 — The RHS circuit stack: pilout → pil-extract → Airs vs AirsClean → ZiskCircuit.
- [ ] 0004 — **The three global hypotheses + trust structure** (aeneasBridgeTrust,
      memoryTimelineConstruction, NoKnownDefect) — answers the user's explicit
      "what these hypotheses mean" ask at the global level. Previewed in 0002 §4.
- [ ] (opt) Harder-opcode trace: LD/load, where memory bus + timeline hyps bite.
- [ ] 0005 — Build system & CI sanity (flake/nix derivations, cachix, proofs.yml shape).
- [ ] Reference: module dependency graph (fills a RESOURCES gap).

## Validation discipline (per user, 2026-06-17)
- README/CLAUDE may be stale/overclaimed — VALIDATE every key claim against
  source (read signatures, baselines) before it goes in a lesson. Cite file:line.
- Confirmed stale: `simplification-suggestions.md` (FromTrust→Wrappers).
- Definitive `lake build` still unrun here (build/ + .lake unpopulated).
