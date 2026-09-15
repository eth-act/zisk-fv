# Mission: Understand zisk-fv's architecture (in order to re-architect it)

## Why
`zisk-fv` was built in a lightly-supervised way with AI assistance, so its
structure accreted rather than being designed. I need an accurate, first-
principles mental model of how the whole repo fits together so I can
deliberately *re-architect* it — the **proof structure** above all, and
secondarily whether the **build system and CI** are sensible.

## Success looks like
- I can draw the repo from memory along **both verification axes, as co-equals**:
  (1) **Soundness** — the Sail (LHS) / ZisK-circuit (RHS) equivalence arcs meeting
  at the per-opcode equivalence theorems, climbed through the tower to the
  trace-level export; (2) **Completeness** — the `Rv.Interface`-mediated coverage
  arc (`ZiskFv/Completeness/`) climbing to `root_completeness`. I can name every
  major territory on each axis and its job, and explain why the two arcs have
  *different shapes* (soundness fully in-tree; completeness interface-mediated with
  its `iface` hypotheses discharged by the out-of-repo Aeneas harness).
- I can trace one opcode along BOTH axes: up the soundness tower from its Sail spec
  + circuit constraints — including the **new top** (per-opcode sound constructions
  + the trace-level export) — AND through the completeness shape-family ladder that
  asserts that opcode's raw words are covered.
- I can state precisely what a green `lake build` proves on EACH axis, what the
  `trust/` gate adds, the difference between the old "assume an `OpEnvelope`"
  headline and the new "construct it from an accepted trace" headline, and what the
  completeness `iface` hypotheses cost (the in-repo / out-of-repo Aeneas seam).
- I can point to where complexity, coupling, and duplication concentrate, and
  argue concrete re-architecture options with their trade-offs.
- I can judge whether the Nix pipeline and CI are well-shaped.

## Constraints
- Stateful, multi-session learning. **Validate every claim against the actual
  tree** (signatures, baselines) before it enters a lesson — the in-repo prose
  docs (README/CLAUDE) lag the code and overclaim. Cite `file:line`.
- I already know Lean 4, formal verification, and the RISC-V / zkVM domain —
  do **not** re-teach those. The gap is *this repo's* structure.
- No wall-time estimates in any planning artifact.
- The library is under active development: the architecture changes between
  sessions. On each restart, re-validate against the latest `main`.

## Out of scope
- Teaching Lean 4 tactics or FV methodology from scratch.
- The mathematics of the Sail spec or the soundness of the zk proof system.
- Actually performing the re-architecture — understand well enough to *plan* it.
