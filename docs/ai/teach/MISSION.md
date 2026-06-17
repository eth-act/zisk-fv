# Mission: Understand zisk-fv's architecture (in order to re-architect it)

## Why
`zisk-fv` was built in a lightly-supervised way with AI assistance, so its
structure accreted rather than being designed. I need an accurate, first-
principles mental model of how the whole repo fits together so I can
deliberately *re-architect* it — the **proof structure** above all, and
secondarily whether the **build system and CI** are sensible.

## Success looks like
- I can draw the repo from memory as **two arcs** — Sail spec (LHS) and ZisK
  circuit (RHS) — meeting at the per-opcode equivalence theorems, and name
  every major territory and its job.
- I can trace one opcode from its Sail spec + circuit constraints up through
  the 3-layer proof tower (`EquivCore` → `Compliance/Wrappers` →
  `Equivalence`) and the per-family dispatchers to the single global theorem.
- I can state precisely what a green `lake build` proves, and what the
  `trust/` gate adds on top of it.
- I can point to where complexity, coupling, and duplication concentrate, and
  argue concrete re-architecture options with their trade-offs.
- I can judge whether the Nix pipeline and CI are well-shaped, and what I'd
  change.

## Constraints
- Stateful, multi-session learning. Ground every claim in the **actual tree +
  in-repo docs** (`CLAUDE.md`, `README.md`, `trust/`, `simplification-suggestions.md`),
  never in parametric guesses.
- I already know Lean 4, formal verification, and the RISC-V / zkVM domain —
  do **not** re-teach those. The gap is *this repo's* structure.
- No wall-time estimates in any planning artifact.

## Out of scope
- Teaching Lean 4 tactics or FV methodology from scratch.
- The mathematics of the Sail spec or the soundness of the zk proof system.
- Actually performing the re-architecture — this mission is to understand the
  structure well enough to *plan* it.
