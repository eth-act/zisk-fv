# zisk-fv Architecture Resources

The "knowledge" for this mission is *the repo itself* plus its own high-trust
in-repo docs. Paths are relative to the repo root
(`/home/cody/zisk-fv/.worktrees/review`).

## Knowledge — primary (in-repo, highest trust)

- [`README.md`](../../../README.md) — §Layout + §Pipeline.
  The canonical human-facing overview: the verification claim, the build
  commands, the path table, and the generation pipeline diagram. **Read first.**
- [`CLAUDE.md`](../../../CLAUDE.md) — §Pipeline + §Trust gate + §Conventions.
  The deepest single source on the proof tower (the 7-stage flow), the trust
  gate's two layers, and the anti-laundering principle. Dense; use as reference.
- [`simplification-suggestions.md`](../../../simplification-suggestions.md) —
  The in-repo **re-architecture backlog**, ranked by leverage. Some items are
  shipped (see §Shipped) and some vocabulary is stale (e.g. `FromTrust/` is now
  `Wrappers/`), but it is the single most mission-relevant document: it names
  the structural seams the original author already saw.
- [`trust/README.md`](../../../trust/README.md) — Full reference for the trust
  gate scripts + baseline files, and the anti-laundering glossary.
- [`trust/trusted-base.md`](../../../trust/trusted-base.md) — Human-readable
  trust ledger; pairs with `trust/generated/baseline-axioms.txt`.
- [`trust/defects.md`](../../../trust/defects.md) — The known-defect ledger the
  global theorem carves out (`Defects.NoKnownDefect`). Read to understand what
  "compliant" excludes — the ZisK v0.17.0 bugs this repo surfaced.
- [`docs/extraction/extractor-notes.md`](../../../docs/extraction/extractor-notes.md)
  + [`docs/extraction/air-inventory.md`](../../../docs/extraction/air-inventory.md)
  — Durable contract for `tools/pil-extract` and the 22-AIR inventory.
- [`nix/README.md`](../../../nix/README.md) — What each Nix derivation produces
  and why. Read for the build-system half of the mission.
- The tree itself: `ZiskFv.lean` (the module root / import manifest),
  `lakefile.toml` (dependency graph), `.github/workflows/{proofs,trust-gate}.yml`.

## Knowledge — external (upstream context)

- [ZisK](https://github.com/0xPolygonHermez/zisk) — the zkVM under verification
  (pinned at v0.17.0). Use for: what the RHS circuit actually computes.
- [Sail RISC-V](https://github.com/riscv/sail-riscv) — the LHS reference spec.
- [Lean 4 / Lake docs](https://lean-lang.org/lean4/doc/) + Mathlib — for
  build-graph and module-organization idioms (not for the math).

## Wisdom (Communities)

- [Lean Zulip](https://leanprover.zulipchat.com) — `#general` /
  `#lean4` / `#mathlib4`. High-signal. Use for: project-structure / Lake /
  large-build-organization questions, sanity-checking a re-architecture.
- Note: you are the *primary author* of this repo, so the "wisdom" gap is
  smaller than usual — much of it is recovering intent you encoded earlier.

## Gaps
- No single document maps the **module dependency graph** (what imports what)
  beyond `ZiskFv.lean`'s flat import list. A generated import-graph would be a
  high-value artifact for the re-architecture decision — candidate for a future
  lesson/reference.
- The relationship between `ZiskFv/Airs/` (op-bus model, 32 files) and
  `ZiskFv/AirsClean/` (Clean-DSL ensemble, 73 files) is not documented in one
  place; understanding it is a likely re-arch pivot.
