# zisk-fv Architecture Resources

The "knowledge" for this mission is *the repo itself*. Pinned to `main @ e731db56`.
Paths are relative to the repo root (`/home/cody/zisk-fv`).

## ⚠️ Stale-doc warning (validated 2026-06-22)
The in-repo narrative docs **lag the code** and overclaim. Both `README.md` and
`CLAUDE.md` still name `zisk_riscv_compliant_program_bus` as "the verification
claim" and say **nothing** about the construction layer or the trace-level
export added in #110/#112. Use them as orientation, then verify against the tree.

## Knowledge — primary (in-repo)

- The tree itself — the ground truth. Key files:
  - [`ZiskFv/Compliance/TraceLevelExport.lean`](../../../ZiskFv/Compliance/TraceLevelExport.lean)
    — the **new headline** (`root_soundness`); its
    docstring is the clearest statement of the new top.
  - [`ZiskFv/Compliance.lean`](../../../ZiskFv/Compliance.lean) — the old global
    theorem `zisk_riscv_compliant_program_bus` (`:95`).
  - `ZiskFv/Compliance/Construction*.lean` (20 modules) — the per-opcode sound
    constructions.
  - `ZiskFv.lean` (import manifest), `lakefile.toml` (deps).
- [`README.md`](../../../README.md) / [`CLAUDE.md`](../../../CLAUDE.md) — overviews;
  **stale** on the new top (see warning above). Still good for the pipeline,
  trust-gate, and conventions.
- [`trust/README.md`](../../../trust/README.md) + `trust/trusted-base.md` +
  `trust/generated/baseline-*.txt` — the trust gate and its baselines, incl. the
  new `baseline-strong-export-*.txt` and `baseline-construction-theorem-binders.txt`.
- [`trust/defects.md`](../../../trust/defects.md) — the known-defect carve-out
  (incl. the DIV/REM signed remainder-bound bug the project found).
- [`docs/extraction/extractor-notes.md`](../../../docs/extraction/extractor-notes.md)
  + [`docs/extraction/air-inventory.md`](../../../docs/extraction/air-inventory.md)
  — the `pil-extract` contract and the 22-AIR map.
- [`nix/README.md`](../../../nix/README.md) — the build derivations.

## Knowledge — external
- [ZisK](https://github.com/0xPolygonHermez/zisk) (v0.17.0) — the zkVM under verification.
- [Sail RISC-V](https://github.com/riscv/sail-riscv) — the LHS reference spec.
- [Lean 4 / Lake docs](https://lean-lang.org/lean4/doc/) — build-graph idioms.

## Wisdom (Communities)
- [Lean Zulip](https://leanprover.zulipchat.com) — project-structure / large-build
  organization questions. You are the primary author, so the wisdom gap is small.

## Gaps
- No single doc maps the module dependency graph — a generated import-graph would
  be a high-value re-architecture artifact (candidate reference doc).
- The `Airs/` vs `AirsClean/` relationship is undocumented in one place.
- The new top (construction + trace-level export) is documented only in the
  `TraceLevelExport.lean` docstring — not in README/CLAUDE.
