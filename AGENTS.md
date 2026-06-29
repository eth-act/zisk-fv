# zisk-fv Agent Guide

This file is the project-specific operating guide for agents. Keep it concise: put durable rules
here, and point to source-of-truth docs for details that change as the proof changes.

## Goal

`zisk-fv` formalizes the RV64IM part of ZisK against the Sail RISC-V specification in Lean 4.

The long-term shape is two root theorems:

- soundness: every modeled ZisK state transition accepted by the constraints is a valid Sail/RISC-V
  transition;
- completeness: every in-scope Sail/RISC-V transition is accepted by the modeled ZisK constraints,
  with known defects and scope exclusions explicit in the theorem statement.

The current public soundness endpoint is `ZiskFv.Compliance.root_soundness` in
`ZiskFv/Soundness.lean`. This is more more developed and mature than the completeness theorem.
`ZiskFv.Compliance.zisk_riscv_compliant_program_bus` is the older global channel-balance theorem
that the trace-level export can consume; do not present it as the headline root theorem. The
checked-in acceptance/coverage endpoints live in `ZiskFv/Completeness.lean`. If this file and
`README.md` or `trust/README.md` disagree, trust the Lean statements first, then update the stale
docs.

## First Steps

- Inspect the worktree before editing. Preserve user changes, including dirty files unrelated to
  your task.
- Read narrowly. Start with the file you will touch, nearby code, `README.md`, and any specialized
  doc named below. Do not preload large historical notes and be skeptical--these are likely stale.

## Stable Architecture

The stable pipeline is:

1. `flake.lock` pins upstream Sail, sail-riscv, ZisK, PIL tooling, and nixpkgs.
2. `nix run .#populate` creates the generated inputs under `build/`.
3. `tools/pil-extract` turns the pinned PIL output into generated Lean constraints under
   `build/extraction/Extraction/`.
4. Human-maintained Lean code under `ZiskFv/` gives those generated artifacts proof-facing names,
   semantics, and theorems.
5. `trust/` records and checks the proof's trust boundary.

Treat `build/` as generated. Do not hand-edit generated Lean, pilout, Sail output, or Aeneas
extraction output. Change the generator or source input, then rerun the producing command.

Prefer stable contracts over file-by-file lore. Before citing counts, opcode sets, check totals, or
generated ledger contents, confirm them from the current tree.

## Development Rules

- Keep diffs local to the requested change. Match surrounding Lean/Rust/shell style instead of
  imposing a new one.
- Do not introduce pass-through layers. A new module or record should own a real invariant, proof
  obligation, or data boundary.
- Avoid new names like "bridge" or "wrapper" for vague adapters. Existing directories with those
  names are historical; new code should name the invariant or transformation it proves.
- Do not change protected proof interfaces without explicit permission: public theorem statements,
  `OpEnvelope`-style dispatch surfaces, extraction interfaces, trust policy files, and `Valid_<AIR>`
  validator fields.
- `Valid_<AIR>` constraints must mirror actual generated/PIL constraints. Any strengthening needs a
  source citation and a constructibility argument showing how a real trace can provide it.
- Prefer deriving facts from existing validators, generated rows, or proved lemmas over adding
  parameters. New caller-supplied hypotheses are a trust cost, not harmless plumbing.
- Commit semantically meaningful completed chunks, but never include secrets or unrelated dirty
  files.

## Anti-Laundering

Laundering means making apparent progress while the proof obligation has only been moved, renamed,
weakened, hidden, or transferred into trust. Treat it as a proof failure, not as a partial win.

Rules:

- Do not replace a proof obligation with a renamed assumption, a broader public premise, an
  overstrong validator, a hidden top-level definition, an allowlist edit, or a theorem weakening and
  then describe it as discharged.
- Do not expand trust to close work unless the task is explicitly to change the TCB. That includes
  adding `axiom`, `opaque`, `constant`, `unsafe`, `partial`, `@[extern]`, `@[implemented_by]`,
  `sorry`, `admit`, new `native_decide`, generated-ledger suppressions, or equivalent escape hatches.
- Do not claim issue progress for moving text between issue bodies, opening child issues, changing
  dependency edges, labels, or milestones, or splitting scope. Those are bookkeeping actions unless
  the corresponding Lean proof, extraction, generated artifact, or trust-ledger reduction actually
  landed.
- Do not move hard proof work into another issue, mark the current issue blocked, close it as
  superseded, or otherwise change tracking to avoid implementing the requested proof without
  explicit owner permission.
- When a proof attempt exposes a missing invariant, prove or expose the invariant in the current
  workstream by default. If changing scope might be necessary, stop and ask before mutating issues
  or reframing the deliverable.
- Progress reports must distinguish clearly between proved facts, code changes, verified gates,
  issue bookkeeping, and hypotheses still being investigated.

## Trust Boundary

For any change touching trust, theorem assumptions, generated artifacts, completeness claims, or
extraction boundaries, read:

- `trust/README.md` for workflow and current ledger state;
- `trust/trusted-base.md` for the narrative trust ledger;
- `trust/defects.md` for known bugs and theorem exclusions.

Rules:

- Do not add `axiom`, `opaque`, `constant`, `unsafe`, `partial`, `@[extern]`, `@[implemented_by]`,
  `sorry`, `admit`, or equivalent trust markers unless the task is explicitly to change the TCB.
- Do not expand use of `native_decide` without explicit permission. Existing uses are part of the
  current proof/trust surface; new uses need review.
- Promise discharge must reduce caller-supplied trust. Do not replace one assumption with a renamed
  assumption, a stronger universal assumption, an overstrong validator, a hidden top-level
  definition, or an axiom of the same shape.
- If the trust boundary intentionally changes, update the Lean declaration, generated ledgers, and
  `trust/trusted-base.md` together. Known defect changes must update `trust/defects.md` and the
  theorem claim boundary together.
- Do not edit allowlists or forbidden-shape files to silence a gate. Fix the proof or get explicit
  approval for a trust-boundary change.

## Build And Test

Bootstrap generated inputs after a fresh clone or relevant input change:

```bash
nix run .#populate
```

Fast proof-development loop:

```bash
lake build <target>
```

Standard gates before claiming a proof-bearing chunk:

```bash
lake build
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
```

Full repository gate:

```bash
nix run .#test
```

`lake build` is the formal-verification check. The fast trust gate does not need oleans; the
semantic trust gate does and should be run after `lake build`. Docs-only changes do not require a
Lean build unless they affect executable examples, generated artifacts, or commands.

Use focused checks while iterating, then run the broader gate after a coherent proof or
trust-boundary change. Prefer fixing verification failures over working around them.

## Lean Guidance

- Use Lean diagnostics, goal state, local search, and small target builds before broad rebuilds.
- Do not shadow the global `[Field FGL]` instance with a proof-local variable; it can break `ring`.
- For carry-chain arithmetic, keep large coefficients in the factored form used by nearby proofs.
  `ring` may treat equal numeric literals with different syntax as different atoms.
- Over `Fin p`, `(1 - 0) * x` does not always simplify the way it looks. Check nearby established
  lemmas before forcing a normalization path.
- For operation-bus composition, prefer the maintained predicates under
  `ZiskFv/Airs/OperationBus.lean` instead of reviving retired interaction modules.

## Documentation Map

- `README.md`: current project overview, public theorem endpoints, build commands, and layout.
- `trust/README.md`: trust workflow, generated ledgers, and PR policy.
- `trust/trusted-base.md`: human-readable trust ledger.
- `trust/defects.md`: known defects and theorem-scope exclusions.
- `docs/extraction/`: extractor and AIR orientation notes.
- `nix/README.md`, `flake.nix`, `flake.lock`: reproducible build inputs and commands.
- `docs/ai/PROJECTS.md` and `docs/ai/plan/`: agent workstream index and plans.

Historical docs removed from the tree should be recovered with `git show` only when needed for the
current task; do not paste old plans back into active instructions.

## Issue Dependency Graph

GitHub structured issue relationships are the source of truth for dependencies; issue prose is only
audit evidence.

- Use `blockedBy` only for strict prerequisites: issue A is blocked by issue B when A cannot be
  implemented, proved, or verified until B is done.
- Use parent/sub-issue relationships for grouping, not dependency edges, unless the same pair also
  has a real `blockedBy` relationship.
- Query node IDs and current links before mutating relationships. Do not run speculative mutations.
- The only visual graph is the generated body of the GitHub issue titled `Issue dependency graph`;
  do not add a checked-in Mermaid graph.
- For an immediate refresh, run:

```bash
python3 scripts/update_issue_deps_graph.py \
  --owner eth-act \
  --repo zisk-fv \
  --issue-title "Issue dependency graph" \
  --update
```
