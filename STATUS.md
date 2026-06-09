Active plan: docs/ai/plan/PLAN_AXIOM_WEAKENING.md
Current focus: Step 1 verification is green; preparing commit and PR.
Blocking: none.
Next step: review diff, commit, push `axiom-weakening`, and open the PR.
Digression: scope check requested; current read is bounded plumbing, not a
redesign, but it necessarily touches the shared load promise bundle and the 7
load call paths.

Recent state:
- Created branch/worktree `axiom-weakening` from current `origin/main`
  (`ef4df58b Add Lean REPL dependency`).
- `nix run .#populate` restored local `build/sail-lean` and `build/clean-lean`
  dependencies after the first cache attempt exposed the missing local path.
- `lake exe cache get` passed.
- The active plan file was local-only in the parent checkout, so this branch now
  carries `docs/ai/plan/PLAN_AXIOM_WEAKENING.md`.
- `trust/consistency/probe_false.lean` compiles before the repair and derives
  `False` with axiom closure containing
  `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load`.
- `trust/scripts/check-all-semantic.sh` now requires that probe to be rejected.
- `lake build` passed after replacing `aeneas_bridge_trust env` with explicit
  `h_bridge : env.aeneasBridgeTrust` and deleting the Aeneas axiom.
- Direct closure print now contains only
  `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load`.
- `row_models_sail_state_load` has been deleted; `MemModel` now repackages
  explicit byte facts, and the 7 load core modules build with the new
  `LoadPromises.mem_read` field.
- Full `lake build` passed after memory demotion.
- `trust/consistency/probe_false.lean` is rejected, and direct closure printing
  for `zisk_riscv_compliant_program_bus` now returns no project axioms.
- `trust/scripts/check-no-output-eq.sh` passed; the new byte-agreement promise
  is not a forbidden output-equality shape.
- Generated ledgers now report 6 source trust declarations and 0 project
  axioms in the global compliance closure.
- Trust docs now describe Aeneas as an explicit theorem hypothesis and memory
  agreement as `LoadPromises.mem_read`; a positive byte-agreement witness is
  wired into the semantic gate.
- `trust/scripts/check-all-semantic.sh`, `trust/scripts/check-all.sh`,
  `lake build`, and `nix run .#test` all passed. The false probe is rejected,
  and the global compliance project-axiom closure is empty.
