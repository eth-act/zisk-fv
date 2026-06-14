# CI runtime investigation

Goal: reduce the `proofs` workflow wall clock after run 27457939944 reached
~2.5h, without weakening the formal gate that runs on `main`.

## Findings

- [x] Run 27457939944 spent 2h22m56s inside `nix run .#test`.
- [x] Internal markers: Aeneas production extraction 1h34m15s, `lake build`
  40m53s, V2 semantic trust gate 4m39s.
- [x] Historical successful runs show Aeneas is a stable ~1.5h fixed cost;
  recent growth is mostly `lake build` rising from ~14m to ~41m after the
  Clean completeness waves.
- [x] Memory was not the limiting resource for the successful run: max kernel
  used memory was ~9.1GiB on the 16GiB runner, with `LEAN_NUM_THREADS=4`.
- [x] Split the independent Aeneas production extraction check out of the main
  serialized `nix run .#test` path in CI.
- [x] Cache the temporary Aeneas `lean-check/.lake` build directory.
- [x] Keep plain local `nix run .#test` as the full all-in-one gate by default.
- [x] Verify workflow/Nix syntax.
- [x] Commit the CI speedup branch.
- [x] Push/open PR (#92).
- [ ] Compare the first split CI run wall time after merge or manual dispatch.

## Log

- 2026-06-14: started from current `origin/main` in
  `.worktrees/ci-proofs-parallel-aeneas` on branch `ci/proofs-parallel-aeneas`.
- 2026-06-14: implemented CI split: `ZISK_FV_TEST_SKIP_AENEAS=1` in the
  Lake/trust job only, a parallel hosted Aeneas job running
  `AENEAS_CHECK_RV_COMPLETENESS=1 nix run .#aeneas-production-extract`, and an
  Actions cache for `build/aeneas-production-extraction/lean-check/.lake`.
  Verified with YAML parse, `git diff --check`, `nix flake check --no-build`,
  and `bash -n` on the generated Nix app wrappers.
- 2026-06-14: committed the speedup branch locally as `ci/proofs-parallel-aeneas`;
  pushed and opened PR #92.
