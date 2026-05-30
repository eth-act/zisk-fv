{ writeShellApplication, elan, cargo, rustc, protobuf, python3, jq, git }:

# Top-level test entry point. Single source of truth for "is the
# project green?" Runs every check in dependency order so a clean
# exit means: builds, has zero sorries, every theorem is the right
# shape, and the trust gate is satisfied.
#
# Bootstrap on a fresh clone — must run once before this:
#   nix run .#populate    (~30 min cold; ~seconds warm via Nix store cache)
#
# After that, `nix run .#test` runs in seconds (modulo lake build).

writeShellApplication {
  name = "test";

  # errexit OFF so all four checks run even if one fails; failures
  # are tracked via `overall` and surfaced in the final exit code.
  bashOptions = [ "nounset" "pipefail" ];

  runtimeInputs = [ elan cargo rustc protobuf python3 jq git ];

  text = ''
    cd "$(git rev-parse --show-toplevel)" || exit 1

    overall=0

    run() {
      local name=$1; shift
      echo "::: $name :::"
      if ! "$@"; then
        echo "❌ $name failed"
        overall=1
      fi
      echo
    }

    # 1. Tool unit tests (extractor + transpiler differential harness).
    run "1/6 cargo test" bash -c '
      cargo test --manifest-path tools/pil-extract/Cargo.toml --quiet
      cargo test --manifest-path tools/transpiler-diff/Cargo.toml --quiet
    '

    # 2. Default Rust-vs-Lean static-transpiler differential pinning.
    run "2/6 transpiler differential pinning" bash -c '
      cargo run --manifest-path tools/transpiler-diff/Cargo.toml --quiet
    '

    # 3. Lake build — the FV check. Every theorem typechecks. This is
    # the load-bearing claim: if `lake build` is green, every per-opcode
    # equivalence theorem (Sail spec = ZisK circuit + bus model) holds.
    #
    # Lake at 5.0 has no -j/jobs flag, but its async build jobs run on
    # Lean's runtime task scheduler, which honors LEAN_NUM_THREADS.
    # threads=4 fits the 32 GB XL runner's budget. CI run 26661855178
    # (2026-05-29, this branch, warm cache) measured peak kernel `used`
    # = 12.4 GiB and MemAvailable = 19 GiB at threads=3, leaving room
    # for a 4th thread. Earlier caps: threads=2 was the original
    # conservative default; threads=4 OOM-killed at ZiskFv.Sail.sd back
    # when sd.lean's elaboration peaked at 42 GiB, before PR #4's
    # layered dsimp+rw refactor cut it to ~8 GiB PSS. Override with
    # LEAN_NUM_THREADS=N at call site for a different cap.
    run "3/6 lake build" env LEAN_NUM_THREADS="''${LEAN_NUM_THREADS:-4}" lake build

    # 4. Trust gate (locality + baseline + forbidden tier1 params +
    # floors + zero-sorry + uniformity lint). See trust/README.md.
    run "4/6 trust gate (V1 syntactic)" trust/scripts/check-all.sh

    # 5. V2 trust-gate semantic checks. Walks the elaborated
    # environment via `lake exe trust-gate`: per-theorem axiom-closure
    # baseline + binder-type forbidden-Names walk. Requires the lake
    # build above to have populated oleans.
    run "5/6 trust gate (V2 semantic)" trust/scripts/check-all-semantic.sh

    # 6. Reproducibility check. The flake.lock pins every input
    # (sail/sail-riscv/zisk/pil2-* sources, nixpkgs revision) by content
    # hash; `nix flake check` verifies the lock matches the flake.
    run "6/6 flake repro" nix flake check --no-build

    if [ $overall -eq 0 ]; then
      echo "================================"
      echo "✅ ALL CHECKS PASSED"
      echo "================================"
    else
      echo "================================"
      echo "❌ SOMETHING FAILED — see above"
      echo "================================"
    fi
    exit $overall
  '';
}
