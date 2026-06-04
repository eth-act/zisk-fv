{ writeShellApplication, elan, cargo, rustc, protobuf, python3, jq, git
, clang, libclang, gcc, gnumake, nasm, gmp, nix, pkgsCross, aeneas }:

# Top-level test entry point. Single source of truth for "is the
# project green?" Runs every check in dependency order so a clean
# exit means: builds, has zero sorries, every theorem is the right
# shape, and the trust gate is satisfied.
#
# Bootstrap on a fresh clone — must run once before this:
#   nix run .#populate    (~30 min cold; ~seconds warm via Nix store cache)
#
# After that, `nix run .#test` runs the reproducibility checks, the
# production-backed Aeneas extraction harness, and the Lean build. Cold
# generated-Lean checking is dominated by the temporary Aeneas Lake project.

writeShellApplication {
  name = "test";

  # errexit OFF so all four checks run even if one fails; failures
  # are tracked via `overall` and surfaced in the final exit code.
  bashOptions = [ "nounset" "pipefail" ];

  runtimeInputs = [
    elan
    cargo
    rustc
    protobuf
    python3
    jq
    git
    clang
    libclang.lib
    gcc
    gnumake
    nasm
    nix
    pkgsCross.riscv64-embedded.stdenv.cc
  ];

  text = ''
    cd "$(git rev-parse --show-toplevel)" || exit 1

    overall=0

    export CPATH="${gmp.dev}/include''${CPATH:+:$CPATH}"
    export LIBRARY_PATH="${gmp.out}/lib''${LIBRARY_PATH:+:$LIBRARY_PATH}"
    export LIBCLANG_PATH="${libclang.lib}/lib"
    riscv_shims="$(mktemp -d)"
    for tool in gcc ar as ld objdump; do
      ln -s "$(command -v "riscv64-none-elf-$tool")" "$riscv_shims/riscv64-unknown-elf-$tool"
    done
    export PATH="$riscv_shims:$PATH"

    run() {
      local name=$1; shift
      echo "::: $name :::"
      if ! "$@"; then
        echo "❌ $name failed"
        overall=1
      fi
      echo
    }

    # 1. Tool unit tests.
    run "1/7 cargo test" bash -c '
      cargo test --manifest-path tools/pil-extract/Cargo.toml --quiet
    '

    # 2. Production-wrapper equivalence tests. These compare every
    # `aeneas_extract` wrapper against `Riscv2ZiskContext::convert` for the
    # covered single-row opcode surface, preventing extraction shims from
    # drifting into a parallel Rust lowering path.
    run "2/7 zisk-core aeneas_extract tests" bash -c '
      cd zisk/core
      cargo test --lib --features aeneas_extract extraction_starts_match_production_convert_for_single_row_opcodes --quiet
    '

    # 3. Pinned Aeneas extraction harness. This stays outside the main Lean
    # build and checks the production-backed extraction boundary. Generated
    # files are written under build/ and are not checked in.
    run "3/7 Aeneas production extraction harness" bash -c '
      AENEAS_FLAKE="${aeneas}" scripts/aeneas-production-extract.sh
    '

    # 4. Lake build — the FV check. Every theorem typechecks. This is
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
    run "4/7 lake build" env LEAN_NUM_THREADS="''${LEAN_NUM_THREADS:-4}" lake build

    # 5. Trust gate (locality + baseline + forbidden tier1 params +
    # floors + zero-sorry + uniformity lint). See trust/README.md.
    run "5/7 trust gate (V1 syntactic)" trust/scripts/check-all.sh

    # 6. V2 trust-gate semantic checks. Walks the elaborated
    # environment via `lake exe trust-gate`: per-theorem axiom-closure
    # baseline + binder-type forbidden-Names walk. Requires the lake
    # build above to have populated oleans.
    run "6/7 trust gate (V2 semantic)" trust/scripts/check-all-semantic.sh

    # 7. Reproducibility check. The flake.lock pins every input
    # (sail/sail-riscv/zisk/pil2-* sources, nixpkgs revision) by content
    # hash; `nix flake check` verifies the lock matches the flake.
    run "7/7 flake repro" nix flake check --no-build

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
