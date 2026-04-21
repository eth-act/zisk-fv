set shell := ["bash", "-euo", "pipefail", "-c"]

pilout    := "pil/zisk.pilout"
extracted := "ZiskFv/ZiskFv/Extraction/BinaryAdd.lean"
oracle    := "ZiskFv/ZiskFv/Extraction/BinaryAdd.hand.lean"
main_extr := "ZiskFv/ZiskFv/Extraction/Main.lean"
main_orcl := "ZiskFv/ZiskFv/Extraction/Main.hand.lean"
fixture   := "ZiskFv/ZiskFv/GoldenTraces/Add.lean"

# Phase 0 gate: regenerate the BinaryAdd extraction, diff vs. the hand-written
# oracle, then typecheck the Lean package end-to-end.
verify-phase0:
    cargo test --manifest-path tools/zisk-pil-extract/Cargo.toml
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air BinaryAdd --skip-unsupported \
        --output {{extracted}}
    diff -w {{extracted}} {{oracle}}
    cd ZiskFv && lake build

# Phase 1 gate: extends Phase 0 with Main-AIR extraction (ADD-relevant
# subset), the harness-emitted golden-trace fixture, and a full lake build
# including the compositional ADD spec + final equivalence theorem.
verify-phase1:
    # Extractor unit tests (constraint kinds, operand kinds).
    cargo test --manifest-path tools/zisk-pil-extract/Cargo.toml
    cargo test --manifest-path tools/zisk-fv-harness/Cargo.toml
    # Re-extract BinaryAdd (Phase 0 invariant).
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air BinaryAdd --skip-unsupported \
        --output {{extracted}}
    diff -w {{extracted}} {{oracle}}
    # Re-extract the ADD-relevant Main subset and diff against the oracle.
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air Main --only 8,9,15,16,17,18,19,24,30 \
        --output {{main_extr}}
    diff -w {{main_extr}} {{main_orcl}}
    # Regenerate the golden-trace fixture (hard-coded 3 + 5 = 8).
    cargo run --manifest-path tools/zisk-fv-harness/Cargo.toml -- \
        --mode golden --output {{fixture}}
    # Phase 1.5 Track H: opt-in live-mode regeneration + byte-diff against
    # the checked-in fixture. Gated by FV_LIVE=1 because it requires the
    # full ZisK proving stack + a pre-built probe ELF. See
    # tools/zisk-fv-harness/Cargo.toml for environment prerequisites.
    just _maybe_verify_live
    # Full Lean build: Goldilocks → Extraction → Airs → Spec → Equivalence
    # → GoldenTraces.
    cd ZiskFv && lake build

# Internal: run the harness in live mode when FV_LIVE=1 and diff against
# the hard-coded fixture; no-op otherwise. Split out because just's `{{ }}`
# interpolation collides with bash's `${VAR:-default}` inline syntax.
_maybe_verify_live:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ "${FV_LIVE:-0}" = "1" ]; then
        echo "FV_LIVE=1: running harness in live mode"
        cargo run --manifest-path tools/zisk-fv-harness/Cargo.toml \
            --features live -- --mode live --output /tmp/Add.live.lean
        diff {{fixture}} /tmp/Add.live.lean
    fi
