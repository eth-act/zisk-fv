set shell := ["bash", "-euo", "pipefail", "-c"]

pilout    := "pil/zisk.pilout"
extracted := "ZiskFv/ZiskFv/Extraction/BinaryAdd.lean"
oracle    := "ZiskFv/ZiskFv/Extraction/BinaryAdd.hand.lean"

# Phase 0 gate: regenerate the extraction, diff vs. the hand-written oracle,
# then typecheck the Lean package end-to-end.
verify-phase0:
    cargo test --manifest-path tools/zisk-pil-extract/Cargo.toml
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air BinaryAdd --skip-unsupported \
        --output {{extracted}}
    diff -w {{extracted}} {{oracle}}
    cd ZiskFv && lake build
