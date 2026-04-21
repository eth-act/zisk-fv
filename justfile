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
    # Regenerate the golden-trace fixture.
    cargo run --manifest-path tools/zisk-fv-harness/Cargo.toml -- \
        --output {{fixture}}
    # Full Lean build: Goldilocks → Extraction → Airs → Spec → Equivalence
    # → GoldenTraces.
    cd ZiskFv && lake build
