set shell := ["bash", "-euo", "pipefail", "-c"]

pilout    := "pil/zisk.pilout"
extracted := "ZiskFv/ZiskFv/Extraction/BinaryAdd.lean"
oracle    := "ZiskFv/ZiskFv/Extraction/BinaryAdd.hand.lean"
main_extr := "ZiskFv/ZiskFv/Extraction/Main.lean"
main_orcl := "ZiskFv/ZiskFv/Extraction/Main.hand.lean"
fixture   := "ZiskFv/ZiskFv/GoldenTraces/Add.lean"
beq_fix   := "ZiskFv/ZiskFv/GoldenTraces/BEQ.lean"
beq_doc   := "docs/fv/archetype-branch.md"
jal_fix   := "ZiskFv/ZiskFv/GoldenTraces/JAL.lean"
jal_doc   := "docs/fv/archetype-jump.md"
ld_fix    := "ZiskFv/ZiskFv/GoldenTraces/LD.lean"
ld_doc    := "docs/fv/archetype-load.md"
sd_fix    := "ZiskFv/ZiskFv/GoldenTraces/SD.lean"
sd_doc    := "docs/fv/archetype-store.md"
arith_extr := "ZiskFv/ZiskFv/Extraction/Arith.lean"
arith_orcl := "ZiskFv/ZiskFv/Extraction/Arith.hand.lean"
mul_fix   := "ZiskFv/ZiskFv/GoldenTraces/MUL.lean"
mul_doc   := "docs/fv/archetype-arith.md"
sllw_fix  := "ZiskFv/ZiskFv/GoldenTraces/SLLW.lean"
sllw_doc  := "docs/fv/archetype-shift.md"

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

# Phase 2 gate: extends Phase 1 with the branch archetype (A1 = BEQ).
# Runs verify-phase1 first as a regression gate, then asserts the
# Phase 2 A1 deliverables are present: BEQ fixture, archetype doc,
# and the Lean build (which already includes Spec.BranchEqual,
# Equivalence.BranchEqual, Tactics.BranchArchetype via package
# default targets).
verify-phase2: verify-phase1
    # Phase 2 A1 deliverables (BEQ): fixture + archetype doc exist.
    test -f {{beq_fix}}
    test -f {{beq_doc}}
    # Phase 2 A2 deliverables (JAL): fixture + archetype doc exist.
    test -f {{jal_fix}}
    test -f {{jal_doc}}
    # Phase 2 A3 deliverables (LD): fixture + archetype doc exist.
    test -f {{ld_fix}}
    test -f {{ld_doc}}
    # Phase 2 A4 deliverables (SD): fixture + archetype doc exist.
    test -f {{sd_fix}}
    test -f {{sd_doc}}
    # Phase 2 A5 deliverables (MUL): Arith extraction diff, fixture,
    # archetype doc exist.
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air Arith \
        --only 2,6,7,8,31,32,33,34,35,36,37,38,40,41,42,43,44,45,46 \
        --output {{arith_extr}}
    diff -w {{arith_extr}} {{arith_orcl}}
    test -f {{mul_fix}}
    test -f {{mul_doc}}
    # Phase 2 A6 deliverables (SLLW): fixture + archetype doc exist.
    test -f {{sllw_fix}}
    test -f {{sllw_doc}}
    # Build the A1 + A2 + A5 + A6 archetype modules explicitly
    # (verify-phase1's `lake build` already covers the full package, but
    # being explicit guards against accidental module-drop regressions
    # in refactors).
    cd ZiskFv && lake build \
        ZiskFv.Spec.BranchEqual \
        ZiskFv.Equivalence.BranchEqual \
        ZiskFv.Tactics.BranchArchetype \
        ZiskFv.GoldenTraces.BEQ \
        ZiskFv.Spec.Jal \
        ZiskFv.Equivalence.Jal \
        ZiskFv.Tactics.JumpArchetype \
        ZiskFv.GoldenTraces.JAL \
        ZiskFv.Airs.MemoryBus \
        ZiskFv.Spec.LoadD \
        ZiskFv.Equivalence.LoadD \
        ZiskFv.Tactics.LoadArchetype \
        ZiskFv.GoldenTraces.LD \
        ZiskFv.Spec.StoreD \
        ZiskFv.Equivalence.StoreD \
        ZiskFv.Tactics.StoreArchetype \
        ZiskFv.GoldenTraces.SD \
        ZiskFv.Extraction.Arith \
        ZiskFv.Airs.Arith.Mul \
        ZiskFv.Spec.Mul \
        ZiskFv.Equivalence.Mul \
        ZiskFv.Tactics.MulArchetype \
        ZiskFv.GoldenTraces.MUL \
        ZiskFv.Spec.Shift \
        ZiskFv.Equivalence.Shift \
        ZiskFv.Tactics.ShiftArchetype \
        ZiskFv.GoldenTraces.SLLW

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
