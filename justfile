set shell := ["bash", "-euo", "pipefail", "-c"]

pilout    := "build/zisk.pilout"
extracted := "ZiskFv/Extraction/BinaryAdd.lean"

# Helper: assert the pilout has been built locally. The pilout is no
# longer vendored — it is a Docker-built artifact (see repro/README.md).
# First-time setup: `repro/build-pilout.sh` (~6 min, persists in build/).
_assert_pilout:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -f "{{pilout}}" ]; then
        echo "❌ {{pilout}} not found." >&2
        echo "" >&2
        echo "The pilout is no longer vendored in the repo — it is a" >&2
        echo "Docker-built artifact. Run once before any verify-phase*:" >&2
        echo "" >&2
        echo "    repro/build-pilout.sh" >&2
        echo "" >&2
        echo "Takes ~6 min, persists in build/. See repro/README.md." >&2
        exit 1
    fi
oracle    := "ZiskFv/Extraction/BinaryAdd.hand.lean"
main_extr := "ZiskFv/Extraction/Main.lean"
main_orcl := "ZiskFv/Extraction/Main.hand.lean"
fixture   := "ZiskFv/GoldenTraces/Add.lean"
beq_fix   := "ZiskFv/GoldenTraces/BEQ.lean"
beq_doc   := "docs/fv/archetype-branch.md"
jal_fix   := "ZiskFv/GoldenTraces/JAL.lean"
jal_doc   := "docs/fv/archetype-jump.md"
ld_fix    := "ZiskFv/GoldenTraces/LD.lean"
ld_doc    := "docs/fv/archetype-load.md"
sd_fix    := "ZiskFv/GoldenTraces/SD.lean"
sd_doc    := "docs/fv/archetype-store.md"
arith_extr := "ZiskFv/Extraction/Arith.lean"
arith_orcl := "ZiskFv/Extraction/Arith.hand.lean"
mul_fix   := "ZiskFv/GoldenTraces/MUL.lean"
mul_doc   := "docs/fv/archetype-arith.md"
sllw_fix  := "ZiskFv/GoldenTraces/SLLW.lean"
sllw_doc  := "docs/fv/archetype-shift.md"

# Phase 0 gate: regenerate the BinaryAdd extraction, diff vs. the hand-written
# oracle, then typecheck the Lean package end-to-end.
verify-phase0: _assert_pilout
    cargo test --manifest-path tools/pil-extract/Cargo.toml
    cargo run --manifest-path tools/pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air BinaryAdd --skip-unsupported \
        --output {{extracted}}
    diff -w {{extracted}} {{oracle}}
    lake build

# Phase 1 gate: extends Phase 0 with Main-AIR extraction (ADD-relevant
# subset), the harness-emitted golden-trace fixture, and a full lake build
# including the compositional ADD spec + final equivalence theorem.
verify-phase1: _assert_pilout
    # Extractor unit tests (constraint kinds, operand kinds).
    cargo test --manifest-path tools/pil-extract/Cargo.toml
    cargo test --manifest-path tools/golden-traces/Cargo.toml
    # Re-extract BinaryAdd (Phase 0 invariant).
    cargo run --manifest-path tools/pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air BinaryAdd --skip-unsupported \
        --output {{extracted}}
    diff -w {{extracted}} {{oracle}}
    # Re-extract the ADD/branch/jump-relevant Main subset and diff against the
    # oracle. Constraint 20 (PC handshake) was added in Phase 2.5 D2 after
    # the extractor learned to handle PIL's negative row-rotation postfix.
    cargo run --manifest-path tools/pil-extract/Cargo.toml -- \
        --pilout {{pilout}} --air Main --only 8,9,15,16,17,18,19,20,24,30 \
        --output {{main_extr}}
    diff -w {{main_extr}} {{main_orcl}}
    # Regenerate the golden-trace fixture (hard-coded 3 + 5 = 8).
    cargo run --manifest-path tools/golden-traces/Cargo.toml -- \
        --mode golden --output {{fixture}}
    # Phase 1.5 Track H: opt-in live-mode regeneration + byte-diff against
    # the checked-in fixture. Gated by FV_LIVE=1 because it requires the
    # full ZisK proving stack + a pre-built probe ELF. See
    # tools/golden-traces/Cargo.toml for environment prerequisites.
    just _maybe_verify_live
    # Full Lean build: Goldilocks → Extraction → Airs → Spec → Equivalence
    # → GoldenTraces.
    lake build

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
    cargo run --manifest-path tools/pil-extract/Cargo.toml -- \
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
    lake build \
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

# Phase 4 / 4.5 gate: bundles the Phase 4 closure invariants. Runs
# verify-phase2 first as a regression gate, then asserts:
#
#   V1. `lake build` of the full package is green (inherited from
#       verify-phase2's `lake build`).
#   V3. Zero sorry in ZiskFv (excluding auto-generated Extraction which
#       intentionally stubs permutation-argument columns).
#   V8. Uniformity lint passes: 58 opcodes with `equiv_<OP>_metaplan`
#       of the canonical shape.
#
# The V2 "just verify-phase4 exits 0" invariant is this recipe itself
# being green. Gates V4–V7 and V9–V11 are opcode-family-specific and
# are tracked in `ai_plans/zisk-fv-phase-4-5.md` directly.
verify-phase4: verify-phase2
    # V3: zero sorry in Fundamentals/Airs/Spec/Equivalence/GoldenTraces.
    # (Extraction/ is auto-generated and stubs permutation-argument
    # columns; those stubs are not called by the compositional proofs.)
    ! grep -rn "sorry" ZiskFv/Fundamentals ZiskFv/Airs \
        ZiskFv/Spec ZiskFv/Equivalence \
        ZiskFv/GoldenTraces 2>/dev/null | \
        grep -v "^[^:]*:[^:]*:--" | grep -v "^[^:]*:[^:]*:///"
    # V8: uniformity lint (58 opcodes, all with canonical metaplan shape).
    bash trust/scripts/check-uniformity.sh > /dev/null

# Internal: run the harness in live mode when FV_LIVE=1 and diff against
# the hard-coded fixture; no-op otherwise. Split out because just's `{{ }}`
# interpolation collides with bash's `${VAR:-default}` inline syntax.
_maybe_verify_live:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ "${FV_LIVE:-0}" = "1" ]; then
        echo "FV_LIVE=1: running harness in live mode"
        cargo run --manifest-path tools/golden-traces/Cargo.toml \
            --features live -- --mode live --output /tmp/Add.live.lean
        diff {{fixture}} /tmp/Add.live.lean
    fi
