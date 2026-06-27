#!/usr/bin/env bash
# check-extraction-closure.sh — V2: assert that every declaration under the
# Aeneas extraction-pin namespace
#
#   ZiskFv.Compliance.Extraction.*
#
# has a RAW, UNFILTERED transitive axiom closure (`Lean.collectAxioms`) that is
# a subset of the kernel trust base {propext, Classical.choice, Quot.sound}.
#
# WHY THIS IS NEEDED (PR #160 / eth-act/zisk-fv#111 review finding P2b):
# these declarations import the Aeneas runtime, which carries upstream `sorry`s
# (Std.Slice / String / etc.). Per-theorem `collectAxioms` isolation currently
# keeps those out of each pin theorem's closure, but NOTHING gates it:
#   * the per-theorem axiom-dep baseline (bin/TrustGate/AxiomClosure.lean)
#     FILTERS OUT `sorryAx` and restricts to `ZiskFv.*` names, so it cannot see
#     a leaked external `sorryAx`;
#   * check-no-sorry.sh scans only source text under ZiskFv/.
# This gate is the missing regression check — it FAILS on any leaked external
# `sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler`, or any `ZiskFv.*`
# project axiom, in the extraction-pin family. It does NOT weaken any existing
# check; it adds raw, unfiltered coverage the others deliberately drop.
#
# Requires `lake build` to have run (consumes oleans).
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

exec lake exe trust-gate check-extraction-closure
