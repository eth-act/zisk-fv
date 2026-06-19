Stream: P4 OpEnvelope constructions → P5 trace-level export (#61). Worktree p4-mext,
branch p4-loads-stores (stacked on PR #110). build/ symlinked, submodule populated.
Metaplan: docs/ai/plan/PLAN_ENDGAME.md (the home-stretch checklist). Gate V1 18/18 + V2 12/12.

=== P4 SOUND CONSTRUCTIONS: 55/63 — and 55 is the HONEST CAP ===
Committed construction_<op>_sound (derived from trace.balanced + honest residuals,
0 PROJECT ZiskFv.* axioms each):
- 30 ALU/shift/W-ALU/LUI/AUIPC (on main) + 6 unsigned M-ext (PR #110)
- stores SB/SH/SW/SD (387c45e0) → 40   [sub-doubleword carry h_m* preservation = #76]
- loads LB/LH/LW/LD/LBU/LHU/LWU (54a99076) → 47   [carry memoryTimelineEvidence = #76 + providers]
- branches BEQ..BGEU + JAL/JALR (fb259f04) → 55   [carry h_nextPC_matches = #100]

The remaining 8 are DEFECT/GAP-GATED — NOT soundly constructible (honest exclusions,
carried by the global theorem's ∀-env NoKnownDefect / decode-gap):
- signed-M MUL/MULH/MULHSU/DIV/DIVW/REM/REMW (7): PROVEN unconstructible (agent a71dfd4).
  The circuit's signed mul/div is UNSOUND (carry-chain can't rule out the exceptional
  product-shape; a malicious prover can forge — defects.md:48-51). NoKnownDefect is
  intentionally contradictory for these envelopes ⇒ any concrete construction is vacuous.
  A laundered vacuous attempt (carried h_env_defect) was rejected + STASHED (never commit).
- FENCE (1): decode-incompleteness (FenceIncomplete — decoder rejects generic fm≠0 FENCE).

=== NEXT: P5 trace-level export (the real #61 closure) over the 55 ===
SCOPING in flight (agent aeaab17d): map OpEnvelope anatomy + the residual inventory +
the decode→dispatch + the target theorem signature that derives the OpEnvelope from the
trace (removing the OpEnvelope param), with the 8 gated covered by the existing NoKnownDefect.

=== SIBLING THREADS ===
- #111 (aeneasBridgeTrust discharge): BLOCKED — sound in-build discharge is NO-GO (numBits/
  irreducibility wall; native_decide gate-forbidden). Needs a route decision (a: large
  symbolic effort / b: native_decide trust-policy [advised against] / c: keep loose coupling).
- #76 (h_memory_timeline): PR-76.5 step D landed on p76-memory (cross-segment seam, GO);
  E/F/G + per-address timeline remain. Discharges loads' + stores' #76 residuals.

GOAL NOTE: the /goal says "ALL 63" — unachievable (8 are defect/gap-gated). Re-scope to
"the 55 constructible + 8 honestly excluded via NoKnownDefect; P5 over the 55."
