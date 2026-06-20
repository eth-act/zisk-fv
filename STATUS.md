Stream: Uniform-63 OpEnvelope-route export (#61 endgame). Worktree p4-mext,
branch p4-loads-stores (PR #112, stacked on PR #110). Metaplan: docs/ai/plan/PLAN_ENDGAME.md.
Gate V1 18/18 + V2 12/12 throughout. 0 new ZiskFv.* axioms.

=== RESULT: 57/63 on the OpEnvelope-route — the honest proof-layer cap (head 03fb00ea) ===
zisk_compliant_of_accepted_trace_strong: for 57 opcodes, construct OpEnvelope.<op> from the
trace + invoke zisk_riscv_compliant_program_bus + thread h_known_bugs. NO OpEnvelope input
(takes rowData). Non-vacuous, NO main-theorem refactor (canonical/OpEnvelope/old-theorem intact).
Built from the trace via mainConstVar/memConstVar (eval-provenance) + the trace-Environment
lookup-witness pattern. 57 = 49 non-defect (ALU/shifts/W-ALU/W-shifts/branches/JAL-JALR/LUI/AUIPC/
unsigned-M/stores/loads) + FENCE + MUL.

Commits (10, on top of e3a71967): ba8b61d1 thread h_known_bugs · debd3bd7 (a) M-ext de-vacuity
(tight <131072→faithful <983041; SOUNDNESS FIX) · 141b44fe branches+JALR · 7cf4c280 6 M-ext ·
55cbc02e LUI/AUIPC/JAL · 009123ee W-shifts+stores · e8264ff3 7 loads · 8b763d61 FENCE ·
8b541c46 (iii) MUL defect retired opcode-wide→exact forge (SOUNDNESS FIX) · 03fb00ea MUL trace-arm.

=== 6 signed-M genuinely blocked (NOT proof laziness — documented boundaries) ===
- MULH/MULHSU (2): EXTRACTION-FIDELITY gap. The REAL circuit IS sound — it pins na=MSB
  (arith.pil:286/289/303 indexed range lookup POS/NEG on a[3]); honest na: arith_operation.rs:487.
  But the FV model collapses the indexed lookup to FULL rangeTable16 (<2^16) and doesn't compose
  ArithRangeTable into balance, so na=MSB is unprovable in-model. Corrects defects.md's "genuinely
  unsound" framing — it's an extraction-scope gap, not unsoundness. Unblock = deep extraction work.
- DIV/DIVW/REM/REMW (4): GENUINE circuit bug LT_ABS_NP |a|=|b| (codygunton/zisk#5). Compliance is
  FALSE for |a|=|b|, not just unproven. Needs upstream circuit fix. (Witness-conditional retirement
  excluding |a|=|b| would also need the signed-range extraction, same scope as MULH/MULHSU.)
Literal "all 63 for all inputs" is impossible (the DIV/REM bug). Ceiling = all-63-ARMS with
witness-conditional defects, gated on the extraction-fidelity work + the upstream fix.

=== Deferred ===
- (d) memory reduction: STASHED (git stash). Fold-B port reduced loads' h_memory_timeline →
  RowTraceCoherence but reverted loads to direct-lift (old theorem wants whole-state evidence).
  Proper (d) needs the old-theorem memoryTimelineConstructionEvidence change (soundness-sensitive).
- aeneas (h_aeneas, #111): on hold — decode residuals carried in rowData.

NEXT (user's call): land 57/63 (recommended — the soundly-verifiable frontier); or pursue the deep
extraction-fidelity (MULH/MULHSU) / old-theorem memory change (d). DIV/REM = upstream fix.
