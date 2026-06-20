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

=== RESULT: DIV/REM retired 59→61/63; DIVW/REMW WALL on missing W discharge infra ===
DONE (uncommitted): canonical equiv_DIV/equiv_REM now REAL (no False.elim), non-vacuous.
Defect ArithDivDynamicWitnessShape .div/.rem narrowed True→exact |r|=|d| forge
((signedRemainderInt v r_a).natAbs = op2.toInt.natAbs). Strict |r|<|d| DERIVED at canonical
layer from WEAK residual h_r_le + narrowed-defect via lt_of_le_of_ne (load-bearing).
Anti-vacuity: honest_{div,rem}_witness_not_forge. Full lake build green; gate V1 18/18 + V2 12/12
(baselines refreshed: hypothesis-count, caller-burden canonical+wrapper; axiom-deps diff EMPTY =
0 new ZiskFv.* axioms). DIVW/REMW kept opcode-wide gated (.divw/.remw => True) — they need
div_w_chain_witnesses + h_rd_val_mdrs_{divw,remw}_chunked + real EquivCore (currently False.elim);
low-level W bridges exist, mid-level glue does not. Ledger updated (defects.md + trusted-base.md).
TODO if continuing: trace-level export arms for signed DIV/REM (additive coverage, not gate-blocking).

=== PRIOR ACTIVE: DIV/DIVW/REM/REMW retirement (signed remainder-bound residual route) ===
Findings: EquivCore.Div/Rem are REAL & complete (via h_rd_val_mdrs_{div,rem}_chunked); only
wrapper+canonical are False.elim. EquivCore.Divw/Remw are False.elim AND lack
h_rd_val_mdrs_{divw,remw}_chunked (deeper). Wall: no arith_div_remainder_bound_signed lemma —
the LT_ABS_NP byte chain proves only WEAK |r|≤|d|; the false positive is exactly at |r|=|d|.
Design (sound, non-laundering): (1) narrow ArithDivDynamicWitnessShape to EXACT |r|=|d| forge;
(2) carry the WEAK bound |r|≤|d| as a caller residual binder (extraction-fidelity, like MULH na=MSB)
PLUS sign-range operand bridges + h_r_sign + h_nr_pin; (3) DERIVE strict h_r_abs = |r|<|d| from
weak + ¬(|r|=|d|) via Nat.lt_of_le_of_ne — making the defect narrowing LOAD-BEARING; (4) call the
ready EquivCore.{Div,Rem}.equiv_{DIV,REM}. W-mode needs EquivCore + W discharge lemmas (deep;
land non-W first, report W gap if it walls).

=== PRIOR: MULH/MULHSU retirement 57→59 (sign-range residual route) ===
Plan: narrow Defects MaliciousSignedMulWitnessShape .mulh/.mulhsu True→exact forge; add sign-range
residual binders (na=MSB op1, nb=MSB op2) to canonical equiv_MULH/MULHSU + wrappers; build real
high-half signed proof via fgl_mul_signed_to_bv64_hi + mul_signed_chain_witnesses +
signed_packed_toInt_eq_of_read_xreg; extend OpEnvelope .mulh/.mulhsu + dispatch; add trace-arms
(mulhEnvOf/mulhsuEnvOf/RowData_*/stepStrong_*) to strong theorem; document sign-range residual in
trust ledger (arith.pil:286/289/303); refresh caller-burden + hypothesis-count + axiom-deps baselines
(GROW, justified+surfaced). 0 new ZiskFv.* axioms (na=MSB is a binder, not an axiom).
Phases: 1 core rd-value lemma · 2 EquivCore · 3 wrappers · 4 canonical equivs · 5 defects+nonvac
· 6 OpEnvelope+dispatch+trace-arms · 7 ledger+baselines+full build+gate.

=== DONE (uncommitted): MULH/MULHSU retired 57→59/63 ===
Full lake build green. Gate V1 18/18 + V2 12/12 pass (baselines refreshed: hypothesis-count,
caller-burden canonical+wrapper; axiom-deps UNCHANGED = 0 ZiskFv.* axioms). Sign-range residual
(na=MSB/nb=MSB) carried as h_sign_a/h_sign_b binders on equiv_MULH/MULHSU — documented in
trust/defects.md + trust/trusted-base.md as extraction-fidelity residual (arith.pil:286/289/303).
New: EquivCore/{MulH,MulHSU}.lean, mdrs_mulh_core_data + h_rd_val_mdrs_{mulh,mulhsu}_chunked,
{mulh,mulhsu}_np_xor_or_zero_product_shape projections, RowData_{mulh,mulhsu}/{mulh,mulhsu}EnvOf/
stepStrong_{mulh,mulhsu} trace-arms. Defects .mulh/.mulhsu narrowed True→exact forge. NOT committed.
