Stream: Uniform-63 OpEnvelope-route export (#61 endgame). Worktree p4-mext,
branch p4-loads-stores (PR #112, stacked on PR #110). Metaplan: docs/ai/plan/PLAN_ENDGAME.md.
Gate V1 18/18 + V2 12/12 throughout. 0 new ZiskFv.* axioms.

=== DONE: 63/63 on the OpEnvelope-route ===
root_soundness: for ALL 63 RV64IM opcodes, construct OpEnvelope.<op>
from the trace + invoke zisk_riscv_compliant_program_bus + thread h_known_bugs. NO OpEnvelope
input (takes rowData), NO direct-lift. Non-vacuous (63 stepStrong arms, no False.elim, execRow real
∀-binder). NO main-theorem refactor (canonical/OpEnvelope/old-theorem intact — every arm built from
the trace via mainConstVar/memConstVar + trace-Environment lookup-witness pattern). All 63 canonical
equiv_<OP> are non-vacuous (all 7 signed-M retired this session).

h_known_bugs carries ONLY the exact witness-conditional defects (NOT opcode-wide):
- MUL/MULH/MULHSU: the np-forge shape (np=0 ∧ na⊕nb=1) — the genuine malicious forge.
- DIV/REM/DIVW/REMW: the |r|=|d| LT_ABS_NP false-positive shape (codygunton/zisk#5) — malicious-only
  (honest division always has |r|<|d|).
Honest inputs are NEVER excluded; honest_<op>_witness_not_forge witnesses confirm satisfiability.

Documented residuals (all honest, named, dischargeable):
- na=MSB sign-range residual (MULH/MULHSU/DIV/REM/DIVW/REMW): the real circuit enforces it
  (arith.pil:286/289/303 indexed range lookup); FV model collapsed to FULL. Dischargeable by
  composing ArithRangeTable (issue #114 category D).
- h_op2_ne (div-by-zero) + h_no_overflow (INT_MIN/-1) on DIV/REM/DIVW/REMW: circuit computes these
  CORRECTLY (investigation a50efb5f, all 15 cases match Sail); dischargeable in-model by extracting
  arith.pil:54,64-95 (issue #114 category A — the Main/Arith --only curation omits them).
- aeneasBridgeTrust decode residuals (#111): held, carried in rowData.

=== Two real ZisK findings surfaced by this goal ===
- eth-act/zisk-fv#114: Main/Arith extracted with hand-curated --only subsets → silently omit F-clean
  circuit constraints (e.g. div-by-zero/overflow). Asks: audit all AIRs + completeness gate.
- codygunton/zisk#7: DIVW INT_MIN/-1 overflow — emulator op_div_w returns 0x0000_0000_8000_0000
  (zero-ext) vs Arith SM's correct sext 0xFFFF_FFFF_8000_0000 → completeness bug (program unprovable),
  NOT soundness. Masked by ZisK's own unit test. Second FV-found bug after #5.

=== Commits (on top of e3a71967) ===
ba8b61d1 thread h_known_bugs · debd3bd7 (a) M-ext de-vacuity · 141b44fe branches+JALR ·
7cf4c280 6 M-ext · 55cbc02e LUI/AUIPC/JAL · 009123ee W-shifts+stores · e8264ff3 7 loads ·
8b763d61 FENCE · 8b541c46 MUL defect-retire · 03fb00ea MUL trace-arm · b90b3bb0 MULH/MULHSU ·
ee4f29ff DIV/REM canonical · 9f4bae1d DIVW/REMW canonical (all 63 canonical non-vacuous) ·
<this> DIV/REM/DIVW/REMW trace-arms → 63/63 arms.

=== Deferred (non-blocking, orthogonal) ===
- div-by-zero/overflow discharge (#114 cat A): extract arith.pil:64-95 → drop h_op2_ne/h_no_overflow.
- na=MSB discharge (#114 cat D): compose ArithRangeTable → drop the sign-range residual.
- (d) memory reduction: DONE (loads). Fold-B (Spike.lean ported) reduces the 7 loads'
  h_memory_timeline from whole-SailState MemoryPrefixStateAlignment → memory-only
  LoadMemoryTimelineCoherenceEvidence (RowTraceCoherence + seed + load-state pin) in the LIVE
  old theorem; byte-local agreement DERIVED via stateBytesAtPrefix_of_rowTraceCoherence. All 63
  build, 0 new ZiskFv.* axioms, gate V1 18/18 + V2 12/12, LD non-vacuity instantiation rebuilt to
  coherence shape. Strict shrink proven by Spike.witness_nondegenerate (regs+cycleCount differ).
  Stores DEFERRED: h_m1..h_m7 are positional OpEnvelope.sb/sh/sw constructor fields (not a keyed
  reducible def) → reducing needs an OpEnvelope inductive refactor of the store arms. NOT committed.
- aeneas (#111): held.
