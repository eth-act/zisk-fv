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

=== P5 trace-level export (the real #61 closure) over the 55 — IMPLEMENTED (uncommitted) ===
ZiskFv/Compliance/TraceLevelExport.lean: 55 `RowData_<op>` structures + 55-arm
`RowConstructionData` sum + `StepCompliance` (per-arm bus_effect) + `stepCompliance_of_rowData`
+ `zisk_compliant_of_accepted_trace` (∀ i, StepCompliance …; NO OpEnvelope param). 0 sorry.

=== P5-STRONG: channel-balance export — 49/55 (uncommitted) ===
[UPDATE] +6 M-ext-unsigned arms (mulw/mulhu/divu/divuw/remu/remuw) added via DIRECT-LIFT:
rw [state_effect_via_channels_eq_bus_effect_2]; exact construction_<op>_sound … — lifts the
FAITHFUL loose-bound (<983041) construction, NEVER the canonical equiv tight (<131072) bound.
Non-vacuous (execRow real ∀-binder; no False.elim). 0 new ZiskFv.* axioms. Full lake build GREEN.
Gate V1 18/18 + V2 12/12. registered in StrongRowConstructionData/StepComplianceStrong/dispatcher.
LEFT in bus_effect form (6): 6 defect/gap (7 signed-M minus unsigned overlap; FENCE). NOT committed.

=== STEP (b2): M-ext OpEnvelope-route conversion — 29 → 35 (uncommitted, this run) ===
All 6 M-ext arms (mulw/mulhu/divu/divuw/remu/remuw) converted from direct-lift to the
OpEnvelope route via PATH 1 (trace-Environment): the lookup-witness STRUCTURES are now
BUILT from the SHARED-ArithMul provider's balance-derived FullSpec, NOT carried.
- New witness builders (Mem `rowRangeLookupWitness_of_range_facts` dummy-env technique,
  non-vacuous: substance = real FullSpec projections): `arithMulTableWitness_of_fullSpec`
  + `arithDivTableWitness_of_fullSpec` (SharedBundles.lean); `chunkRangeLookupWitness_of_spec`
  + `signedCarryRangeLookupWitness_of_spec` (ArithMul/Bridge.lean + ArithDiv/Bridge.lean).
- ArithMul→ArithDiv view bridge (Div arms): `arithDiv_fullSpec_of_arithMul_fullSpec` +
  `divu_row_constraints_of_arithMul_fullSpec` (ConstructionDivu.lean) — Div canonical equiv
  needs ArithDiv witnesses; provider is SHARED ArithMul; bridge re-views the same facts.
  `remainder_bound` stays the explicit RowData residual.
- Each arm: construct OpEnvelope.<op> from the trace's *Arow FullSpec/match + decode pins
  (added h_m32/h_set_pc/h_jmp_offset1/h_jmp_offset2 to all 6 RowData), call
  zisk_riscv_compliant_program_bus, thread h_known_arm (real EnvNoKnownDefectFor, M-ext
  cases added to StepNoKnownDefect; satisfiable via envNoKnownDefectFor_of_nondefect).
  DIVU projects exec_eq_divu (.2.2.2.2.2.2.2.2.2.1); the other 5 project exec_eq_remaining.
- OpEnvelope.lean / Compliance.lean / zisk_riscv_compliant_program_bus / canonical equiv_<OP>
  UNCHANGED (Attempt 1, no arm-redefinition). 0 new ZiskFv.* axioms. Full lake build GREEN.
  Gate V1 18/18 + V2 12/12. NOT committed.

=== STEP (b1): OpEnvelope-route conversion — 22 → 29 (uncommitted, prior run) ===
Converted 7 of the 16 targeted direct-lift arms to the OpEnvelope route (construct envelope +
call zisk_riscv_compliant_program_bus + thread h_known_arm): the 6 branches (beq/bne/blt/bge/
bltu/bgeu, projecting exec_eq_branch) + JALR (projecting exec_eq_remaining). Each: build
OpEnvelope.<op>, prove aeneasBridgeTrust (flat decode pins), memoryTimeline=trivial,
NoKnownDefect=h_known_arm env trivial. StepNoKnownDefect now returns the real EnvNoKnownDefectFor
for these 7 (non-vacuous: satisfiable for non-defect ops via envNoKnownDefectFor_of_nondefect —
verified). Added 6 flat decode-pin fields to each RowData_b* (h_main_active/h_main_op/h_m32/
h_set_pc/h_store_pc/h_jmp_offset1or2 — genuine trace residuals); JALR needed none (pins already
present). Full lake build GREEN; 0 new ZiskFv.* axioms; gate V1 18/18 + V2 12/12. NOT committed.
BLOCKED 9 (genuine walls, reported — NOT laundered/forced):
- M-ext (6: mulw/mulhu/divu/divuw/remu/remuw): OpEnvelope arms require lookup-witness STRUCTURES
  (ArithMul/DivTableWitness, *ChunkRangeWitness, *SignedCarryRangeWitness, ArithDivRemainderBound-
  Witness = {offset, env : Environment FGL, holds : ConstraintsHold.Soundness …}). Balance yields
  only Prop-level FullSpec; NO FullSpec→lookup-witness bridge exists (witness needs a Clean env for
  the constant vOf*Row view). DIVU/MULHU additionally route through equiv_DIVU/MULHU whose internal
  TIGHT <131072 carry bound is documented NOT balance-constructible (ConstructionDivu.lean:36-57).
  The *_of_fullSpec wrappers exist precisely to AVOID this route.
- LUI/AUIPC/JAL (3): OpEnvelope arms require MainRowProvenance + *RowMode (the Aeneas-extracted-row
  record incl. ROM fields). NO constructor of MainRowProvenance from a trace exists anywhere
  (it is the blocked-in-build aeneasBridgeTrust residual; 4.28 can't import 4.30 Aeneas world).
  Constructions route through MainRowProvenance-free variants (equiv_LUI / equiv_JAL_of_main_pins).
Stores (4) + loads (7) intentionally LEFT on direct-lift (next step).
--- (prior note, now superseded by the line above) ---
TraceLevelExport.lean: 43 `stepStrong_<op>` theorems via TWO sound routes, both yielding the
OLD global theorem's per-arm conclusion (channel-balance `state_effect_via_channels`) —
STRICTLY STRONGER than the bus_effect form. + `StrongRowConstructionData` (43-arm sum) +
`StepComplianceStrong` + `stepComplianceStrong_of_rowData` + `zisk_compliant_of_accepted_trace_strong`
(∀ i, …; NO OpEnvelope param).
- ENV-CONSTRUCTED route (22 op-bus ALU): RTYPE sub/and/or/xor/slt/sltu; ITYPE
  andi/ori/xori/slti/sltiu; shifts sll/srl/sra/slli/srli/srai; ADD/ADDI; W-ALU subw/addw/addiw.
  CONSTRUCT OpEnvelope.<op> per row, invoke zisk_riscv_compliant_program_bus; 3 hyps discharged
  in place (aeneasBridgeTrust/memoryTimeline/NoKnownDefect-trivially-TRUE).
- DIRECT-LIFT route (21 NEW this run): branches beq/bne/blt/bge/bltu/bgeu; LUI/AUIPC; JAL/JALR;
  stores sb/sh/sw/sd; loads lb/lh/lw/ld/lbu/lhu/lwu. Each construction_<op>_sound proves the
  bus_effect form over the real trace row; state_effect_via_channels is @[reducible]-defeq to
  bus_effect.2, so `rw [state_effect_via_channels_eq_bus_effect_2]; exact construction_<op>_sound …`
  yields the IDENTICAL channel-balance proposition the global theorem produces. For branches this
  IS the Equivalence.<B>.equiv_<B> the global dispatcher dispatches to. This route NEVER builds an
  OpEnvelope / invokes zisk_riscv_compliant_program_bus, so it sidesteps the stores' whnf BLOWUP
  (Eq.mpr cast over MainRowWithRom) and the loads' Var/Environment eval-provenance obstacle.
NON-VACUOUS: no False.elim / contradictory binder anywhere; execRow stays a real ∀-binder;
conclusion over the real mainOfTable row; #76/SextLoadBridge residuals carried verbatim as
RowData binders. 0 sorry; 0 new ZiskFv.* PROJECT axioms (only ZiskFv-prefixed name in closure is
the theorem itself; deps = Sail-translation + Lean-kernel postulates, = constructions' closure).
Full lake build GREEN; gate V1 18/18 + V2 12/12.
LEFT in bus_effect form (12): 6 M-ext-unsigned (mulw/mulhu/divu/divuw/remu/remuw — direct-lift
available BUT bus_effect is CORRECT: channel-balance equiv needs the TIGHT <131072 carry bound,
known-suspect / not row-locally constructible; faithful <983041 is right — do NOT force) + 6
defect/gap (7 signed-M minus the unsigned overlap counts as the M-ext set; FENCE) with no sound
construction. NOT committed (per instructions).

=== SIBLING THREADS ===
- #111 (aeneasBridgeTrust discharge): BLOCKED — sound in-build discharge is NO-GO (numBits/
  irreducibility wall; native_decide gate-forbidden). Needs a route decision (a: large
  symbolic effort / b: native_decide trust-policy [advised against] / c: keep loose coupling).
- #76 (h_memory_timeline): PR-76.5 step D landed on p76-memory (cross-segment seam, GO);
  E/F/G + per-address timeline remain. Discharges loads' + stores' #76 residuals.

=== P5-STRONG h_known_bugs THREADING — DONE (uncommitted) ===
zisk_compliant_of_accepted_trace_strong now TAKES a per-row defect-exclusion binder
`(h_known_bugs : ∀ i, StepNoKnownDefect trace binding i (rowData i))` and threads it via
stepComplianceStrong_of_rowData → each of the 22 OpEnvelope-route stepStrong_<op> arms, which
now RECEIVE the supplied obligation and pass `h_known_arm env trivial : NoKnownDefect env` to
zisk_riscv_compliant_program_bus INSTEAD of proving NoKnownDefect internally. New helpers in
TraceLevelExport.lean: `EnvNoKnownDefectFor sel := ∀ env, sel env → NoKnownDefect env` (def),
`envNoKnownDefectFor_of_nondefect` (trivial-discharge theorem), `StepNoKnownDefect` (per-arm
obligation; EnvNoKnownDefectFor on the arm's constructor for the 22, True for direct-lift arms).
NON-VACUOUS: trivially satisfiable for the 49 current non-defect arms (witness verified);
for the future signed-M/FENCE defect arms the same binder becomes the genuine NoKnownDefect of a
defect-region env (NOT unconditionally true) — the plumbing point. 0 new ZiskFv.* axioms (closure
unchanged). Full lake build GREEN. Gate V1 18/18 + V2 12/12. NOT committed.

GOAL NOTE: the /goal says "ALL 63" — unachievable (8 are defect/gap-gated). Re-scope to
"the 55 constructible + 8 honestly excluded via NoKnownDefect; P5 over the 55."
