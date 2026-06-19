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

=== P5-STRONG: channel-balance export — 43/55 (uncommitted) ===
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

GOAL NOTE: the /goal says "ALL 63" — unachievable (8 are defect/gap-gated). Re-scope to
"the 55 constructible + 8 honestly excluded via NoKnownDefect; P5 over the 55."
