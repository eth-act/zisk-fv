Stream: P4 M-ext constructions (p4-mext worktree, off origin/main). build/ symlinked,
submodule populated, gate 18/18 (V1) + 12/12 (V2). Plan: docs/ai/plan/PLAN_ENDGAME_P4_MEXT.md.

=== P4 SET NOW 55/63 (control flow added; see bottom) ===

=== UNSIGNED M-EXT COMPLETE: 36/63 ===
All 6 unsigned RV64M construction_<op>_sound landed, full-fidelity (arith witnesses
DERIVED from componentWithArithTable.FullSpec, not caller-supplied), green, 0 PROJECT
ZiskFv.* axioms each, committed:
- MULW e86b7c05, MULHU 94b09482, DIVU 266e7a98, DIVUW a297ef86, REMU 8e2f084c, REMUW e7ffae17.
Signed M-ext (MUL/MULH/MULHSU/DIV/DIVW/REM/REMW) stay defect-gated (NoKnownDefect /
the codygunton/zisk#5 LT_ABS_NP bug). FENCE defect-gated.

EXTRACTION FOUNDATION (committed, the lever that unblocked full-fidelity M-ext):
- c46 re-compose (cd26a331), chunk ranges (d9e59667), carry ranges (8660312f),
  faithful op-bus mux (af16b990) → componentWithArithTable now faithfully constrains
  carry-chain + ArithTable + c46 + chunk ranges + carry ranges + the muxed message
  (all modes), all balance-derivable.

RESIDUALS carried per div/rem construction (honest, == canonical equiv): the ONE
`remainder_bound` (LTU |d|<b self-edge — a finished-channel self-edge NOT in the
ensemble; full-fidelity needs composing it, deferred) + W-mode bus-encoding residuals
(h_b23/h_c23/h_sext_choice for the W ops) + operand bridges + decode/Sail/exec/nextPC.

=== LOADS COMPLETE (uncommitted): 40 → 47 ===
All 7 RV64 load construction_l{b,h,w,d,bu,hu,wu}_sound landed in NEW
ZiskFv/Compliance/ConstructionLoad.lean, green, 0 PROJECT ZiskFv.* axioms each
(LHU/LWU inherit native_decide via the canonical MemAlign zero-pad path).
Pattern mirrors ConstructionStore: bus.e1 (read) / bus.e2 (rd-write) rooted at
the Main row's own b/c emissions ⇒ main_b_match/main_c_match = refl. Canonical
equiv_<LOAD> reused (byte/sext/zext already proven there). Registered in
ZiskFv.lean + bin/TrustGate/Main.lean; baseline-construction-theorem-binders.txt
regenerated (1768→2494, purely additive). Gate: V1 18/18 + V2 12/12. NOT committed.

HONEST #76 RESIDUALS carried per load (genuinely irreducible, FLAGGED in header):
- h_memory_timeline : MemoryTimelineEvidence state bus.e1 (loaded bytes ↔ Sail mem,
  cross-row replay timeline) — inside LoadPromises.memory_timeline.
- Mem-AIR provider linkage (mem, r_mem, h_mem_match, h_mem_sel, h_mem_wr): the
  Mem-channel balance leaves a 5-way provider disjunction (per ConstructionStore
  note), so it is NOT balance-derivable here.
- LBU/LHU/LWU: + align : MemAlignWitness (sub-doubleword high-byte-zero provider).
- LB/LH/LW: + BinaryExtension op-bus provider (v, r_binary, offset, env, h_static,
  h_match) — no signextend balance wrapper exists.

=== CONTROL FLOW COMPLETE (uncommitted): 47 → 55 ===
All 8 control-flow construction_<op>_sound landed: 6 branches in NEW
ZiskFv/Compliance/ConstructionBranch.lean (beq/bne/blt/bge/bltu/bgeu) + JAL/JALR
in NEW ZiskFv/Compliance/ConstructionJump.lean. Green, 0 PROJECT ZiskFv.* axioms
each (no native_decide; branches/JAL purely Sail-axiom + kernel; JALR + the
documented Sail execute_JALR_pure_equiv axiom). Registered in ZiskFv.lean +
bin/TrustGate/Main.lean; baseline-construction-theorem-binders.txt regenerated
(2494→2774, strictly additive). Gate: V1 18/18 + V2 12/12. NOT committed.

HONEST #100 RESIDUAL carried per control-flow op (genuinely irreducible, FLAGGED):
- Branches: h_nextPC_matches = the #100 cross-row CONDITIONAL next-PC obligation
  (exec-bus PC ↔ Sail execute_<BOP>_pure.nextPC, where Sail IS the
  `if cmp then pc+imm else pc+4` term — NO separate taken/not-taken selector
  needed; the conditional collapses into the one equation). Plus operand bridges
  + misa[C]=0 profile + happy-path not_throws/success.
- JAL/JALR: JumpPromises.nextPC_matches = the #100 next-PC obligation (JAL
  unconditional pc+imm; JALR computed (rs1+imm)&~1). jump_subset/jalr_subset
  DERIVED from per-row Spec; rd-write = Main row's own cMemMessage (eRdLui /
  StorePcMemoryWitness, matches_memory_entry_refl). Intra-row h_pc_bridge /
  h_link_bridge are bucket-(b) Sail bridges, NOT the cross-row term.

NEXT: either P5 assembly (compose the 55 constructions → env removal) or merge/PR.
Sibling threads: #76 (p76-memory) + Aeneas downgrade (aeneas-discharge).
