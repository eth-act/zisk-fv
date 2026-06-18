Active stream: P4 M-ext constructions — add the 6 unsigned RV64M
`construction_<op>_sound` theorems (MULW, MULHU, DIVU, DIVUW, REMU, REMUW), 31 → 36.
Feeds the P5 OpEnvelope-removal assembly.

Worktree `.worktrees/p4-mext`, branch `p4-mext` off `origin/main`. build/ symlinked.
Plan: docs/ai/plan/PLAN_ENDGAME_P4_MEXT.md (P4/P5 PATH + extraction-expansion checklist).

PATH (verified): expanding the PIL extraction is the ONLY lever for the M-ext arith
constructions; rest of P4/P5 is non-extraction (constructions plumbing / #76 / #100 /
bus_effect retirement / Aeneas / defect gates). Full fidelity throughout (user choice).

DONE (faithful-mux foundation, uncommitted): the Clean ArithMul provider op-bus
message is now FAITHFUL to the real PIL emission (arith.pil:247-258 /
build/extraction/Extraction/Buses.lean bus_emission_Arith_0). `primaryOpBusMessageExpr`
+ concrete `primaryOpBusMessage` carry the real MUXED a_lo/a_hi/c_lo lanes
(div / main_mul / main_div selectors) covering all arith modes via one message.
The hardcoded `main_mul` branch is GONE. Anti-laundering positive: replaces an
unfaithful hardcoding with the real PIL mux; NO new trust (the emission was already
in the ensemble — now correct). MULW PRESERVED: `construction_mulw_sound` re-derived
through the new muxed message + a MODE-GATED bridge
(`primaryOpBusMessage_toEntry_rowAt_eq_opBus_row` now takes div=0 ∧ main_mul=1 ∧
main_div=0; reduces the mux to the plain c-lanes). Mode pins DERIVED inside the
construction from the balance-derived FullSpec's ArithTableSpec + op=182 via the new
bare-row `mulw_mode_pins_of_row` (ArithTableProjections). construction_mulw_sound
binders UNCHANGED. Full `lake build` GREEN (8692 jobs); 0 sorry; 0 new ZiskFv.* axioms
(construction_mulw_sound closure = Sail+kernel external only); V1 17/18 (only the
pre-existing zisk-submodule-absent Aeneas 16/18 fails) + V2 ALL PASS; no trust baseline
files changed. 4 files touched: AirsClean/ArithMul/{Constraints,Bridge}.lean,
AirsClean/ArithTableProjections.lean, Compliance/ConstructionMulw.lean.
NEXT (separate task): build MULHU + div/rem op-bus matches off the muxed message
(secondary/div-mode bridges) — NOT in this foundation task.

DONE (committed, green, 0 ZiskFv.* axioms):
- c46 re-compose (cd26a331), chunk ranges (d9e59667), carry ranges (8660312f) →
  `componentWithArithTable.Spec = FullSpec = Spec ∧ ArithTableSpec ∧ C46Spec ∧
  ChunkRangeSpec ∧ CarryRangeSpec`, all balance-derivable.
- construction_mulw_sound (e86b7c05) — FIRST M-ext construction, full-fidelity (31/63).
  F4 bridge `equiv_MULW_of_fullSpec` derives the arith witnesses from balance;
  residual binders are honest decode/Sail/operand/exec/nextPC only.

KEY FINDING: the other 5 M-ext were blocked — the Clean ArithMul provider's op-bus
message HARDCODES the main_mul (c-chunk) lane; the real PIL emission (arith.pil:247-258
/ bus_emission_Arith_0) MUXES the a/c lanes (bus_a0 div-mux, bus_res0 3-way mux). So
MULW (c-lane) matched; MULHU (d-lane) + div/rem (a-lane) could not. User chose FULL
FIDELITY (core extraction) over carrying the match as a residual.

IN PROGRESS: Stage 1 — make `primaryOpBusMessageExpr` the faithful bus_a/bus_res0 mux
(one message covers all modes; each op's mode pins select its lane). MULW-preserving.
Ripples to the core op-bus enumeration (Balance.lean) + the per-mode bridge
(opBus_row_ArithMul at MULW mode) + MULW re-derivation. Anti-laundering positive
(faithful mux replaces unfaithful hardcoding; no new trust).

NEXT after Stage 1: construction_mulhu_sound (d-lane via mode pins), then the
div-family (DIVU/DIVUW/REMU/REMUW — ArithDiv view + the remainder-bound self-edge).
Then P5 assembly over the 36 constructions, carrying the non-extraction residuals.
