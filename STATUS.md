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

DONE (Stage 2 — construction_mulhu_sound, d-lane secondary, 32/63): mirrors MULW.
KEY BLOCKER FOUND + RESOLVED: EquivCore.MulHU.equiv_MULHU wants carry ranges < 131072
(2^17) but balance (FullSpec.CarryRangeSpec) only gives the SIGNED disjunction
(< 983041 ∨ ≥ p-983040). Genuine 4×4 unsigned-mul carries reach ~3·2^16 > 2^17, so
< 131072 is UNSATISFIABLE from real balance data (the shared MulNoWrap < 131072 bound
is documented-conservative). Resolution: derive < 983041 from balance
(unsigned_carry_step_nat = signed disjunction + chain step + chunk ranges ⟹ < 983041)
and route construction_mulhu_sound through a NEW equiv_MULHU_of_fullSpec that
reconstructs rd via a LOOSE-bound (< 983041) chunk→ℕ→high-half write-value path in
ConstructionMulhu.lean (NOT modifying shared MulNoWrap / equiv_MULHU). Arith witnesses
all DERIVED from FullSpec; 0 PROJECT ZiskFv.* axioms. Closure carries
Lean.ofReduceBool/trustCompiler (native_decide) INHERITED from the canonical
equiv_MULHU path (already has it; NOT new — MULW is native_decide-free); tracked by #75.
Full lake build GREEN (8693). V1 17/18 + V2 ALL PASS (only the pre-existing
zisk-submodule-absent Aeneas 16/18 fails). Files: NEW Compliance/ConstructionMulhu.lean;
+op-177 keep/refute in ArithBalance + table-exclusions (Binary/BinaryExtension Table +
StaticCircuit + Binary Bridge) + AcceptedTrace binding wrapper + ArithMul/Bridge
MULHU-mode bridge + ArithTableProjections mulhu_mode_pins_of_row; registered in
ZiskFv.lean + bin/TrustGate/Main.lean; construction-binder baseline appended.

DONE (Stage 3 — construction_divu_sound, unsigned DIVU primary a-lane, 33/63):
mirrors MULW/MULHU. Provider = SHARED ArithMul componentWithArithTable (ArithDiv
emits NO op-bus in the ensemble: arithDiv_table_interactionsWith_opBus_nil →
circuit.channels=[]). DIVU Main op-bus matches the muxed primaryOpBusMessage; new
DIVU-mode bridge primaryOpBusMessage_toEntry_eq_opBus_row_ArithDiv reduces it (at
div=1 ∧ main_div=1 ∧ main_mul=0) to opBus_row_ArithDiv. Arith witnesses
(ArithTable/chunk/signed-carry/c46/carry-chain) ALL DERIVED from FullSpec.
CARRY BOUND: same MULHU blocker — equiv_DIVU wants <131072 (2^17), balance only
gives signed disjunction; genuine Euclidean carries >2^17 ⟹ loose <983041 derived
(divu_carry_bounds via unsigned_carry_step_nat) + NEW loose write-value path
h_rd_val_mdru_divu_loose (in MulDivRemUnsigned.lean) routed through a custom
equiv_DIVU_of_fullSpec (NOT equiv_DIVU). REMAINDER BOUND = RESIDUAL (not
balance-derivable): ArithDivRemainderBoundWitness is the arith.pil:274
assumes_operation LTU consumer edge matched vs a Binary provider — a
finished-channel SELF-EDGE absent from the ensemble (ArithDiv emits no op-bus), so
it CANNOT come from balance. Carried as the ONE explicit residual binder, exactly
as the canonical equiv_DIVU carries it. Full lake build GREEN (8694); 0 sorry;
0 PROJECT ZiskFv.* axioms (closure carries Classical.choice + Quot.sound + Sail +
Lean.ofReduceBool/trustCompiler native_decide INHERITED from canonical equiv_DIVU
path — NOT new; #75). V1 18/18 + V2 12/12 ALL PASS. Files: NEW
Compliance/ConstructionDivu.lean; +op-184/offset-168 exclusions (BinaryTable,
BinaryExtensionTable, Binary/Bridge, BinaryExtension/StaticCircuit) + ArithBalance
keep/refute + AcceptedTrace from_binding wrapper + ArithTableProjections
divu_mode_pins_of_row + MulDivRemUnsigned loose divu path; registered in ZiskFv.lean
+ bin/TrustGate/Main.lean; construction-binder baseline refreshed. NOT committed
(parent commits).

NEXT after Stage 3: DIVUW/REMU/REMUW. Then P5 assembly over the 36 constructions,
carrying the non-extraction residuals.
