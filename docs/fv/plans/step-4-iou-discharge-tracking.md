# Step 4 IOU tracking — residual *promise hypotheses* to lift into discharge bridges

This file enumerates every caller-burden binder that `Compliance.lean`
(Step 4) currently inherits as a precondition, organized by shape, with
the exact discharge mechanism needed to lift it into
`Equivalence/Bridge/<Shape>.lean`. The end state is: each
`Bridge/<Shape>.lean` exposes a per-opcode `<op>_discharge_full` entry
point delivering the full set of equations the opcode's equiv needs,
each per-opcode equiv consumes that entry point and drops its
preconditions, and `Compliance.lean` becomes a thin case-split + dispatch
with minimal preconditions (just AIR validators + structural facts +
Sail state match).

The Path-B engineering choice (per the chat transcript): author
`Compliance.lean` now using current per-opcode equivs (preconditions
inherit), then iteratively lift discharges shape-by-shape. **Each
discharge bridge below MUST be lifted before the project is "done"
relative to the user's stated goal of a global theorem whose
`#print axioms` closure is exactly the documented trust ledger.**

## Layering recap

```
Airs/<AIR>.lean + <AIR>/Ranges.lean       trust-ledger axioms (per AIR)
Fundamentals/Transpiler.lean              transpile contracts (66 axioms)
Equivalence/Bridge/<Shape>.lean           ← per-shape discharge (THIS is what we thicken)
  Bridge/SailStateBridge.lean              Sail-state ↔ Main lane bridge
  Bridge/StateBridge.lean                  packed-lane reconstruction
Equivalence/WriteValueProofs/<family>.lean rd-value identity (per family)
Equivalence/<OP>.lean                     canonical equiv (consumes Bridge + RdVal)
Compliance.lean                            global theorem (dispatches to <OP>)
Compliance/Dispatch.lean                   per-Op dispatchers
Compliance/Wrappers/<Op>.lean             trust-discharge wrappers (×63)
```

## Per-shape IOUs

### BinaryExtension (11 ops: SLL, SLLI, SRL, SRLI, SRA, SRAI, SLLW, SLLIW, SRLW, SRAW, SRAIW, SRLIW)

Plus LB/LH/LW (3 ops) which use the BinaryExtension AIR through
`Circuit/SextLoadBridge.lean` for sign extension.

**Already discharged** (alpha + cleanup + first lift iteration): 8
a-byte ranges, 16 c-byte 32-bit ranges, 8 e2 byte ranges (now via
`memory_bus_entry_byte_range_perm_sound` for ALL 12 shifts plus LB/LH/LW),
9 (LB) / 10 (LH) / 12 (LW) e1+e2 byte ranges for signed loads.

**First lift iteration outcome (commits 6197b62, 1ab0abc):** 96
binders dropped (8 e2 byte-ranges × 12 shifts). Bridge file
extended with `binext_shift_discharge_partial` helper +
per-opcode `<op>_discharge_partial` wrappers (SLL/SRL/SRA/SLLW/SRLW/SRAW).
These wrappers are scaffolding for the next iteration; not yet consumed
by equivs.

**Blocker for deeper discharge (`h_op`, `h_match_clo`, `h_match_chi`,
`h_bytes`, `h_input_r1_circuit`, `h_shift_pin`, `h_lane_rd`):** The
discharge requires deriving `v.op_is_shift r_binary = 1` from
`v.op r_binary = OP_<shift>`. Per PIL
`binary_extension.pil:88` (`col witness bits(1) op_is_shift; // 1
if operation is in the shift family; 0 otherwise`) and the table
lookup at line 92, this linkage is enforced at the AIR row level
but is NOT currently exposed in the Lean model — `ByteLookupHypotheses`
in `BinaryExtensionPackedCorrect.lean` omits the `op_is_shift` field.
To unblock:

**REQUIRED NEXT IOU:** Add narrow axiom in
`ZiskFv/Airs/Binary/BinaryExtensionRanges.lean` (or new
`BinaryExtensionOpClassification.lean`):

```lean
/-- **BinaryExtension AIR op_is_shift linkage.** Per PIL
    `binary_extension.pil:88` (`col witness bits(1) op_is_shift`) and
    `binary_extension.pil:92` (the table lookup binding op_is_shift
    to the table entry's flag), every row whose `op` column matches
    a shift-family literal has `op_is_shift = 1`, and every row
    matching a SEXT-family literal has `op_is_shift = 0`.

    Trust class: lookup-soundness on the BinaryExtension table (same
    class as `bin_ext_table_consumer_wf`). -/
axiom binary_extension_op_is_shift_pin (v : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (v.op r = OP_SLL ∨ v.op r = OP_SRL ∨ v.op r = OP_SRA
     ∨ v.op r = OP_SLL_W ∨ v.op r = OP_SRL_W ∨ v.op r = OP_SRA_W
        → v.op_is_shift r = 1)
  ∧ (v.op r = OP_SIGNEXTEND_B ∨ v.op r = OP_SIGNEXTEND_H ∨ v.op r = OP_SIGNEXTEND_W
        → v.op_is_shift r = 0)
```

After this axiom lands (with ledger entry under existing class #6),
the deeper BinExt discharge becomes mechanically derivable:
- `h_input_r1_circuit`: `op_is_shift = 1` + matches_entry's `a_lo`
  conjunct unfolds `opBus_row_BinaryExtension`'s `a_lo` formula to
  the pure packed-a-byte form (without the `b_0` correction term).
- `h_shift_pin`: same simplification for `b_lo`.

**Residual caller-burden (still IOU):**

| Binder | Discharge mechanism | New file/section needed |
|---|---|---|
| `r_binary : ℕ` existential | Already from `binext_discharge_conservative` (delivers ∃ r_binary + matches_entry) | Use existing |
| `h_op : v.op r_binary = OP_<shift>` | Project matches_entry's `op` conjunct + caller's `h_main_op` | `Bridge/BinaryExtension.lean` add `<op>_project_op` per opcode |
| `h_match_clo`, `h_match_chi` | Project matches_entry's `c_lo`/`c_hi` conjuncts after unfolding `opBus_row_BinaryExtension` (which sums `free_in_c_{even}` / `free_in_c_{odd}`) | `Bridge/BinaryExtension.lean` add `project_match_c` helper |
| `h_bytes : ByteLookupHypotheses v r_binary` (8 consumer matches) | Chain `bin_ext_table_consumer_wf` for each byte; the BinExt AIR's row-level lookup interactions provide consumer-matches per byte | `Bridge/BinaryExtension.lean` add `byte_lookups_at` helper consuming `bin_ext_table_consumer_wf` |
| `hc_lo_sum_lt`, `hc_hi_sum_lt` | Substitute `h_match_clo`/`chi` to rewrite sum as `(m.c_0/c_1 r_main).val`, then apply `main_columns_in_range` for `< 2^32` bound | `Bridge/BinaryExtension.lean` add `c_sum_bound` helper |
| `h_input_r1_circuit` (Sail r1_val ↔ packed BinExt a-bytes) | (1) `SailStateBridge.packed_lane_eq_of_read_xreg` at `(m.a_0, m.a_1)` + `transpile_<OP>` instantiated at `sail_to_rv64 state`. (2) Project matches_entry's `a_lo` after unfolding `opBus_row_BinaryExtension` with `e.op_is_shift = 1` to bridge `m.a_0` ↔ packed `e.free_in_a_*`. (3) Compose. | `Bridge/BinaryExtension.lean` add per-shift `<op>_input_r1_packed` entry point |
| `h_shift_pin` (Sail r2 low 6 bits ↔ `v.free_in_b`) | `transpile_<OP>` gives `m.b_0 = lane_lo (state.xreg rs2)`; matches_entry's `b_lo` + `e.op_is_shift = 1` gives `m.b_0 = e.free_in_b + 256 * e.b_0 - a0 + a0 = ...` simplifying to the b-byte/shift correspondence | `Bridge/BinaryExtension.lean` add `<op>_shift_pin` entry point |
| `h_lane_rd : register_write_lanes_match m r_main e2` | Apply `LaneMatch.register_write_lanes_match_of_bus_emission` to Main's `store_pc = 0, store_reg = 1` selectors | Already exists; consume in equiv |
| 8 `h_e2_*` byte ranges (shifts only — LB/LH/LW already done) | `memory_bus_entry_byte_range_perm_sound e2` (already in ledger) | Apply to remaining 11 shifts |

**Per-opcode entry point shape** (after lift):

```lean
theorem sll_discharge_full
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (state : PreSail.SequentialState ...)
    (r_main : ℕ) (sll_input : SllInput) (r1 r2 rd : regidx) (e2 : MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = OP_SLL)
    (h_main_store : m.store_pc r_main = 0 ∧ m.store_reg r_main = 1 ∧ m.store_ind r_main = 0)
    (h_read_r1 : read_xreg (regidx_to_fin r1) state = ok sll_input.r1_val state)
    (h_read_r2 : read_xreg (regidx_to_fin r2) state = ok sll_input.r2_val state)
    (h_e2_emit : <e2 emission shape>) :
  ∃ r_binary,
    matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary)
    ∧ v.op r_binary = OP_SLL
    ∧ h_bytes_form v r_binary
    ∧ h_a_range_form v r_binary
    ∧ all_hc_ranges_form v r_binary
    ∧ hc_lo_sum_lt_form v r_binary ∧ hc_hi_sum_lt_form v r_binary
    ∧ h_match_clo_form m v r_main r_binary ∧ h_match_chi_form m v r_main r_binary
    ∧ register_write_lanes_match m r_main e2
    ∧ memory_entry_bytes_in_range e2
    ∧ sll_input.r1_val = packed_a_bytes_form v r_binary
    ∧ sll_input.r2_val.toNat % 64 = (v.free_in_b r_binary).val % 64
```

Apply analogously for SRL/SRA/SLLI/SRLI/SRAI/SLLW/SLLIW/SRLW/SRAW/SRAIW/SRLIW.

### Binary (14 ops already done conservatively: AND/ANDI/OR/ORI/XOR/XORI/SLT/SLTI/SLTU/SLTIU/SUB/SUBW/ADDIW/ADDW)

**Already discharged**: 24 byte ranges per opcode.

**Residual caller-burden (still IOU):**

| Binder | Discharge mechanism |
|---|---|
| `r_binary` existential | `op_bus_perm_sound_Binary` (in trust ledger) |
| 8 `h_byte_<i> : consumer_byte_match` | Chain `bin_table_consumer_wf` per byte (already in ledger) |
| `h_match_clo`, `h_match_chi` | Project `matches_entry`'s `c_lo`/`c_hi` after unfolding `opBus_row_Binary` (which sums free_in_c bytes with shift coefficients) |
| `h_input_r1_circuit`, `h_input_r2_circuit` (packed Sail-form) | `SailStateBridge.packed_lane_eq_of_read_xreg` + per-opcode `transpile_<OP>` + matches_entry a/b projection |
| `h_e2_*` byte ranges | `memory_bus_entry_byte_range_perm_sound e2` |
| `h_lane_rd` | `LaneMatch.register_write_lanes_match_of_bus_emission` |
| **For SUB/SLT-shape only**: 6-field `consumer_byte_match_chain` (cin/flags/pos_ind) | **NEW AXIOM needed**: 6-field forward witness extending the existing 3-field `binary_per_byte_lookup_witness`. Fits existing trust class (Binary AIR row-level lookup soundness). |

### BinaryAdd (2 ops: ADD, ADDI)

**Already discharged**: chunk-range hypotheses.

**Residual caller-burden:**
| Binder | Discharge mechanism |
|---|---|
| `r_binary` existential | `op_bus_perm_sound_BinaryAdd` |
| `h_match` | Project matches_entry's c_lo/c_hi after unfolding `opBus_row_BinaryAdd` |
| `h_input_r1`, `h_input_r2` (for ADD) / `h_input_r1` (for ADDI) | `SailStateBridge.{add,addi}_input_bridges_of_read_xreg` (already exist) + matches_entry a/b projection |
| `h_e2_*`, `h_lane_rd` | Same as Binary shape |

### Arith Mul (5 ops: MUL, MULH, MULHU, MULHSU, MULW)

**Already discharged**:
- MUL/MULHU: 16 chunk-range hypotheses + 22-binder loose
  `(cy_i, h_cy_i, hC*)` carry-chain bundle (Round 2,
  commit `cf1900e`)
- MULH/MULHSU/MULW: 8 e2 byte-range hypotheses (cleanup batch)

**Residual caller-burden:**
| Binder | Discharge mechanism |
|---|---|
| `r_a` existential | `op_bus_perm_sound_ArithMul` |
| Loose `a₀..d₃` chunks (for MULH/MULHSU/MULW — promotion not done) | Tier-2 → Tier-3: add `(v : Valid_ArithMul, r_a : ℕ)` param, replace loose with column accessors |
| `cy₀..cy₆` + 7 cy ranges + 8 `hC31..hC38` (for MUL/MULHU after promotion) | Consume `mul_carry_chain_holds v r_a` from `Valid_ArithMul`'s row-level constraint set + extract cy projection from circuit |
| `h_byte_lo`, `h_byte_hi` (e2 packing) | Project `matches_entry`'s c_lo/c_hi conjuncts after unfolding `opBus_row_Arith` |
| `h_op1`, `h_op2` (Sail r1/r2 packing) | `SailStateBridge.packed_lane_eq_of_read_xreg` + `transpile_MUL` + matches_entry a/b projection |
| 8 e2 byte ranges (for MUL/MULHU only — not in cleanup) | `memory_bus_entry_byte_range_perm_sound e2` |
| `h_lane_rd` | `LaneMatch.register_write_lanes_match_of_bus_emission` |

**Round 3 attempt — skipped (MULH / MULHSU / MULW).** Investigated
under branch `lift-arith-2-discharge`. Each of these 3 opcodes carries
a single deeply caller-supplied promise hypothesis `h_byte_sum_circuit`
that asserts the *full operand-form spec output equation*: the bus
entry's byte-sum equals `(BitVec.ofInt 64 ((r1.toInt * r2.toInt) /
2^64)).toNat` (or the MULHSU / MULW analog). Discharging it requires
EITHER:

1. **Tier-2 → Tier-3 promotion** — add `(v : Valid_ArithMul, r_a : ℕ)`
   plus chain predicate + 7 mode pins + `h_byte_lo` / `h_byte_hi` (2)
   + `h_op1` / `h_op2` (2) = ≥12 new binders to derive
   `h_byte_sum_circuit` internally via `arith_mul_signed_packed_correct`
   + `h_rd_val_mdrs_<op>` chain. **Net hypothesis-count GROWS** by ≥11
   per opcode (replaces 1 binder, adds ≥12). Fails the anti-laundering
   metric monotone-decrease requirement (`CLAUDE.md` ¶ "Anti-laundering
   principle").
2. **Arith-correctness axiom** — declare e.g.
   `axiom arith_mulh_byte_sum_circuit (v, r_a, e2, h_match, ...)`
   delivering `h_byte_sum_circuit` directly. This is **axiom inflation**
   (the trust ledger grows by an axiom asserting the spec output) and
   fails check #1 of the same anti-laundering principle (no new axiom
   *kind*: this would assert spec equivalence, not row-level
   constraints).

A parser-artifact note (Round 3, now historical): the previous
`trust/scripts/check-no-output-eq.py` `split_params_and_conclusion`
truncated the binder list at the first Lean line-comment (`--`)
inside a binder gap, so `h_byte_sum_circuit` was **not** counted in
`trust/baseline-hypothesis-count.txt` or
`trust/baseline-caller-burden.txt` for any of the 9
byte-sum-circuit ops. The parser bug was fixed in commit `3800df2`
and the baselines refreshed accordingly: each of the 9 ops now
shows `total=25 hypothesis=16` (was 24/15) with
`h_byte_sum_circuit` visible at index 024 in the caller-burden
ledger.

**Round 3 re-attempt under fixed metric — still skipped.** With
the parser fix in place, dropping `h_byte_sum_circuit` now scores
as `−1 total / −1 hypothesis` per opcode. The two discharge
routes (Tier-3 promotion, arith-correctness axiom) were
re-evaluated against the corrected metric:

* **Tier-3 promotion** still INFLATES. Concrete comparison: the
  successful unsigned siblings `equiv_MUL` / `equiv_MULHU` /
  `equiv_DIVU` / `equiv_REMU` carry `total=47..49 hypothesis=35..37`
  — i.e. Tier-3 promotion costs ~24 binders per opcode (`v`,
  `r_a`, 8 chunk ranges already absorbed into ranges discharge,
  `h_chain`, 7 mode pins, `h_byte_lo`, `h_byte_hi`, `h_op1`,
  `h_op2`, plus the carry-chain witness pack absorbed by the
  Bridge helper). Net per-opcode metric: `−1 + 24 = +23 total` —
  still strongly regressive.

* **Narrow Arith-correctness axiom** would have to assert
  `e2.bytes = operand-form spec output` (or an intermediate
  equivalent tying e2 lanes directly to operand arithmetic).
  Tracing the dependency chain in the constructive direction:
  `e2.bytes → LaneMatch (Main.c lanes) → matches_entry (Arith
  bus_res0/1) → Bridge1 (c_chunks_packed / a_chunks_packed /
  d_chunks_packed) → carry chain (a_packed * b_packed) → operand
  packing (r1_val / r2_val)`. To bypass this chain in a single
  axiom requires asserting full Arith correctness at the bus
  layer, which is **the spec equivalence itself** — a new trust
  *kind* (output-form assertion), not range / lookup / permutation
  soundness. Per `CLAUDE.md`'s anti-laundering principle, "every
  new axiom must fit one of the 11+ trust classes already
  documented … with a citation to a specific PIL line, Rust
  function, or protocol-soundness theorem. New trust *kinds* are
  a separate prior PR with explicit justification." Escalation
  point reached; no axiom landed in this attempt.

**Decision (Round 3, parser-fix-aware):** all 9 byte-sum-circuit
ops (MULH / MULHSU / MULW / DIV / DIVW / DIVUW / REM / REMW /
REMUW) remain deferred. Tier-3 promotion is mechanically possible
but anti-laundering-regressive; a narrow arith-correctness axiom
requires a new trust kind. Either route is a separate prior PR
with explicit justification. Pre-existing skip rationale in
commit `cf1900e` retained; this round's refresh adds no axioms,
no binder drops, and no commits beyond the IOU-tracking
documentation update.

### Arith Div (8 ops: DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW)

**Already discharged**:
- DIVU/REMU: 16 chunk-range hypotheses + 22-binder loose
  `(cy_i, h_cy_i, hC*)` carry-chain bundle (Round 2,
  commit `cf1900e`)
- DIV/DIVW/DIVUW/REM/REMW/REMUW: 8 e2 byte-range hypotheses (cleanup batch)

**Residual caller-burden:** mirror of Arith Mul, with additional:
| Binder | Discharge mechanism |
|---|---|
| `h_op2_ne : divu_input.r2_val.toNat ≠ 0` | Caller obligation — comes from Sail spec's pre-condition on division. Stays as Sail-input precondition (it's not a promise about the circuit). |
| `h_d_lt_b : <remainder constraint>` | Derive from `Valid_ArithDiv`'s row-level constraint on the d-quotient/remainder relationship + `arith_div_columns_in_range`. Substantial work. |

**Round 3 attempt — skipped (DIV / DIVW / DIVUW / REM / REMW / REMUW).**
Same `h_byte_sum_circuit` shape and same skip rationale as the
MULH / MULHSU / MULW analysis above (see Arith Mul section's
"Round 3 attempt — skipped" subsection). Each of these 6 opcodes
carries a single `h_byte_sum_circuit` promise that ties bus-entry
bytes to a pure operand-form integer expression (`Int.tdiv` /
`Int.tmod` / 32-bit-signed-DIVW / etc.). Both discharge routes
(Tier-2 → Tier-3 promotion, arith-correctness axiom) fail the
anti-laundering metric per opcode.

### Mem (7 ops: LD, LBU, LHU, LWU, SB, SH, SW, SD — plus signed-load LB/LH/LW which mostly route through `Circuit/SextLoadBridge.lean`)

**Already discharged**:
- LD: e1/e2 byte ranges
- LBU/LHU/LWU: e1/e2 byte ranges
- LB/LH/LW: byte ranges
- **Mem lift iteration (this PR, branch `lift-mem-discharge`):**
  LD / LBU / LHU / LWU each dropped 7 promise hypotheses
  (`h_main_emit_b`, `h_main_emit_c`, `h_ptr_match`, `h_rd_zero_iff`,
  `h_rd_idx`, `h_copy0`, `h_copy1`) via the new
  `ZiskFv.Equivalence.Bridge.Mem.{ld,lbu,lhu,lwu}_discharge_full`
  entry points consuming the new `main_load_emission_bundle` axiom
  (class #4, PIL-cited; `Airs/MemoryBus/MemBridge.lean`). Net
  metric change per opcode: total −7 / hypothesis −7 (LD); total
  −7 / hypothesis −7 (LBU / LHU / LWU). Anti-laundering metric
  strictly shrinks; trust ledger gains 1 axiom (84 → 96 active
  baseline entries after composing prior iterations and this one's
  addition).

**Residual caller-burden (after Mem-lift iteration):**

For LD / LBU / LHU / LWU — `h_main_emit_b`, `h_main_emit_c`,
`h_ptr_match`, `h_copy0`, `h_copy1`, `h_rd_zero_iff`, `h_rd_idx`
are all discharged via the new `main_load_emission_bundle` axiom
(class #4). `h_ext` and `h_op` remain at the canonical theorem
because they are the transpile-pinned activation hypotheses the
discharge consumes; they are derivable from `transpile_<OP>` once
`Compliance.lean` provides the Sail decode + the universal Main
row constraint set.

For LB / LH / LW — **lifted in round-3** (branch
`lift-mem-2-discharge`). The signed loads also emit memory-bus
entries through the same Main-row b/c-side `mem_op` calls as the
copyb loads; only the activation pin differs
(`is_external_op = 1`, `op = OP_SIGNEXTEND_{B,H,W}`). The new
`main_sext_load_emission_bundle` axiom (class #4, PIL-cited;
`Airs/MemoryBus/MemBridge.lean`) packages the same lane / ptr /
rd-routing facts as `main_load_emission_bundle` minus the copyb
passthrough (vacuous for external rows). The
`Bridge.Mem.{lb,lh,lw}_discharge_full` entry points consume it
to retire `h_main_emit_b`, `h_main_emit_c`, `h_ptr_match`,
`h_rd_zero_iff`, `h_rd_idx` — five hypotheses per opcode. Net
metric change: LB 42→37 (−5 total, hypothesis 25→20), LH 42→37
(−5 total, hypothesis 26→21), LW 45→40 (−5 total, hypothesis
28→23). Trust ledger gains 1 axiom (99 → 100 active baseline
entries after this iteration).

For SB / SH / SW / SD — **skipped (anti-laundering metric)**. The
store equivs accept simpler bridging premises (`h_mem_eq` for
SB/SH/SW; per-byte `h_byte_i` for SD) without a Main / Mem
validator binder. Introducing the validator + discharge call
would inflate the anti-laundering metric: SB/SH/SW currently have
1 bridge hypothesis (`h_mem_eq`); the round-3 attempt requires
adding 9 binders (`main`, `mem`, `r_main`, `h_ext`, `h_op` +
optional explicit bus-shape pins already present) to retire just
that 1 hypothesis. SD has 9 bridge hypotheses (`h_ptr_match` +
8 byte equalities), but the byte equalities tie to circuit
witnesses that don't appear in any current bundle — discharging
them would require either a per-byte store-emission axiom or a
deeper byte-bus closure. Both store cases would require new
discharge infrastructure not present in the load family; tracked
as a follow-up IOU. (See the "Anti-laundering principle" in
`CLAUDE.md`: per the operational metric, a refactor that holds
or grows `total` / `hypothesis` columns is not progress; this
attempt is paused until the byte-discharge primitive lands.)

Original (pre-lift) table preserved for reference:

| Binder | Discharge mechanism |
|---|---|
| `risc_v_assumptions` + `h_opcode_assumptions` | Platform inerts (already in trust ledger as classes 7-10); these are caller obligations on `state`, not promises about circuit |
| `h_main_emit_b`, `h_main_emit_c` (Main row emission of memory entries) | **DONE for unsigned + signed loads** — `main_load_emission_bundle` (copyb) and `main_sext_load_emission_bundle` (LB/LH/LW). **TODO for stores** — analogous axiom, but anti-laundering metric currently blocks the round-3 attempt (see store IOU note above). |
| `h_ptr_match` (e1.ptr ↔ r1 + signExt(imm)) | **DONE for all 7 loads.** Same axiom family. |
| `h_copy0`, `h_copy1`, `h_ext`, `h_op` (copyb / op pins for Main row) | **DONE for loads** — `h_copy0/1` via the bundle (unsigned loads only — vacuous for signed loads with `is_external_op = 1`); `h_ext/h_op` retained as transpile-pinned activation. |
| `h_rd_zero_iff`, `h_rd_idx` (Sail rd ↔ bus e2.ptr) | **DONE for all 7 loads.** Same axiom family. |

### ControlFlow non-branch (6 ops: AUIPC, JAL, JALR, LUI, FENCE)

**Already discharged**:
- AUIPC, JAL: 8 e_rd byte ranges (cleanup batch)
- JALR: 8 byte ranges (cleanup batch)

**Residual caller-burden:**
| Binder | Discharge mechanism |
|---|---|
| `h_circuit` (UType / ITypeArchetype mode pin) | Project from Main's row-level constraints + `transpile_<OP>` |
| `h_offset_bridge` (Main jmp_offset2 ↔ Sail-form imm) | `transpile_<OP>` (e.g., `transpile_AUIPC`) instantiated with `imm_offset = Sail-form sign-extended imm`. The transpile axiom takes `imm_offset` as a free parameter — instantiate at proof site. |
| `h_lane_lo`, `h_lane_hi` (PC lane match) | `LaneMatch.store_pc_lanes_match_{lo,hi}_of_bus_emission` (already in ledger) |
| `h_no_wrap`, `h_lo_bound`, `h_pc_offset_lt_2_32` (arithmetic bounds on PC + imm) | **Partially derivable**: `main_columns_in_range` gives `< 2^32`. Some imm-specific bounds may stay as Sail-input preconditions if they can't be derived from Main's range checks. |
| `h_input_imm` (Sail `<op>_input.imm = imm` BitVec data tautology) | Refl-trivial once Sail input is constructed from decoded instruction in `Compliance.lean` — vanishes in global theorem |

### ControlFlow branch (6 ops: BEQ, BNE, BLT, BLTU, BGE, BGEU)

**Already at minimum form** — no Provider-AIR cross-AIR promises. Caller
burden is structural (bus shape, Sail state inputs, misa check,
`h_not_throws`, `h_success`). These are NOT promises about the
circuit — they're Sail-side preconditions or bus-emission shape facts
that the global theorem provides via its own structural-shape
hypotheses.

**No IOU.**

## Open trust-ledger items

Two items would require new axioms (each fits an existing class):

1. **6-field `consumer_byte_match_chain` forward witness for Binary AIR.**
   Extends the existing 3-field `binary_per_byte_lookup_witness` to
   include `cin`/`flags`/`pos_ind` for SUB/SLT-shape chain projection.
   Trust class: lookup-soundness on the Binary table (same as #6 in
   trusted-base.md).

2. **Main memory-bus emission column shape** (NEW class). For Mem
   load/store, Main's `b_0/b_1` (load) and `c_0/c_1` (store) columns
   pack the entry's `memory_entry_lo`/`memory_entry_hi`. Currently
   `h_main_emit_b`/`h_main_emit_c` are caller-supplied; could be
   discharged if there were an axiom asserting Main's emission shape
   in those columns. Trust class would be analogous to existing
   memory-bus-emission axioms in `LaneMatch.lean`. Adding it requires
   PIL citation and CODEOWNER review.

## Sequencing for the IOU lift

1. **Compliance.lean (this PR)** — author with current per-opcode equivs.
   Preconditions inflate. Global theorem exists; case-split + dispatch
   works.
2. **BinaryExtension full discharge** — thicken `Bridge/BinaryExtension.lean`
   with per-opcode `<op>_discharge_full` entry points. Refactor
   11 shift equivs. Global theorem's BinExt preconditions shrink.
3. **Binary full discharge** + 6-field axiom — thicken
   `Bridge/Binary.lean`. Add 6-field forward axiom + ledger entry.
   Refactor 14 Binary equivs.
4. **Arith Mul/Div full discharge** — Tier-2 → Tier-3 promotion for
   MULH/MULHSU/MULW/DIV/DIVW/DIVUW/REM/REMW/REMUW. Carry-chain
   consumption via `mul_carry_chain_holds`.
5. **Mem full discharge** + Main emission axiom — `Bridge/Mem.lean`
   thickening. Add Main memory-bus emission axiom.
6. **ControlFlow non-branch full discharge** — `Bridge/ControlFlow.lean`
   thickening. Most discharges are existing-axiom chaining.
7. **Trust gate V3 (Step 5)** — add classifier that statically rejects
   reintroduction of any of these promise-hypothesis shapes after
   they've been lifted.

Each step is a separable PR. The global theorem `zisk_riscv_compliant_program_bus`
exists and compiles after step 1; its preconditions shrink at each
subsequent step until only `(AIR validators) + (∀ r, core_every_row)`
+ Sail state match + bus structural shape remain.

## Done state

After all 7 steps:

```lean
theorem zisk_riscv_compliant_program_bus
    (m : Valid_Main C FGL FGL)
    (b_BinaryAdd : Valid_BinaryAdd C FGL FGL)
    (b_Binary : Valid_Binary C FGL FGL)
    (e_BinExt : Valid_BinaryExtension C FGL FGL)
    (a_Mul : Valid_ArithMul C FGL FGL) (a_Div : Valid_ArithDiv C FGL FGL)
    (mem : Valid_Mem C FGL FGL)
    (mab : Valid_MemAlignByte C FGL FGL) (marb : Valid_MemAlignReadByte C FGL FGL)
    (ma : Valid_MemAlign C FGL FGL)
    (r_main : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_active : m.is_external_op r_main = 1)
    (h_riscv : RISC_V_assumptions state ...)
    (h_state_match : state_matches_main m r_main state)
    (h_main_constraints : ∀ r, Main.core_every_row m r)
    (h_b_BinaryAdd_constraints : ∀ r, BinaryAdd.core_every_row b_BinaryAdd r)
    (h_b_Binary_constraints : ∀ r, Binary.core_every_row b_Binary r)
    (h_e_BinExt_constraints : ∀ r, BinaryExtension.core_every_row e_BinExt r)
    (h_a_Mul_constraints : ∀ r, ArithMul.core_every_row a_Mul r)
    (h_a_Div_constraints : ∀ r, ArithDiv.core_every_row a_Div r)
    (h_mem_constraints : ∀ r, Mem.core_every_row mem r)
    (...other Mem-aligned providers similar...)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_rows : List (Interaction.MemoryBusEntry FGL))
    (h_exec_row_shape : <bus structural shape predicate>)
    (h_mem_rows_shape : <bus structural shape predicate>) :
  ∃ instr,
    decode_main_row m r_main = some instr ∧
    execute_instruction instr state = (bus_effect exec_row mem_rows state).2
```

`#print axioms zisk_riscv_compliant_program_bus` closure = the ~13
documented trust classes in `docs/fv/trusted-base.md` (the existing
12 + the new 6-field Binary forward witness + the new Main
memory-emission axiom = 14 if both new axioms land; or fewer if we
defer one of them).
