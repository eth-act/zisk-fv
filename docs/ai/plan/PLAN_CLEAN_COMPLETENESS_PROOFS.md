# Plan: Clean Completeness Proofs

Status: Wave 1 COMPLETE (PR #69). Waves 2–5 READY FOR EXECUTION.
This file is the handoff document — execute it without further design work.
Wave 1's merged code is the REFERENCE IMPLEMENTATION for everything below;
when this plan and that code disagree, copy the code.

## How to run a wave

- One worktree per wave: `git worktree add .worktrees/completeness-<wave>
  origin/main` (MANUALLY — never agent worktree isolation). Base must contain
  the Wave 1 merge (CompletenessHelpers + hardened witness gate).
- FIRST command in the new worktree: `lake exe cache get`. If it complains
  about missing path deps: `nix run .#populate`, retry. Then full
  `lake build` + `trust/scripts/check-all.sh` green BEFORE any edit.
- This plan file is tracked in the repo. Edit ONLY your wave's checklist
  boxes and append log lines prefixed `W<n>:`. Never touch another wave's
  section. On rebase conflicts in this file or STATUS.md, keep both sides.
- Commit and push freely on the wave branch.

### PR protocol (UPDATED 2026-06-12 — no human pre-ack needed)

When your wave's checklist is done and ALL verification commands pass, OPEN
THE PR YOURSELF — do not wait for permission. Requirements:

- Title: `Clean completeness Wave <n>: <components>`.
- First body line: `Queued for Claude review — do not merge.`
- Body sections, in order: Summary; Scope notes (any documented partial
  coverage — Wave 3 table ops, Wave 4 unsigned modes); Verification (paste
  the gate tails, the empty trust-diff confirmation, the closure-print
  result, and the witness file list); Notes for later waves (anything the
  next agents must copy or avoid).
- Review is performed by Claude (Cody's reviewing agent), not by you.
  Expect the review to: re-run both gates and the build, diff-check the
  baselines, grep for soundness-side edits, hand-check your builder against
  the constraint expressions, and negative-test your witness. Write the PR
  so all of that passes on the first try.
- After opening the PR, STOP. Do not merge, do not self-approve, do not
  start another wave's components.

### Sub-agent rule

Any sub-agent prompt must include the CLAUDE.md anti-laundering principle
verbatim and require reading `trust/README.md#anti-laundering-terms` first.
Vocabulary: this stream is **completeness / constructibility** work, NOT
promise discharge — use those words in PR titles/bodies/commits.

## Context

PR #66 (`2c862063`) demoted all dishonest Clean completeness fields to
explicit non-claims (`ProverAssumptions := fun _ _ _ => False`, ex-falso
bodies). History: the six original axioms were FALSE as stated (see
`ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS` in `trust/defects.md`), and
PR #56's "proofs" were circular (`ProverAssumptions := Spec row` restating
the constraints — reverted by PR #62 as a launder).

This stream upgrades all 16 demoted fields to GENUINE completeness proofs:
per component, an honest-row builder, a builder-existential
`ProverAssumptions`, a real proof, and a gate-wired anti-vacuity witness.
Purely additive: no axioms, no ledger changes, no canonical-theorem changes.
Wave 1 (PR #69) delivered MemAlign + BinaryAdd + helpers + the hardened
witness gate. Remaining fields:

| Component file (`ZiskFv/AirsClean/`) | Circuits to complete | Wave |
|---|---|---|
| MemAlignReadByte/Circuit.lean | `circuit` | 2 |
| MemAlignByte/Circuit.lean | `circuit` | 2 |
| Mem/Circuit.lean | `circuit`, `circuitWithMemBus`, `circuitWithDualMemBus` | 2 |
| Binary/Circuit.lean | `circuit`, `staticLookupCircuit` | 3 |
| BinaryExtension/StaticCircuit.lean | `staticLookupCircuit`, `shiftStaticLookupCircuit` | 3 |
| ArithMul/Circuit.lean | `circuit` | 4 |
| ArithDiv/Circuit.lean | `circuit` | 4 |
| Main/Circuit.lean | `circuit`, `circuitWithRomAndMemBus`, `circuitWithRomMemAndOpBus` | 5 |

`BinaryExtension/Circuit.lean` (plain, push-only) is already genuinely
complete — leave it untouched. Re-run `rg "completeness :=" ZiskFv` at the
start of your wave and reconcile against this table.

## Reference implementations (READ THE CODE FIRST)

Wave 1 proved the idiom end to end. Before writing anything, read:

| What you need | Copy from |
|---|---|
| Helpers (`boolF`, `boolF_booleanity`, `boolF_booleanity_add`, `fgl_natCast_val_lt_of_lt`) | `ZiskFv/AirsClean/CompletenessHelpers.lean` |
| Nat-operand builder + chunk/carry lemmas + range-lookup discharge | `ZiskFv/AirsClean/BinaryAdd/Circuit.lean` (builder `binaryAddRowOf`, lemmas `binaryAdd_*`, the `completeness :=` block) |
| Bool/enum-operand builder + computed mux columns + case-split proof | `ZiskFv/AirsClean/MemAlign/Circuit.lean` (`MemAlignPhase`, `memAlignRowOf`, the `completeness :=` block) |
| Witness file shape | `trust/consistency/completeness_witness_binaryadd.lean` and `_memalign.lean` |
| Scoped docstring wording (states what IS proved and what is NOT claimed) | The module docstrings of both Wave 1 files (post-`91679f42`) |
| Principled ensemble proof patterns (channel-name discrimination, `change` to the channel-list goal) | `ZiskFv/AirsClean/FullEnsemble.lean` MemAlign `.addTable` args; `FullEnsemble/Balance.lean::memAlign_table_interactionsWith_opBus_nil` and `binaryAdd_table_interactionsWith_memBus_nil` |

## The proven recipe (follow mechanically)

### 1. Builder

```lean
def <air>RowOf (<semantic operands>) : <Air>Row FGL := { <every column> := … }
```

- Dependent columns (carries, mux outputs, composed values, result chunks)
  are COMPUTED by the builder. Never operands.
- Boolean-constrained columns take `Bool` operands via `boolF`. Columns with
  a one-hot-or-idle constraint take a small enum (see `MemAlignPhase`).
- Columns not occurring in any constraint of the slice are free `FGL`
  operands (bundle as a `<Air>FreeCols` structure when there are many).
- Mux/composed columns must mirror the `Constraints.lean` expressions
  VERBATIM (with operands substituted) — then those constraints discharge by
  `ring`/`simp`, no case analysis on the muxed branches.

### 2. ProverAssumptions

```lean
ProverAssumptions := fun row _ _ =>
  ∃ <operands>, <semantic side-conditions> ∧ row = <air>RowOf <operands>
```

Side-conditions are SEMANTIC operand facts only: numeric ranges
(`a < 2^64`), Bool implications, table-entry coherence (Waves 3/5). A
side-condition that restates a constraint polynomial is the banned PR #56
shape and fails review. Keep the existential inline — no named Prop wrappers.

### 3. Completeness proof — the working skeleton

Narrow rows (≤ ~30 cols), as in BinaryAdd:

```lean
completeness := by
  circuit_proof_start [<Channels>, Lookup.completeness_def]  -- channels only if the circuit pushes
  obtain ⟨<operands>, hrow⟩ := h_assumptions
  injection hrow with h_<col1> h_<col2> …    -- one name per column, in order
  subst_vars
  -- then refine ⟨?_, …⟩ with one goal per lookup/assertZero and discharge
```

Wide rows (43-col Arith) or when `circuit_proof_start` is slow, as in
MemAlign:

```lean
set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
def circuit : … := { … with
  completeness := by
    circuit_proof_start_core
    simp only [<main defs>, circuit_norm, <message exprs>, <Channel>]
    obtain ⟨<operands>, hrow⟩ := h_assumptions
    rw [hrow] at h_input
    simp only [circuit_norm] at h_input
    injection h_input with h_<col1> …       -- nested rows: injection AGAIN per sub-struct
    <case splits> <;> simp [h_…, <builder defs>] <;> ring_nf <;> simp }
```

Per-goal discharge:

- **Range lookup** (`rangeTable32/16/8`):
  `simp only [RangeTables.rangeTable<N>, RangeTables.rangeStaticTable]`,
  then `exact fgl_natCast_val_lt_of_lt (by decide) (by omega)`.
- **Static-table lookup** (BinaryTable / BinaryExtensionTable / ROM): the
  goal is `∃ i, <tuple> = rowOfIndex i.val` (resp. `= program i`). Build the
  row FROM table indices so this closes with `exact ⟨i_k, rfl⟩` (Wave 3/5
  recipes below).
- **Booleanity**: `boolF_booleanity` / `boolF_booleanity_add` (the goal may
  arrive in `a + -b` normal form — the `_add` variant or
  `simpa only [sub_eq_add_neg]` handles it).
- **Carry/chunk equations**: prove the Nat identity by `omega` in a
  standalone lemma, cast via `congrArg (fun n : ℕ => (n : FGL))` +
  `push_cast`/`norm_num`, close with `linear_combination`. Keep power
  literals in ONE form per proof (CLAUDE.md trap #2).
- **Channel pushes**: no goal, or `trivial` — `circuit_proof_start
  [<Channel>]` absorbs them.

### 4. Witness file (verbatim shape from Wave 1)

`trust/consistency/completeness_witness_<air>.lean` (single lowercase word
after the prefix — the gate globs `completeness_witness_*.lean`):

```lean
import ZiskFv.AirsClean.<Air>.Circuit
namespace ZiskFv.TrustConsistency
open Goldilocks ZiskFv.AirsClean.<Air>

private def <air>WitnessRow : <Air>Row FGL := <air>RowOf <concrete operands>

private theorem <air>WitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions <air>WitnessRow data hint := by
  refine ⟨<concrete operands>, <side-condition proofs by norm_num/decide>, ?_⟩
  rfl

theorem completeness_witness_<air> :
    ∃ row : <Air>Row FGL, ∀ data hint, circuit.ProverAssumptions row data hint :=
  ⟨<air>WitnessRow, <air>WitnessProverAssumptions⟩

#print axioms completeness_witness_<air>
end ZiskFv.TrustConsistency
```

The semantic gate (check 6/6) discovers it automatically and FAILS on
`sorry` — `sorry` in a witness is caught mechanically, don't try. DO NOT
edit `trust/scripts/check-all-semantic.sh`; it is final as of `91679f42`.

### 5. Docstring (audit surface — reviewers read this first)

Replace the PR #66 "intentionally NOT claimed" comment with the Wave 1
post-fix wording style: state the proved scope ("Completeness is a
constructibility claim for rows equal to `<air>RowOf …` with <conditions>")
AND the explicit non-claims ("It does not claim that arbitrary input rows
are honest <Air> executions"; cross-row/out-of-slice caveats where relevant).

### 6. Ensemble call sites (perf trap — handle in the SAME PR)

`FullEnsemble.lean` and `FullEnsemble/Balance.lean` contain
`simp [circuit_norm, ZiskFv.AirsClean.<X>.component, …<elaborated>]` proofs
that unfold your component record. Once your completeness field is a large
term, those `simp`s can slow down or time out. Rule: after your component
edit, run `lake build ZiskFv.AirsClean.FullEnsemble` and `lake build
ZiskFv.AirsClean.FullEnsemble.Balance`. If slow or failing, convert YOUR
component's call sites to the Wave 1 patterns (statements unchanged, proof
bodies only):

- channel-subset arg: `(by change ([] : List (RawChannel FGL)) ⊆ _; simp)`
  or `(by simp [circuit_norm])`.
- `interactionsWith … = []` lemmas in Balance.lean:
  `change <Other>Channel.toRaw ∉ [<Mine>Channel.toRaw]`, then the
  name-discrimination block from
  `Balance.lean::memAlign_table_interactionsWith_opBus_nil`.
- Assumptions-consistency arg: `trivial` (all components have
  `Assumptions := True`).

Call sites by wave (grep `simp \[circuit_norm, ZiskFv` to get current
lines): Wave 2 — MemAlignByte, MemAlignReadByte, Mem.componentWithDualMemBus
(2 sites each in FullEnsemble.lean + 1 each in Balance.lean). Wave 3 —
Binary.staticLookupComponent, BinaryExtension.staticLookupComponent. Wave 4
— ArithMul.component, ArithDiv.component (ArithDiv has 2 Balance sites).
Wave 5 — Main sites were already converted in Wave 1; verify with the grep.

## Wave 1 — COMPLETE (PR #69)

- [x] Worktree + cache + green baseline; commit plan copy + STATUS.md.
- [x] `ZiskFv/AirsClean/CompletenessHelpers.lean`.
- [x] MemAlign builder + completeness + witness.
- [x] BinaryAdd builder + completeness + witness.
- [x] Globbing witness check in `check-all-semantic.sh` (+ post-review
      hardening: fails on `sorry`; also wraps check 5/5).
- [x] Gates; PR opened and review-fixed (`91679f42`).

Outcome notes for later waves: `lake build ZiskFv.AirsClean` is NOT a
target — use `lake build ZiskFv.AirsClean.<Component>.Circuit`. Broad
`simp` over component records in ensemble proofs is the main perf hazard
(section 6). The `injection`-based `h_input` split is reliable; name every
column in order.

## Wave 2 — byte/mem mux family (1 agent, 1 PR)

### Checklist

- [x] Worktree + cache + green baseline; STATUS.md; log line `W2: started`.
- [x] MemAlignReadByte builder + completeness + witness.
- [x] MemAlignByte builder + completeness + witness.
- [x] Mem shared builder + one shared constraints lemma + all 3 completeness
      fields + witness.
- [x] Docstrings per recipe §5; ensemble call sites per §6.
- [x] Verification block; open PR per protocol.

### MemAlignReadByte (`circuit`, smallest — do first)

Row columns: `sel_high_4b sel_high_2b sel_high_b direct_value composed_value
value_16b value_8b byte_value addr_w step`. Constraints (mirror
`Constraints.lean` exactly — counts in this plan are approximate): selector
booleanities + the composed-value reconstruction + a `rangeTable8` lookup on
`byte_value`.

Builder: `(s4 s2 s1 : Bool)` selectors; `(byteVal : ℕ)` with side-condition
`byteVal < 2^8`; `value_16b value_8b direct_value addr_w step : FGL` free;
`composed_value` COMPUTED as the `Constraints.lean` reconstruction
expression with `boolF`-substituted selectors (this component's Spec.lean
byte-factor polynomials show the shape — but transcribe from
Constraints.lean, which is what the proof must match). Discharge: booleanity
helper; reconstruction by `ring` after substitution (selector case analysis
NOT needed — the value is defined as the expression); range lookup via
`fgl_natCast_val_lt_of_lt`.

### MemAlignByte (`circuit`)

Superset with the write path. Row adds: `is_write written_composed_value
written_byte_value mem_write_values_0 mem_write_values_1 bus_byte`.
Builder adds: `(isWrite : Bool)`, `(writtenByteVal : ℕ)` with `< 2^8`
side-condition, `written_composed_value` computed like the read
reconstruction over the written byte, `mem_write_values_0/1` computed as the
`sel_high_4b` muxes, `bus_byte` computed as the `is_write` mux
(`boolF isWrite * (written_byte - byte) + byte`). All from
`Constraints.lean` verbatim. Discharge identical in kind to ReadByte; the
extra `rangeTable8` lookups close from the `< 2^8` side-conditions.

### Mem (3 circuits, ONE builder, ONE lemma)

Row columns: `addr step sel addr_changes step_dual sel_dual value_0 value_1
wr previous_step increment_0 increment_1 read_same_addr`. The 9 constraints:
booleanities (sel_dual, sel, addr_changes, wr) + the two implication
products (`(1-sel)*sel_dual`, `wr*(1-sel)`), the `read_same_addr`
definitional identity, and the two `(addr_changes*(1-wr))*value_i = 0`
zeroing constraints.

Builder:

```lean
def memRowOf (sel selDual wr addrChanges : Bool)
    (addr step stepDual previousStep increment_0 increment_1 v0 v1 : FGL) : MemRow FGL
-- sel/sel_dual/wr/addr_changes := boolF …
-- read_same_addr := (1 - boolF addrChanges) * (1 - boolF wr)   (computed)
-- value_0 := if addrChanges && !wr then 0 else v0   (same for value_1)

ProverAssumptions := fun row _ _ => ∃ sel selDual wr addrChanges …,
  (selDual = true → sel = true) ∧ (wr = true → sel = true)
  ∧ row = memRowOf …
```

Prove ONE lemma `memRowOf_constraintsHold` covering the 9 equations by
`cases` on the four Bools (the implications kill the impossible cases) +
`simp [boolF]`; the three completeness fields (`circuit`,
`circuitWithMemBus` with `[MemBusChannel]`, `circuitWithDualMemBus` with
`[MemBusChannel]`) each consume it. The bus variants add only trivially-true
Guarantees goals.

Risk: low. If the `if … then 0 else` form fights `circuit_norm`
normalization in `h_input`, switch the value columns to
`(1 - boolF addrChanges * (1 - boolF wr)) * v0`-style computed products —
either is honest; pick whichever makes the zeroing constraints close by
`ring`/`cases`.

## Wave 3 — table-lookup family (1 agent, 1 PR)

New content vs Wave 1: static-table membership obligations. Both tables are
`StaticTable`s with `Spec t := ∃ i : Fin tableSize, t = rowOfIndex i.val`
and DEFINITIONAL `contains_iff` (`BinaryTable.lean:382-388`,
`BinaryExtensionTable.lean:223-229`). **Primary recipe — the index route:
take table indices as operands.** The honest prover's lookups ARE table
rows, so `i_0 … i_7 : Fin tableSize` operands are fully honest, and every
lookup goal closes with `exact ⟨i_k, rfl⟩` — zero table semantics needed.

The work is making the 8 looked-up tuples consistent with SHARED row
columns. Method, mechanically:

1. Read the 8 `lookupMessage<k>` expressions in the component's
   Constraints/Circuit files. Each is a tuple of row-column expressions.
2. For each row column appearing in exactly one message: builder sets it to
   the corresponding projection of `rowOfIndex i_k`.
3. For each slot SHARED between messages (mode/flag packings, chained
   carries — e.g. message k's carry-out is message k+1's carry-in):
   side-condition equating the two entries' projections, e.g.
   `(rowOfIndex i_0.val).<slot> = (rowOfIndex i_1.val).<slot>`. These are
   semantic table-entry facts — allowed. Derive the EXACT side-condition
   list from the message expressions; do not guess.
4. The witness file instantiates concrete indices (compute a real op row's
   indices once, with explicit numerals and `decide`/`norm_num`) — this also
   proves the side-conditions are satisfiable.

Fallback (only if the index route stalls): builders over a documented op
subset computing result bytes via the table's defining function
(`rowOfIndex` composed with index arithmetic). Record any scope cut in the
PR body and the log — documented partial coverage is fine, silent narrowing
is not.

### Checklist

- [ ] Worktree + cache + baseline; STATUS.md; log `W3: started`.
- [ ] Survey: list the 8 message exprs + shared slots for Binary and
      BinaryExtension; write the derived side-condition list into the PR
      body (this is the review surface for honesty).
- [x] Binary plain `circuit` (7 assertZeros, no lookups): Bool mode flags
      (`mode32 result_is_a use_first_byte c_is_signed`, `carry_7 : Bool`);
      `b_op_or_sext` and `mode32_and_c_is_signed` COMPUTED; free byte/carry
      columns. Plain-recipe discharge.
- [x] Binary `staticLookupCircuit`: index-route builder extending the plain
      one + witness.
- [x] BinaryExtension `staticLookupCircuit` (0 assertZeros, 8 lookups):
      index-route builder + witness.
- [x] BinaryExtension `shiftStaticLookupCircuit`: same builder + whatever
      `ShiftB0RangeSpecFact` demands — read its definition first; expect a
      range/shape fact on `b_0`, supplied as an operand side-condition or by
      computing `b_0` from a bounded operand.
- [x] Docstrings §5 (state the index-route scope); ensemble call sites §6.
- [ ] Verification block; open PR per protocol.

W3: Binary plain `circuit` and Binary `staticLookupCircuit` completeness now
compile under `lake env lean ZiskFv/AirsClean/Binary/Circuit.lean`; static
lookups use explicit BinaryTable indices plus field-consistency side
conditions.
W3: Added `trust/consistency/completeness_witness_binary.lean`; it typechecks
and prints no `sorryAx`.
W3: BinaryExtension `staticLookupCircuit` and `shiftStaticLookupCircuit`
completeness now compile under `lake env lean
ZiskFv/AirsClean/BinaryExtension/StaticCircuit.lean`.
W3: Added `trust/consistency/completeness_witness_binaryextension.lean`; it
typechecks and prints no `sorryAx`.
W3: Focused component builds plus `lake build ZiskFv.AirsClean.FullEnsemble`
and `lake build ZiskFv.AirsClean.FullEnsemble.Balance` pass after converting
Wave 3 ensemble call sites away from broad component-record `simp`.

## Wave 4 — Arith pair, unsigned scope (1 agent, 1 PR)

Scope FIXED BY CODY: unsigned modes only (`na=nb=np=nr=m32=0`; MUL `div=0`,
DIV `div=1`; `fab=1`, `na_fb=nb_fa=0`). Signed/m32 modes are follow-up
disjuncts — say so in the docstrings and the PR body. Verified facts: these
component slices emit ONLY the 11 equations (3 sign pins + 8 carry-chain) —
no range checks on carries/chunks, no flag booleanities, no ArithTable
lookup. Carries are pinned only by the chain equations; since
`(65536 : FGL)` is a unit, each equation has a UNIQUE field solution for its
new carry — define carries as those solutions (they provably coincide with
the honest integer carries; note this in the docstring).

### Checklist

- [ ] Worktree + cache + baseline; STATUS.md; log `W4: started`.
- [ ] Shared `ZiskFv/Airs/Arith/CarryChainCompleteness.lean` — build it
      green BEFORE touching components:
      `chunk16 (x k : ℕ) := x / 65536 ^ k % 65536`; `chunk16_lt`;
      `nat_decomp4/8` (by `omega`); `fgl_decomp4/8` (`push_cast`);
      `fgl_65536_ne_zero : (65536 : FGL) ≠ 0 := by decide`;
      field-solved carries generic over `[Field F] (B : F) (hB : B ≠ 0)`:
      `cc0 e0 := e0 / B` … `cc6 … := (e0 + e1*B + … + e6*B^6) / B^7`;
      `chain_eq_0 : e0 - cc0*B = 0`; `chain_eq_k (k=1..6)`;
      `chain_last (h : Σ e_k*B^k = 0) : e7 + cc6 = 0`.
      If `field_simp` blows up: state pre-cleared forms
      (`cc_k * B^(k+1) = Σ_{j≤k} e_j*B^j` via `div_mul_cancel₀`) and
      `linear_combination` against those. Keep `65536` powers FACTORED.
- [ ] ArithMul `circuit` (11 assertZeros + OpBus push):
      `ArithMulFreeCols` = the 11 unconstrained columns (`sext div_by_zero
      div_overflow main_div main_mul signed range_ab range_cd op bus_res1
      multiplicity`); builder `arithMulRowOf (a b : ℕ) (free)` — a/b chunks
      via `chunk16`, c/d := chunks of `a*b` (the GENUINE product chunks),
      zero flags, `fab := 1`, carries := `cc_k` of this row's chain
      numerators. ProverAssumptions: `a < 65536^4 ∧ b < 65536^4 ∧ row = …`.
      Discharge: C6/7/8 `norm_num`; C31–C37 `linear_combination (chain_eq_k …)`;
      C38 via `chain_last` with `h_packed : ↑a * ↑b = c_packed + d_packed *
      B^4` from `fgl_decomp4 a/b` + `fgl_decomp8 (a*b)` + `Nat.cast_mul`.
- [ ] ArithDiv `circuit` (11 assertZeros, NO push — easier): operands
      `(c b : ℕ)` = dividend, divisor; a := chunks of `c / b`, d := chunks
      of `c % b`; side-conditions `c < 65536^4 ∧ b < 65536^4 ∧ b ≠ 0`
      (`b ≠ 0` is documentation honesty); `h_packed` from `Nat.div_add_mod`.
      Mul first, Div as template copy.
- [ ] Witnesses (e.g. `6 * 7` and `100 / 7`); docstrings §5 (unsigned scope
      + the field-solved-carry note); ensemble sites §6 (ArithDiv has TWO
      Balance.lean sites).
- [ ] Verification block; open PR per protocol.

MANDATORY mechanics for both: the `circuit_proof_start_core` route (the
plain tactic is too slow on 43-column rows — documented from the soundness
work), `set_option maxHeartbeats 4000000`, and NESTED `injection`:
`ArithMulRow`/`ArithDivRow` are `{chunks, flags, carries/aux}` sub-structs,
so the first `injection` yields sub-struct equations — `injection` each of
those again to reach per-column equations.

## Wave 5 — Main, 3 circuits + stream finalization (1 agent, 1 PR)

### Checklist

- [ ] Worktree + cache + baseline; STATUS.md; log `W5: started`.
- [ ] Plain `circuit` (9 assertZeros + OpBus emit). The internal-op
      conditionals force exactly three honest shapes:
      ```lean
      inductive MainExecKind (F)
        | external (op : F) (flag : Bool) (c_0 c_1 set_pc : F)
            -- builder: set_pc column := if flag then 0 else set_pc
        | internalFlag                 -- op := 0, c := 0, flag := 1, set_pc := 0
        | internalCopyB (set_pc : F)   -- op := 1, c_i := b_i, flag := 0
      ```
      plus `MainFreeCols` (a/b operands, pc, m32, ind_width, jmp offsets,
      store_pc, im_high_degree_2, segment_l1). Discharge by `cases k` +
      helpers.
- [ ] `circuitWithRomAndMemBus length program` — builder from the program
      ENTRY so the ROM lookup closes by construction:
      `RomFlagBits` (15 Bools, bit order of `romFlags`, main.pil:483-486);
      `packFlags : RomFlagBits → FGL` (verbatim `romFlags` polynomial);
      `mainRomRowOf (msg : ZiskRomMessage FGL) (bits) (k : MainRomExecKind)
      (free)` copying pc/op/ind_width/jmp_offsets/imm fields from `msg`.
      ProverAssumptions: `∃ i bits k free, (program i).flags = packFlags bits
      ∧ <kind coherence: external ↔ bits.is_external_op; internal kinds fix
      msg.op = 0/1> ∧ <flag=1 forces bits.set_pc = false> ∧ row = mainRomRowOf
      (program i) bits k free`. The lookup goal is
      `∃ j, eval … = program j` — close with `⟨i, …⟩` via the EXISTING
      `eval_romMessageExpr` / `eval_romFlagsExpr`
      (`Main/Constraints.lean:176,184`); mirror the unfold path of
      `romSpec_of_mainWithRomAndMemBus_constraints` (`Main/Circuit.lean`
      ~154). Ten data slots are `rfl` by construction; the flags slot closes
      by the `packFlags` hypothesis. Prove this as a STANDALONE
      `theorem mainWithRomAndMemBus_completeness` (not inline).
      Fallback if `circuit_proof_start` decomposes the lookup entry too
      eagerly: `_core` route, keep `h_input` whole, apply
      `Lookup.completeness_def` + `eval_romMessageExpr` manually, split
      `h_input` only for the assertZero goals. `MainRowWithRom` is a nested
      `{core, rom}` struct — nested `injection` as in Wave 4.
- [ ] `circuitWithRomMemAndOpBus`: ~15-line `simpa [mainWithRomMemAndOpBus,
      circuit_norm, OpBusChannel, MemBusChannel]` wrapper around the
      standalone theorem (mirror `mainWithRomMemAndOpBus_soundness`). Same
      ProverAssumptions for both.
- [ ] Witness: concrete 1-instruction `Program` + one honest row per
      `MainExecKind`; concrete `RomFlagBits` proving the coherence
      side-conditions are satisfiable.
- [ ] Finalization sweep (only after Waves 2–4 have merged): CLAUDE.md
      status paragraph (completeness fields now proved; state the Wave 3/4
      scopes); append an upgrade note to
      `ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS` in `trust/defects.md`;
      PROJECTS.md/STATUS.md closeout; list follow-ups (signed Arith
      disjuncts, table-op gaps). Do NOT touch `ZiskFv/Completeness/**`
      (the RV64IM stream's surface).
- [ ] Verification block; open PR per protocol.

## Hard invariants (every wave — violations fail review)

- ZERO new `axiom` / `sorry` / `opaque` / `partial def` / `unsafe def`.
  `git diff origin/main -- trust/` shows ONLY
  `trust/consistency/completeness_witness_*.lean` additions (the gate
  script is final; baselines and `trust/generated/*` byte-identical).
- Soundness fields, `Spec` definitions, `main` do-blocks, elaborated
  circuits, and all theorem STATEMENTS untouched. Ensemble proof-body
  conversions (§6) are the only permitted edits outside your component's
  new defs + the 16 field bodies + docstrings.
- ProverAssumptions: inline builder existential, semantic side-conditions
  only.
- Witness file lands in the SAME PR as its proofs.
- Edit surface: `ZiskFv/AirsClean/**`,
  `ZiskFv/Airs/Arith/CarryChainCompleteness.lean` (Wave 4),
  `trust/consistency/completeness_witness_*.lean`, FullEnsemble proof
  bodies per §6, docs. Nothing else.
- Never commit files from `~/ai-workflow`. No wall-time estimates. Plan
  edits limited to your own wave's boxes + `W<n>:` log lines.

## Verification (run in this order before opening the PR)

```bash
lake build ZiskFv.AirsClean.<Component>.Circuit   # inner loop, per component
lake build ZiskFv.AirsClean.FullEnsemble          # ensemble perf check (§6)
lake build                                        # full
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh               # must show your witness in 6/6
nix run .#test
git diff origin/main -- trust/generated trust/baseline-axioms.txt \
  trust/baseline-hypothesis-count.txt trust/baseline-caller-burden.txt  # EMPTY
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
# no project axioms
```

Paste the gate tails, the empty-diff confirmation, the closure result, and
the witness file list into the PR body, then open the PR per the protocol
and STOP.

## Acceptance criteria (stream closeout, Wave 5)

1. All 16 demoted fields are genuine proofs with builder-existential
   ProverAssumptions; the already-honest BinaryExtension plain field
   untouched; every scope restriction stated in docstrings and listed as
   follow-ups here.
2. ≥10 `trust/consistency/completeness_witness_*.lean` files typecheck
   inside the semantic gate's 6/6 check.
3. Ledgers and anti-laundering baselines byte-identical to base; closure
   print unchanged; `nix run .#test` green on every PR.
4. PR bodies use completeness/constructibility vocabulary and carry the
   verification evidence.

## Log

(append one line per milestone; do not expand the plan body)

- 2026-06-12: Wave 1 worktree `clean-completeness-wave1` created from
  `origin/main` at `e3b87fc0`; generated inputs populated via Nix; `repl`,
  full `lake build`, and `trust/scripts/check-all.sh` are green at baseline.
- 2026-06-12: added `ZiskFv.AirsClean.CompletenessHelpers` with `boolF` and
  `boolF_booleanity`; `lake build ZiskFv.AirsClean.CompletenessHelpers` passed.
- 2026-06-12: MemAlign builder, completeness proof, and witness added; focused
  `lake build ZiskFv.AirsClean.MemAlign.Circuit` and witness typecheck passed.
- 2026-06-12: BinaryAdd builder, completeness proof, and witness added; focused
  `lake build ZiskFv.AirsClean.BinaryAdd.Circuit` and witness typecheck passed.
- 2026-06-12: Full `lake build`, `trust/scripts/check-all.sh`, and
  `trust/scripts/check-all-semantic.sh` passed; semantic gate glob picked up
  BinaryAdd and MemAlign completeness witnesses.
- 2026-06-12: `nix run .#test` passed all 8 steps, including embedded V1/V2
  trust gates and flake reproduction.
- 2026-06-12: trust generated/baseline diff is empty; `trust/` diff is limited
  to witness files plus `check-all-semantic.sh`; canonical closure print shows
  no project axioms.
- 2026-06-12: BinaryAdd proof/gate chunk committed as `60c645c6`; next step is
  push and review PR without merging.
- 2026-06-12: opened review PR https://github.com/eth-act/zisk-fv/pull/69;
  do not merge until external review completes.
- 2026-06-12: review feedback in progress: harden semantic witness checks to
  fail on Lean `sorry` warnings and refresh stale BinaryAdd/MemAlign docstrings.
- 2026-06-12: addressed review feedback; temporary sorry witness made the
  semantic gate fail as expected, then focused BinaryAdd/MemAlign build,
  `trust/scripts/check-all-semantic.sh`, `trust/scripts/check-all.sh`,
  `bash -n trust/scripts/check-all-semantic.sh`, and `git diff --check` passed.
- 2026-06-12: review feedback fix pushed to PR #69 as `91679f42`; next step is
  external review, do not merge.
- 2026-06-12: plan strengthened for Waves 2–5 (Cody-directed): Wave 1 recipe
  promoted to reference implementation, Wave 3 index-route made primary,
  ensemble call-site duty (§6) added, PR protocol switched to
  queue-for-Claude-review with no human pre-ack.
- W2: 2026-06-12: started Wave 2 worktree `clean-completeness-wave2` from
  `origin/clean-completeness-wave1` at `5c10ecc6` because `origin/main` does
  not yet contain Wave 1; populated generated inputs, initialized pinned
  `zisk` submodule, and passed `lake exe cache get`, `lake build repl`, full
  `lake build`, and `trust/scripts/check-all.sh`.
- W2: 2026-06-12: MemAlignReadByte builder, completeness proof, and witness
  added; focused `lake build ZiskFv.AirsClean.MemAlignReadByte.Circuit` and
  witness typecheck passed.
- W2: 2026-06-12: MemAlignByte builder, completeness proof, and witness added;
  focused `lake build ZiskFv.AirsClean.MemAlignByte.Circuit` and witness
  typecheck passed.
- W2: 2026-06-12: Mem shared builder, constraints lemma, all three
  completeness fields, and witness added; focused
  `lake build ZiskFv.AirsClean.Mem.Circuit` and witness typecheck passed.
- W2: 2026-06-12: Wave 2 docstrings updated; stale non-claim scan is clean;
  `lake build ZiskFv.AirsClean.FullEnsemble` and
  `lake build ZiskFv.AirsClean.FullEnsemble.Balance` passed with no ensemble
  call-site edits needed.
- W2: 2026-06-12: final Wave 2 verification passed: full `lake build`,
  `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
  `nix run .#test`, empty trust generated/baseline diff against
  `origin/clean-completeness-wave1`, `git diff --check`, clean status after
  restoring generated `zisk/lib-float` artifacts, and closure print with no
  project axiom lines.
- W2: 2026-06-12: opened review PR
  https://github.com/eth-act/zisk-fv/pull/70 against
  `clean-completeness-wave1`; queued for Claude review, do not merge.
