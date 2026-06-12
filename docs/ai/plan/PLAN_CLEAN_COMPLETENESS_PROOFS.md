# Plan: Clean Completeness Proofs

Status: READY FOR EXECUTION. Base: `origin/main` at `e3b87fc0` or later.
This file is the handoff document — it is written to be executed by agents
without further design work. Read it fully before editing anything.

## How to run this stream

- One worktree per wave: `git worktree add .worktrees/completeness-<wave>
  origin/main` (create MANUALLY — never agent worktree isolation).
- FIRST command in every new worktree: `lake exe cache get`. If it complains
  about missing path deps, run `nix run .#populate`, then retry. Then a full
  `lake build` + `trust/scripts/check-all.sh` BEFORE any edit (green baseline).
- Copy this plan into the worktree's `docs/ai/plan/` and commit it there
  (docs/ai is local-excluded in the parent checkout). Keep the worktree's
  `STATUS.md` and this file's checklists current at every progress report.
  Tick checkboxes and append short log lines only — do NOT expand this plan.
- Commit and push freely on the wave branch. ASK CODY before opening each PR.
- Wave 1 goes first and fixes the idiom. Waves 2–5 run in parallel after
  Wave 1's PR merges (they copy its idiom; Waves 2,3,5 also use its helpers).
- Sub-agent prompts must include the CLAUDE.md anti-laundering principle
  verbatim and require reading `trust/README.md#anti-laundering-terms`.
  Vocabulary note: this stream is **completeness / constructibility** work,
  NOT promise discharge — use those words in PR titles/bodies/commits.

## Context

PR #66 (`2c862063`) demoted all dishonest Clean completeness fields to
explicit non-claims: `ProverAssumptions := fun _ _ _ => False` with ex-falso
bodies. History: the six original axioms were FALSE as stated (trivial
ProverAssumptions over input-only rows — see
`ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS` in `trust/defects.md`), and
the earlier PR #56 "proofs" were circular (`ProverAssumptions := Spec row`
where Spec restates the constraints — reverted by PR #62 as a launder).

This stream upgrades all 16 demoted fields to GENUINE completeness proofs:
for each component, an honest-row builder, a builder-existential
`ProverAssumptions`, a real proof, and a gate-wired anti-vacuity witness.
The payoff is proved satisfiability of each constraint slice by honest rows
(constructibility), which also protects the soundness theorems from
overstrong-validator vacuity. Purely additive: no axioms, no ledger changes,
no canonical-theorem changes.

The 16 fields (post-#66 tree; re-run `rg "completeness :=" ZiskFv` and
reconcile before starting — line numbers drift):

| Component file (`ZiskFv/AirsClean/`) | Circuits to complete | Wave |
|---|---|---|
| BinaryAdd/Circuit.lean | `circuit` | 1 |
| MemAlign/Circuit.lean | `circuit` | 1 |
| MemAlignReadByte/Circuit.lean | `circuit` | 2 |
| MemAlignByte/Circuit.lean | `circuit` | 2 |
| Mem/Circuit.lean | `circuit`, `circuitWithMemBus`, `circuitWithDualMemBus` | 2 |
| Binary/Circuit.lean | `circuit`, `staticLookupCircuit` | 3 |
| BinaryExtension/StaticCircuit.lean | `staticLookupCircuit`, `shiftStaticLookupCircuit` | 3 |
| ArithMul/Circuit.lean | `circuit` | 4 |
| ArithDiv/Circuit.lean | `circuit` | 4 |
| Main/Circuit.lean | `circuit`, `circuitWithRomAndMemBus`, `circuitWithRomMemAndOpBus` | 5 |

`BinaryExtension/Circuit.lean` (plain circuit, push-only) is ALREADY genuinely
complete with `ProverAssumptions := True` — leave it untouched.

## Technical groundwork (verified 2026-06-12 — trust this, don't re-derive)

What `GeneralFormalCircuit.Completeness` demands, per operation in `main`:

- `assertZero e` → goal `env e = 0` (a Goldilocks field equation).
- `lookup (Table.fromStatic t) entry` → goal = `t.Spec (eval env entry)`,
  reached via `Lookup.completeness_def`
  (`build/clean-lean/Clean/Circuit/Lookup.lean:107`; StaticTable's
  `Completeness := Spec` at `Lookup.lean:137-153`). For
  `rangeTable32/16/8` the Spec is `val < 2^32 / 2^16 / 2^8`
  (`ZiskFv/AirsClean/RangeTables.lean:58-74`). For the ROM table the Spec is
  `∃ i, msg = program i` (`ZiskFv/AirsClean/ZiskInstructionRom.lean:56-67`).
- `OpBusChannel.push` / `MemBusChannel.emit` → goal `Guarantees env`, which
  is `True` for both buses (`ZiskFv/Channels/OperationBus.lean:145`,
  `ZiskFv/Channels/MemoryBus.lean:105`). `circuit_proof_start [<Channel>]`
  discharges these automatically.
- `env.UsesLocalWitnessesCompleteness` is a HYPOTHESIS and is vacuously true
  for every component here (`localLength = 0`, no witness ops/subcircuits).
- Binder order after the statement unfolds: `offset env input_var h_env
  input h_input h_assumptions ⊢ ConstraintsHold.Completeness … ∧ ProverSpec …`.
  With `ProverSpec := True` the second conjunct is `trivial`.
- `circuit_proof_start` handles completeness goals (recognizes
  `GeneralFormalCircuit.Completeness`,
  `build/clean-lean/Clean/Utils/Tactics/CircuitProofStart.lean:65-69`).
  For WIDE rows (43-column ArithMul/ArithDiv) its `provable_struct_simp` is
  too slow — use `circuit_proof_start_core` + `subst` + targeted
  `simp only [circuit_norm, main]`, exactly as the existing
  `ArithDiv.circuit.soundness` does (`ZiskFv/AirsClean/ArithDiv/Circuit.lean`).
- Nothing downstream consumes `completeness` or `ProverAssumptions`
  (`FormalEnsemble` has no completeness field) — these edits cannot break
  soundness consumers; `lake build` confirms per wave.

## The idiom (fixed — every component follows this exactly)

```lean
/-- Honest row for <Air>: <one-line semantics>. Dependent columns are
    COMPUTED from operands; columns outside this constraint slice are free. -/
def <air>RowOf (<semantic operands>) (free : <Air>FreeCols FGL) : <Air>Row FGL :=
  { <col> := <computed or copied> , … }

-- in the circuit definition:
    ProverAssumptions := fun row _ _ =>
      ∃ <operands> free, <semantic side-conditions> ∧ row = <air>RowOf <operands> free
    ProverSpec := fun _ _ _ => True
    completeness := by
      circuit_proof_start [<Channel names>]      -- or _core route for wide rows
      obtain ⟨<operands>, free, h_side, rfl⟩ := h_assumptions
      -- h_input : eval env input_var = <air>RowOf …; split per-column:
      --   simp only [circuit_norm] at h_input; dsimp only [<air>RowOf] at h_input
      --   then `<Air>Row.mk.injEq` / `injection` to get per-column equations,
      --   rewrite them into the constraint goals.
      refine ⟨?_, …⟩  -- one goal per assertZero/lookup, then discharge
```

Rules:

1. Dependent columns (carries, mux outputs, composed values, c-chunks) are
   computed BY the builder. Never operands.
2. Side-conditions are SEMANTIC operand facts only: numeric ranges
   (`a < 2^64`), `Bool`-typed flags, program-entry coherence. A
   side-condition that restates a constraint polynomial = the PR #56 launder
   = reject the work.
3. Free columns (not occurring in any constraint of the slice) are bundled in
   a `<Air>FreeCols` structure so honesty is maximal (any honest value
   allowed).
4. Replace the PR #66 doc comment ("Completeness is intentionally NOT
   claimed…") with one stating what IS now proved, including scope caveats.
5. New top-level defs get the hidden-promise review: builders and FreeCols
   are constructive data (fine as plain defs); do NOT introduce named Prop
   abbreviations for ProverAssumptions — keep the existential inline and
   visible.
6. Every component ships, in the same PR, a witness file
   `trust/consistency/completeness_witness_<air>.lean`: concrete operands,
   `example`/`theorem` applying the proved completeness statement or at
   minimum proving `ProverAssumptions (<air>RowOf <concrete>) …` is
   inhabited and the row satisfies the constraint equations. Follow the
   structure of `trust/consistency/load_byte_agreement_witness.lean`
   (private defs + one public theorem). Prefer `decide`/`norm_num` over
   `native_decide` where feasible.

## Gate wiring (Wave 1 does this ONCE)

Add to `trust/scripts/check-all-semantic.sh`, after the existing check 5/5,
a single globbing check so later waves add witness files without ever
editing the script (no merge conflicts):

```bash
run_witnesses() {
  local ok=0
  for f in trust/consistency/completeness_witness_*.lean; do
    [ -e "$f" ] || continue
    lake env lean "$f" || ok=1
  done
  return $ok
}
run "6/6 Clean completeness witnesses" run_witnesses
```

(Match the script's existing `run` helper conventions; renumber the label if
the script counts checks differently.)

## Wave 1 — pilot: helpers + MemAlign + BinaryAdd (1 agent, 1 PR)

### Checklist

- [x] Worktree + cache + green baseline; commit plan copy + STATUS.md.
- [x] `ZiskFv/AirsClean/CompletenessHelpers.lean`: `boolF`,
      `boolF_booleanity`, shared plumbing lemmas discovered during the pilot.
- [ ] MemAlign builder + completeness + witness.
- [ ] BinaryAdd builder + completeness + witness.
- [ ] Globbing witness check in `check-all-semantic.sh`.
- [ ] Gates (see Verification); ask Cody; open PR.
- [ ] Record in the PR body any idiom adjustments waves 2–5 must copy.

### Helpers

```lean
def boolF (b : Bool) : FGL := if b then 1 else 0
@[simp] lemma boolF_booleanity (b : Bool) : boolF b * (1 - boolF b) = 0 := by
  cases b <;> simp [boolF]
```

### MemAlign (`MemAlign/Circuit.lean::circuit`, 16 assertZeros + MemBus emit, no lookups)

Lowest-risk validation of the existential/`h_input` idiom. Constraints:
12 booleanities + `preL1 * pc = 0` + `sel_prove * (sel_up + sel_down) = 0`
+ two 8-way multiplexer value reconstructions (`Spec.lean:50-88`,
`Constraints.lean:54-78`).

Builder vocabulary:

```lean
inductive MemAlignPhase | prove | upToDown | downToUp | idle
-- maps to (sel_prove, sel_up_to_down, sel_down_to_up) ∈ {(1,0,0),(0,1,0),(0,0,1),(0,0,0)}
-- NOTE sel_prove has NO booleanity constraint; the phase enum keeps it honest.

def memAlignRowOf (phase : MemAlignPhase) (isBoot wr reset : Bool)
    (sel_0 … sel_7 : Bool) (reg_0 … reg_7 : FGL)
    (addr offset width step delta_addr pcVal : FGL) : MemAlignRow FGL
-- pc := if isBoot then 0 else pcVal; preL1 := boolF isBoot
-- value_0 / value_1 := the mux expressions from Constraints.lean VERBATIM,
--   with boolF/phase values substituted  ← this is the key trick
```

Discharge: booleanities by `boolF_booleanity`; `preL1*pc` by `cases isBoot`;
disjointness by `cases phase <;> norm_num [boolF]`; the two mux constraints
by `ring`/`sub_self` after substitution — NO selector case analysis, because
`value_0/1` are defined as the mux expressions. Watch the `a + -b` vs `a - b`
normal-form mismatch: `simpa only [sub_eq_add_neg]` (same fix as this file's
soundness proof). Channel: `circuit_proof_start [MemBusChannel]`.

### BinaryAdd (`BinaryAdd/Circuit.lean::circuit`, 4 assertZeros + 8 range lookups + OpBus push)

Validates the range-lookup discharge. Constraints (`Constraints.lean:60-66`):
2 carry booleanities + the two carry-equations over 32-bit limbs / 16-bit
chunks. Builder:

```lean
def binaryAddRowOf (a b : ℕ) : BinaryAddRow FGL :=
  -- a_0 := ↑(a % 2^32), a_1 := ↑(a / 2^32 % 2^32)  (same for b)
  -- s := (a + b) % 2^64; c_chunks_k := ↑(s / 2^16^k % 2^16) for k = 0..3
  -- cout_0 := ↑((a % 2^32 + b % 2^32) / 2^32)         -- 0 or 1
  -- cout_1 := ↑((a / 2^32 % 2^32 + b / 2^32 % 2^32 + carry0) / 2^32)

ProverAssumptions := fun row _ _ => ∃ a b, a < 2^64 ∧ b < 2^64 ∧ row = binaryAddRowOf a b
```

Discharge: booleanities — the quotient is 0/1 (`Nat.div_lt_iff` / `omega`),
then `cases`-style or `mul_self` arithmetic. The two carry equations: cast
the Nat identities `a%2^32 + b%2^32 = cout_0*2^32 + (low 32 bits of s)` (by
`omega` on the chunk definitions) into FGL via `push_cast`, then
`linear_combination`/`ring`. Lookups: `chunk < 2^32` / `< 2^16` facts are
`Nat.mod_lt`/`omega`; pipe through `Lookup.completeness_def` →
`rangeTable32.Spec` = `val < 2^32` (cast-of-small-Nat val lemma; check
`Fundamentals/Goldilocks.lean` for an existing `val_natCast`-style lemma
before writing one). CLAUDE.md trap #2 applies: write `4294967296` factored
consistently when `linear_combination` is involved.

## Wave 2 — byte/mem mux family (1 agent, 1 PR, after Wave 1)

- [ ] **MemAlignReadByte** (S): operands `(byteVal : ℕ < 2^8, value_8b
      value_16b : FGL, 3 sel Bools, addr_w step direct_value : FGL)`;
      `composed_value` computed via the byte-factor expressions from its
      Spec.lean; 3 booleanities + 1 `rangeTable8` lookup + composed-value
      equation by `ring` after substitution.
- [ ] **MemAlignByte** (M): superset with write path — also compute
      `written_composed_value`, `mem_write_values_0/1` (the `sel_high_4b`
      muxes), `bus_byte` (the `is_write` mux); 9 assertZeros + 3
      `rangeTable8` lookups. Same recipe; more columns.
- [ ] **Mem** (M): ONE builder serves all 3 circuits (the WithMemBus /
      WithDualMemBus variants only add trivially-true emits). Operands:
      `(sel sel_dual wr addr_changes : Bool)` with side-conditions
      `sel_dual → sel` and `wr → sel` (as Bool implications), values
      `(addr step value_0 value_1 previous_step increment_0 increment_1
      step_dual : FGL)`; builder zeroes `value_0/1` when
      `addr_changes ∧ ¬wr` and computes
      `read_same_addr := boolF (!addr_changes && !wr)`. All 9 constraints
      by `cases` on the four Bools + `boolF` simp; write the three
      completeness fields by proving ONE shared lemma and reusing it.
- [ ] Witness file per component; gates; ask Cody; PR.

## Wave 3 — table-lookup family (1 agent, 1 PR, after Wave 1)

The new content here is table-membership completeness: builders must COMPUTE
result bytes from the tables' defining semantics so the lookup obligations
(`t.Spec tuple`, via `contains_iff`) close. FIRST read the table definitions
(`ZiskFv/AirsClean/` BinaryTable / BinaryExtensionTable files) and the
existing lookup-witness lemmas referenced in
`ZiskFv/ZiskCircuit/SextLoadBridge.lean` — reuse before writing new.

- [ ] **Binary plain `circuit`** (7 assertZeros): operands = 4 mode Bools +
      free byte/carry columns; `b_op_or_sext` and `mode32_and_c_is_signed`
      computed. Easy.
- [ ] **Binary `staticLookupCircuit`** (+8 BinaryTable lookups): builder
      takes per-byte op inputs `(op : <table op enum/code>, a_i b_i bytes,
      carry-in)` and computes `c_i` bytes + carry-out from the table's
      defining function. If universal membership proofs are heavy, SCOPE the
      existential to a documented subset of ops (e.g. ADD-family rows) —
      same honesty rule as Wave 4's unsigned scope: documented partial
      coverage is fine, silent narrowing is not. Record chosen scope in the
      PR body and this file's log.
- [ ] **BinaryExtension `staticLookupCircuit` + `shiftStaticLookupCircuit`**
      (0 assertZeros; 8 BinaryExtensionTable lookups; shift variant adds the
      `ShiftB0RangeSpecFact` obligation): builder computes the 16 result
      bytes for a chosen documented op scope (the SLL/SRL/SRA/SE families
      the table defines); `binary_extension_sext_*` lemmas are candidates
      for reuse.
- [ ] Witnesses; gates; ask Cody; PR.

## Wave 4 — Arith pair, unsigned scope (1 agent, 1 PR, after Wave 1)

Scope DECIDED BY CODY: unsigned modes only (`na=nb=np=nr=m32=0`; MUL:
`div=0`; DIV: `div=1`). Signed/m32 modes are follow-up disjuncts
(`∨ row = …SignedRowOf …`) — record as follow-up at closeout, and say so in
the builder docstrings. Key verified facts: the AirsClean Arith components
constrain ONLY the 11 equations (3 sign pins + 8 carry-chain) — no range
checks on carries/chunks, no flag booleanities, no ArithTable lookup (those
live elsewhere). So carries are pinned only by the chain equations, and since
`(65536 : FGL)` is a unit each equation has a UNIQUE field solution for its
new carry — define carries as those solutions; they provably coincide with
the honest integer carries.

- [ ] New shared `ZiskFv/Airs/Arith/CarryChainCompleteness.lean`
      (pure math, build it green before touching components):
      - `def chunk16 (x k : ℕ) : ℕ := x / 65536 ^ k % 65536`;
        `chunk16_lt : chunk16 x k < 65536`.
      - `nat_decomp4` / `nat_decomp8`: `x < 65536^4 (resp ^8)` →
        x = Σ chunk16 x k * 65536^k (by `omega`).
      - `fgl_decomp4` / `fgl_decomp8`: the FGL casts (`push_cast`).
      - `lemma fgl_65536_ne_zero : (65536 : FGL) ≠ 0 := by decide`.
      - Field-solved carries, generic over `[Field F] (B : F) (hB : B ≠ 0)`:
        `cc0 e0 := e0 / B`, …, `cc6 e0…e6 := (e0 + e1*B + … + e6*B^6) / B^7`;
        `chain_eq_0 : e0 - cc0*B = 0`; `chain_eq_k : e_k + cc_{k-1} - cc_k*B = 0`
        (k=1..6); `chain_last (h : Σ e_k*B^k = 0) : e7 + cc6 = 0`.
        If `field_simp` blows up, state pre-cleared forms
        (`cc_k * B^(k+1) = Σ_{j≤k} e_j*B^j` via `div_mul_cancel₀`) and
        `linear_combination` against those. Keep `65536` powers FACTORED
        (CLAUDE.md trap #2).
- [ ] **ArithMul** (`circuit`, 11 assertZeros + OpBus push):
      ```lean
      structure ArithMulFreeCols (F) where  -- the 11 columns in no constraint:
        sext div_by_zero div_overflow main_div main_mul signed
        range_ab range_cd op bus_res1 multiplicity : F
      def arithMulRowOf (a b : ℕ) (free : ArithMulFreeCols FGL) : ArithMulRow FGL
      -- a_k/b_k := chunk16 casts; c_k := ↑(chunk16 (a*b) k); d_k := ↑(chunk16 (a*b) (k+4))
      -- flags na nb np nr m32 div := 0; fab := 1; na_fb := nb_fa := 0
      -- carry_k := cc_k applied to this row's chain numerators e_k
      ProverAssumptions := fun row _ _ =>
        ∃ a b free, a < 65536^4 ∧ b < 65536^4 ∧ row = arithMulRowOf a b free
      ```
      Discharge: C6/C7/C8 by `norm_num` after substitution; C31–C37 by
      `linear_combination (chain_eq_k …)`; C38 via `chain_last` with
      `h_packed : ↑a * ↑b = c_packed + d_packed * B^4` from `fgl_decomp4 a/b`
      + `fgl_decomp8 (a*b)` + `Nat.cast_mul`. MANDATORY: the
      `circuit_proof_start_core` route (43-column row; pattern in this
      file's own soundness proof), `set_option maxHeartbeats 4000000` if
      needed.
- [ ] **ArithDiv** (`circuit`, 11 assertZeros, NO push — strictly easier):
      same skeleton; operands `(c b : ℕ)` = dividend, divisor; roles
      a := chunks of `c / b` (quotient), d := chunks of `c % b` (remainder);
      include `b ≠ 0` side-condition (documentation honesty — ZisK flags
      div-by-zero rows separately); `h_packed` from `Nat.div_add_mod`.
      Same agent, Mul first as the template.
- [ ] Witnesses (concrete a,b — e.g. 6×7 and 100/7); gates; ask Cody; PR.

## Wave 5 — Main, 3 circuits + finalization (1 agent, 1 PR, after Wave 1)

- [ ] **Plain `circuit`** (9 assertZeros + OpBus emit): the internal-op
      conditionals force exactly three honest shapes —
      ```lean
      inductive MainExecKind (F)
        | external (op : F) (flag : Bool) (c_0 c_1 set_pc : F)
            -- builder sets set_pc column := if flag then 0 else set_pc
        | internalFlag                  -- op := 0, c := 0, flag := 1, set_pc := 0
        | internalCopyB (set_pc : F)    -- op := 1, c_i := b_i, flag := 0
      ```
      plus `MainFreeCols` (a/b operands, pc, m32, ind_width, jmp offsets,
      store_pc, im_high_degree_2, segment_l1). All 9 goals by `cases k` +
      `boolF_booleanity` / `norm_num` / `ring`.
- [ ] **`circuitWithRomAndMemBus length program`** (adds 14 ROM-flag
      booleanities + the static ROM lookup + 3 MemBus emits). Builder takes
      the program ENTRY so the lookup closes by construction:
      ```lean
      structure RomFlagBits where  -- 15 Bools, bit order of romFlags (main.pil:483-486)
        a_src_imm a_src_mem is_precompiled b_src_imm b_src_mem is_external_op
        store_pc store_mem store_ind set_pc m32 b_src_ind a_src_reg b_src_reg
        store_reg : Bool
      def packFlags (bits : RomFlagBits) : FGL  -- verbatim romFlags polynomial shape
      def mainRomRowOf (msg : ZiskRomMessage FGL) (bits : RomFlagBits)
          (k : MainRomExecKind FGL) (free : MainRomFreeCols FGL) : MainRowWithRom FGL
      -- pc/op/ind_width/jmp_offsets/imm fields copied from msg;
      -- flag columns := boolF of bits; flag/c columns from k as in plain Main
      ProverAssumptions := fun row _ _ => ∃ i bits k free,
        (program i).flags = packFlags bits        -- entry decodes to these bits
        ∧ <kind coherence: external ↔ bits.is_external_op; internal kinds fix msg.op = 0/1>
        ∧ <flag=1 cases force bits.set_pc = false>
        ∧ row = mainRomRowOf (program i) bits k free
      ```
      ROM lookup obligation unfolds to `∃ i, eval … = program i` — close with
      witness `i` using the EXISTING `eval_romMessageExpr` /
      `eval_romFlagsExpr` (`Main/Constraints.lean:176,184`); mirror the
      unfold path of `romSpec_of_mainWithRomAndMemBus_constraints`
      (`Main/Circuit.lean` ~line 154). The 10 data slots are rfl-equal by
      construction; the flags slot closes by the `packFlags` hypothesis.
      Fallback if `circuit_proof_start` decomposes the lookup entry too
      eagerly: `_core` route, keep `h_input` whole, apply
      `Lookup.completeness_def` + `eval_romMessageExpr` manually, split
      `h_input` only for the assertZero goals. Prove this as a STANDALONE
      `theorem mainWithRomAndMemBus_completeness …` (not inline).
- [ ] **`circuitWithRomMemAndOpBus`**: ~15-line `simpa [mainWithRomMemAndOpBus,
      circuit_norm, OpBusChannel, MemBusChannel]` wrapper around the
      standalone theorem — mirror `mainWithRomMemAndOpBus_soundness`
      (`Main/Circuit.lean` ~line 205). Same ProverAssumptions for both.
- [ ] Witness: a concrete 1-instruction `Program` + one honest row per kind.
- [ ] Finalization sweep (this wave, after all others merge): CLAUDE.md
      status paragraph (Clean completeness fields now proved; state the
      Arith/table scopes), append an upgrade note to
      `ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS` in `trust/defects.md`,
      PROJECTS.md/STATUS.md closeout, record follow-up items (signed Arith
      disjuncts, any table-op scope gaps). Do not edit the RV64IM
      completeness modules (`ZiskFv/Completeness/**`) — different stream.
- [ ] Gates; ask Cody; PR.

## Hard invariants (every wave — violations mean the PR is rejected)

- ZERO new `axiom` / `sorry` / `opaque` / `partial def` / `unsafe def`.
  `trust/allowed-axiom-files.txt`, `trust/tolerated-completeness-axioms.txt`,
  and ALL of `trust/generated/*` + `trust/baseline-*` must be byte-identical
  to base (`git diff origin/main -- trust/` shows only
  `check-all-semantic.sh` (Wave 1) and `trust/consistency/` additions).
- Soundness fields, `Spec` definitions, `main` do-blocks, and elaborated
  circuits UNTOUCHED. Builders/witnesses are new defs only.
- ProverAssumptions: inline existential over builder + semantic
  side-conditions. No constraint-equation side-conditions; no named Prop
  wrappers.
- Each component's witness file lands in the SAME PR as its proof.
- Edit surface: `ZiskFv/AirsClean/**` (new defs + the 16 field bodies +
  doc comments), `ZiskFv/Airs/Arith/CarryChainCompleteness.lean`,
  `trust/consistency/completeness_witness_*.lean`,
  `trust/scripts/check-all-semantic.sh` (Wave 1 only), docs. Nothing else.
- Never commit files from `~/ai-workflow`. No wall-time estimates anywhere.

## Verification (every wave, in order)

```bash
lake build ZiskFv.AirsClean.<Component>.Circuit   # inner loop, per component
lake build                                        # full, before commit of a chunk
trust/scripts/check-all.sh                        # V1, seconds
trust/scripts/check-all-semantic.sh               # V2 + witness glob check
nix run .#test                                    # before PR
git diff origin/main -- trust/generated trust/baseline-axioms.txt \
  trust/baseline-hypothesis-count.txt trust/baseline-caller-burden.txt  # must be empty
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
# must print no project axioms
```

Paste the gate tail, the empty-diff confirmation, and the witness file list
into each PR body.

## Acceptance criteria (stream closeout)

1. All 16 demoted fields are genuine proofs with builder-existential
   ProverAssumptions; the already-honest BinaryExtension plain field
   untouched; every scope restriction (Arith unsigned, table-op subsets)
   stated in docstrings and listed as follow-ups in this file.
2. ≥10 `trust/consistency/completeness_witness_*.lean` files typecheck
   inside the semantic gate's glob check.
3. Ledgers and anti-laundering baselines byte-identical to base; closure
   print unchanged; `nix run .#test` green on every PR.
4. PR bodies use completeness/constructibility vocabulary (not promise
   discharge) and include the verification evidence.

## Log

(append one line per milestone; do not expand the plan body)

- 2026-06-12: Wave 1 worktree `clean-completeness-wave1` created from
  `origin/main` at `e3b87fc0`; generated inputs populated via Nix; `repl`,
  full `lake build`, and `trust/scripts/check-all.sh` are green at baseline.
- 2026-06-12: added `ZiskFv.AirsClean.CompletenessHelpers` with `boolF` and
  `boolF_booleanity`; `lake build ZiskFv.AirsClean.CompletenessHelpers` passed.
