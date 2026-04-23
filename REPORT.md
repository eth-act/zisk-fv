# zisk-fv — Formal-verification report

**Scope.** Per-opcode equivalence of ZisK's zkVM circuit against the
[official Sail RISC-V specification](https://github.com/riscv/sail-riscv),
restricted to **RV64IM** (base integer + M extension).

**Status.** `lake build` green (8089 jobs, 0 errors, 0 `sorry`). 58/58
RV64IM opcodes proved. Trust base: 62 axioms, all catalogued with
closure paths in [`docs/fv/trusted-base.md`](docs/fv/trusted-base.md).

---

## 1. What is proved

For every opcode in the RV64IM subset (58 opcodes total), the project
exports a theorem of the canonical shape

```
theorem equiv_<OP>_metaplan … :
    execute_instruction (instruction.<Shape> (…, rop.<OP>)) state
      = (bus_effect exec_row mem_row state).2
```

where the LHS is the Sail spec (via `NethermindEth/sail-riscv-lean`'s
`LeanRV64D` module) and the RHS is ZisK's Goldilocks-valued circuit
constraints composed with the operation-bus model. Each theorem is
parameterized over the Valid-AIR witnesses (`Valid_Main`, `Valid_Binary`,
`Valid_ArithMul` / `Valid_ArithDiv` where applicable) and bus-match
hypotheses (same pattern as BinaryAdd's shape-(a) closure from Phase 1).

See the uniformity-lint roster at
[`tools/zisk-fv-lint/uniformity-lint.sh`](tools/zisk-fv-lint/uniformity-lint.sh)
for the machine-readable 58-opcode list.

## 2. What is assumed (the trust base)

Every axiom is narrow, per-opcode, and catalogued with a statement,
consumer list, provenance trace, and closure path in
[`docs/fv/trusted-base.md`](docs/fv/trusted-base.md). The **62** axioms
split as follows:

### 58 transpile axioms (`ZiskFv/ZiskFv/Fundamentals/Transpiler.lean`)

One `transpile_<OP>` axiom per RV64IM opcode. Each axiom is the
pure-functional spec of the corresponding arm in
[`vendor/zisk/core/src/riscv2zisk_context.rs`](vendor/zisk/core/src/riscv2zisk_context.rs) —
ZisK's Rust transpiler that lowers RV64 instructions to Zisk
microinstructions.

**Trust basis.** These axioms encode the transpiler's contract: "if the
Rust transpiler emits this row for opcode `<OP>`, the row has exactly
these field values." Retirement requires a Rust-side proof and is out of
scope for the Lean-side verification. An independent audit of the
transpile axioms against the Rust source is the natural next step for
project completion.

### 4 platform axioms (`ZiskFv/ZiskFv/RV64D/Auxiliaries.lean`, Phase 3.5)

| Label | Statement | Consumer scope |
|-------|-----------|----------------|
| **P1** | `pmpCheck_is_pure_none` | PMP (Physical Memory Protection) is disabled in the ZisK execution environment |
| **P2** | `within_clint_is_false` | The CLINT MMIO region is disjoint from user program memory |
| **P3** | `pmaCheck_is_pure_none` | The PMA (Physical Memory Attribute) check is inert for in-scope memory |
| **P4** | `update_elp_state_is_pure_unit` | Zicfilp (CFI landing-pad) is disabled |

These are scope-honest claims about the platform ZisK runs on. They
would retire only if ZisK's execution model changes to enable these
features.

### 0 Sail-equivalence axioms (retired Phase 4)

Phase 3A and 3C shipped 9 narrow Sail-equivalence axioms (C2a–d
branches, C5–C9 SLT-family + LW) in lieu of direct proofs. Phase 4
retired all 9 by porting the BNE proof skeleton to the branch opcodes
and closing the `BitVec.setWidth`/`BitVec.slt` bridge for the SLT-family
(along with fixing a Phase 3B statement bug in LW where `is_unsigned`
was set incorrectly). The affected RV64D files now carry direct lemmas;
the escape-hatch helper files (`SltEquivHelper`, `SltiEquivHelper`,
`LoadEquivHelper`) were deleted.

## 3. Caveats and residual structural parameters

### 3.1 Arith state-machine internal correctness

Theorems for the MUL family (MUL / MULH / MULHU / MULHSU / MULW, Phase
3A) and DIV/REM family (DIV / DIVU / REM / REMU, Phase 3C T-D) ship
with the following structural parameterization:

- The Main ↔ Arith bus-match projection (`mul_compositional` /
  `div_compositional`) proves Main's packed `c` equals Arith's packed
  output lanes. This **does not derive** the claim that Arith's output
  lanes equal the actual 64-bit product/quotient — that derivation
  requires deriving from Arith's 8-chunk × 16-bit carry chain
  (constraints 31–38 in `ZiskFv/ZiskFv/Extraction/Arith.lean`) the
  polynomial identity
  `(a[0] + … + a[3]*2^48) * (b[0] + … + b[3]*2^48) = (c[0] + … + c[3]*2^48) + (d[0] + … + d[3]*2^48) * 2^64`.

- The `equiv_<OP>_metaplan` theorems consume a `h_rd_match` structural
  hypothesis that the bus row's register-write bytes match the pure
  spec's `.rd` output. Proving this without the carry-chain derivation
  requires assuming Arith's internal correctness.

The 8-chunk carry-chain identity is a tractable `linear_combination`
proof (templated off BinaryAdd's 42-line Phase 1 closure), estimated
~300-500 lines in a new `Airs/Arith/CarryChain.lean` plus per-mode
specializations. This is deferred scope — the existing theorems are
usable in a trust-base mode "assume Arith's carry chains are correct"
identical to how BinaryAdd's permutation accumulator (`gsum`) is
treated.

### 3.2 Arith lookup-table witnesses

Even after carry-chain closure, three Arith sub-features remain
trusted:

1. **Sign-preprocessing table lookup** (constraints 6–8 of
   `Extraction/Arith.lean`) witnesses `(na, nb)` as the signs of
   `(a_packed, b_packed)` via a permutation argument against the
   `arith_table`. Not embedded in the Lean extraction.
2. **Stage-2 `range_cd` column** (constraint 46) range-checks the
   remainder bound `|d| < |b|` for signed DIV/REM via a 16-bit lookup.
3. **`inv_sum_all_bs`** — the multiplicative-inverse witness for the
   "divisor ≠ 0 ⇒ correct quotient" implication.

These are lookup-correctness claims orthogonal to the carry-chain
derivation; they stay trusted in the same scope-honest way the
BinaryAdd permutation accumulator is trusted.

### 3.3 Sample-level golden-trace coverage

Each opcode ships with ≥1 golden-trace witness fixture
(`ZiskFv/ZiskFv/GoldenTraces/*.lean`). Phase 4 demonstrated the
pattern for ≥3 fixtures per opcode (ADD, SUB, AND, SLT, MUL, LW
currently carry 3 fixtures each, exercising zero / max-value / sign-
boundary / overflow edge cases). The full 58 × 3 = 174-fixture matrix
is a mechanical extension; the harness at
[`tools/zisk-fv-harness/`](tools/zisk-fv-harness/) supports emission.

## 4. Known limitations (explicitly out of scope)

Per [`CLAUDE.md`](CLAUDE.md):

- **Zicclsm** (Compressed Load/Store Misaligned) extension.
- **Precompiles** — Keccak, SHA256, and other hash/crypto AIRs handled
  by ZisK's secondary state machines. Their internal correctness is
  outside the RV64IM verification scope.
- **ZisK custom internal ops** — ZisK's non-RISC-V microinstructions
  used for bookkeeping (`OP_FLAG`, `OP_COPYB` beyond its documented
  load-family role, etc.).
- The Sail RISC-V spec itself is a trusted input (per standard
  formal-verification practice against a reference specification).
- The `LeanRV64D` module's trusted axioms (floating-point primitives,
  reservation-set ops, `plat_term_write`, `get_16_random_bits`) are
  LeanRV64D's platform ops inherited as transitive dependencies.

## 5. Reproducing the build

```bash
git clone <this repo>
cd zisk-fv
cd ZiskFv && lake build          # ~8089 jobs on a cold cache
cd .. && git grep -n 'sorry' ZiskFv/ZiskFv/{Fundamentals,Airs,Spec,Equivalence,GoldenTraces,Tactics,RV64D}
# Expected: empty (no sorrys)
bash tools/zisk-fv-lint/uniformity-lint.sh
# Expected: "Uniformity lint PASSED. 58 opcodes expected; actual count follows." + roster
```

## 6. Project history

Development proceeded in phases, each closed with a CLOSED section
appended to its plan file in [`ai_plans/`](ai_plans/). Highlights:

- **Phase 0**: pilout-extractor spike (Rust tool
  [`tools/zisk-pil-extract/`](tools/zisk-pil-extract/)).
- **Phase 1 / 1.5**: ADD end-to-end (Sail + circuit) as the canonical
  compositional template.
- **Phase 2 / 2.5**: 6 archetype macros + 19 opcodes.
- **Phase 3A / 3B / 3C**: 39 more opcodes — all 58 RV64IM opcodes
  shipped.
- **Phase 3.5**: trust-base closure for memory-model (M1–M11), JALR
  (C1), ALU (C3a-c, C4).
- **Phase 4**: 9 Sail-equivalence axiom retirements (C2a–d, C5–C9);
  uniformity lint + top-level re-export audit; additional golden-trace
  fixtures; this REPORT.md.

## 7. Prior art

The project template was adapted from
[`openvm-fv`](https://github.com/Nethermind-Ordinals/openvm-fv) — the
Nethermind / OpenLabs formal verification of the OpenVM RV32IM zkVM
(45 opcodes). The pipeline shape — `Extraction/` → `Airs/` →
`RV<N>D/` → `Spec/` → `Equivalence/` — mirrors `openvm-fv`'s layout
while substituting ZisK's Goldilocks field, PIL2 constraint language,
and Main-AIR+secondary-SM+operation-bus architecture for `openvm-fv`'s
BabyBear + Plonky3 `SymbolicConstraintsDag` layer.
