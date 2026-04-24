# zisk-fv vs. openvm-fv — parity audit

**Date of audit:** 2026-04-24 (against `/home/cody/zisk-fv` @ `a1595bf` and
`/home/cody/openvm-fv` @ current `main`).

**Scope-honest trust** (transpiler, Sail spec, platform) is **by design**
and not a "gap" — both projects trust those surfaces. This doc captures
where zisk-fv's proof *structure* is weaker than openvm-fv's, so that
Phase 4.5+ work can close the delta.

## Reference point

The closest structural analogue to our `equiv_<OP>_metaplan` theorems in
openvm-fv is the RISC-V-equivalence theorem bundle in each
`OpenvmFv/Equivalence/<Family>.lean`. The concrete comparison below is
against `OpenvmFv/Equivalence/Mul.lean:540-597` (MUL's chip-bus + state
equivalence), chosen because it has a direct zisk-fv counterpart at
`ZiskFv/ZiskFv/Equivalence/Mul.lean:126-182`.

## openvm-fv's parameter list (RISC-V MUL equivalence)

```lean
(air : Valid_VmAirWrapper_mul FBB ExtF)             -- AIR structural mirror
(row : ℕ) (h_row : row ≤ air.last_row)              -- row in range
(h_constraints : allHold air row h_row)             -- PIL constraints at this row
(h_is_valid : air.core.is_valid row 0 = 1)         -- row is an active MUL row
(h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
(h_bus : (bus_effect _executionBus_row _memoryBus_row state).1) -- bus-effect precondition
```

## zisk-fv's parameter list (RISC-V MUL equivalence)

```lean
(state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
(mul_input : PureSpec.MulInput) (r1 r2 rd : regidx) (srs1 srs2 : Signedness)
(exec_row : List (Interaction.ExecutionBusEntry FGL))
(e0 e1 e2 : Interaction.MemoryBusEntry FGL)
-- Sail input parameters (DERIVED in openvm-fv, parameters in zisk-fv):
(h_input_r1 : read_xreg (regidx_to_fin r1) state = ok mul_input.r1_val state)
(h_input_r2 : read_xreg (regidx_to_fin r2) state = ok mul_input.r2_val state)
(h_input_rd : mul_input.rd = regidx_to_fin rd)
(h_input_pc : state.regs.get? Register.PC = .some mul_input.PC)
-- Bus wellformedness (decomposed; openvm-fv bundles these):
(h_exec_len : exec_row.length = 2)
(h_e0_mult : ...) (h_e1_mult : ...) (h_nextPC_matches : ...)
(h_m0_mult : ...) (h_m0_as : ...) (h_m1_mult : ...) (h_m1_as : ...)
(h_m2_mult : ...) (h_m2_as : ...)
-- rd correspondence (DERIVED in openvm-fv, parameter in zisk-fv):
(h_rd_match : if ... then pure () else write_xreg ... U64.toBV #v[e2.x0..e2.x7] = ...)
```

## Side-by-side

| Hypothesis | openvm-fv | zisk-fv | Gap? |
|-----------|-----------|---------|------|
| AIR structural mirror | `Valid_VmAirWrapper_mul` | `Valid_Main`, `Valid_ArithMul` (decomposed) | equal |
| PIL constraints hold | `h_constraints : allHold air row` | `h_circuit : <op>_circuit_holds` (bundles mode + bus-match + booleans) | equal |
| Row is an active opcode row | `h_is_valid` | folded into `<op>_circuit_holds` (`m.is_external_op = 1`, opcode literal) | equal |
| Bus-row wellformedness | `h_bus_wellformedness` (bundled) | `h_exec_len`, `h_e*_mult`, `h_m*_mult`, `h_m*_as`, `h_nextPC_matches` (decomposed, same content) | equal |
| Transpile contract used in proof | ✓ (`transpile_of_bus_wellformedness` consumed at `Mul.lean:478,560`) | ✗ (58 `transpile_<OP>` axioms declared in `Fundamentals/Transpiler.lean` but **zero proof-level consumers**) | **weaker — Gap 3** |
| Sail input state (`read_xreg rs1`, `rs2`, `PC`) | **derived internally** via `chip_bus_hypotheses` lemma | **parameters** (`h_input_r1`, `h_input_r2`, `h_input_pc`) | **weaker — Gap 1** |
| rd-write alignment | **derived internally** via `rd_neq_0` + transpile unfolding | **parameter** (`h_rd_match`) | **weaker — Gap 2** |
| Arith/Binary carry-chain → `BitVec` product | **derived** (RV32, BabyBear) | partially derived — pure-field unsigned 8-chunk identity shipped in `Airs/Arith/CarryChain.lean`; field→`BitVec 64` lift not shipped | **weaker (same kind of work) — part of Gap 2** |
| Transpiler trusted | ✓ (by design) | ✓ (by design) | equal |
| Sail spec trusted | ✓ (by design) | ✓ (by design) | equal |
| Platform axioms (PMP/CLINT/PMA/Zicfilp) | N/A (RV32 IM only, no privileged modes exercised) | 4 axioms (P1–P4) — scope-honest | equal (ours more explicit because RV64 touches those surfaces) |

## The three real gaps

### Gap 1 — Sail input state derivation

openvm-fv's `chip_bus_hypotheses` lemma
(`Equivalence/Mul.lean:492-537`) takes `h_constraints + h_is_valid +
h_bus_wellformedness` and derives

```
read_xreg (wrap_to_regidx rs1_ptr) state = ok (U32.toBV #v[b_0, b_1, b_2, b_3]) state
read_xreg (wrap_to_regidx rs2_ptr) state = ok (U32.toBV #v[c_0, c_1, c_2, c_3]) state
read_xreg (wrap_to_regidx rd_ptr) state = ok (U32.toBV #v[prev_data_0..3]) state
Sail.readReg Register.PC state = ok (BitVec.ofNat 32 pc) state
```

zisk-fv takes these as proof-signature parameters (`h_input_r1`,
`h_input_r2`, `h_input_pc`). Closing the gap is a shared
`chip_bus_hypotheses`-analogue lemma per shape family (ALU-RRW,
branch, jump, LD, SD). Each is ~150 lines of bus-effect unfolding +
transpile-contract application. Reuses the (unused-today) 58
transpile axioms.

### Gap 2 — `h_rd_match` derivation (Package C) — **STRUCTURALLY CLOSED (Phase 4.5)**

Phase 4.5 (sessions 2026-04-23 / 2026-04-24) decomposed the
monolithic `h_rd_match` into two smaller hypotheses for all 9
Arith-family `equiv_<OP>_metaplan` theorems (MUL, MULH, MULHU,
MULHSU, MULW, DIV, DIVU, REM, REMU), plus the LD MEM-family pilot:

- `h_rd_idx` — the rd-pointer equality (`input.rd = wrap_to_regidx
  e2.ptr` or the `.val`/`.toNat` equivalent for BitVec-typed rd).
- `h_rd_val` — the 8 byte lanes encode the pure-spec product /
  quotient / remainder / loaded-value.

Both are downstream-derivable via three Package-C bridges:

- **Bridge 1** (`Airs/Arith/Bridge1.lean`, commit `2b354e7`) —
  constraint-46 normalization collapses `bus_res1` to the high-chunk
  pack in each of the three Arith modes (MUL-primary, DIV-primary,
  REM-secondary).
- **Bridge 2** (`Spec/MulField.lean`, commit `5a68556`) — Main ↔ Arith
  operand composition at the bus; yields
  `main_a_packed * main_b_packed = main_c_packed + d_chunks_packed
  * 2^64` over FGL.
- **Bridge 3** (`Fundamentals/PackedBitVec.lean`, commit `6cddb9b`) —
  field → `BitVec 64` lift via `U64.toBV` (6 lemmas: BV-concat to
  Nat byte-sum, byte-coercion preservation, field-packed-vs-Nat
  cast, etc.).

Combined with `Airs/MemoryBus.lean`'s
`memory_entry_toField_eq_toBV_toNat` (commit `3076d00`),
downstream callers discharge `h_rd_val` from byte-range + no-wrap
hypotheses and the Arith packed-correct theorems.

Signed MUL/DIV carry-chain identity is closed too (Phase 4.5 Track
B, commit `6bc6250`): `arith_mul_signed_carry_identity` and
`arith_div_signed_carry_identity` in `Airs/Arith/CarryChain.lean`
hold over arbitrary sign witnesses; per-opcode specializations in
`Airs/Arith/{Mul,Div}.lean` consume the raw constraints.

**Not yet closed** (stays scope-honest): the `arith_table`
permutation lookup that ties the `(opcode, mode)` pair to the sign
witnesses `(na, nb, np, nr)` remains a parameter. Closing it
requires the permutation-argument infrastructure, orthogonal to the
polynomial identities.

### Gap 3 — Unwired transpile axioms

openvm-fv's `transpile_of_bus_wellformedness` lemma is **actually
consumed** in MUL/ADD/SUB/etc. proofs to discharge per-row
equalities that would otherwise be parameters.

zisk-fv's 58 `transpile_<OP>` axioms in `Fundamentals/Transpiler.lean`
are **declared but never invoked** anywhere in the Lean tree (verified
via grep 2026-04-24: zero non-docstring consumers). They are intended
to play the same role as openvm-fv's, but the wiring never landed.

Closing this is a **mechanical rewiring** — one `have := transpile_<OP>
...; obtain ⟨...⟩ := this.choose_spec` per opcode, consuming the
axiom's existential to discharge the bus-shape and rd-alignment
hypotheses that are currently parameters. Enables Gap 1 and part of
Gap 2.

## Not-gaps

- **Bus-wellformedness hypothesis content.** openvm-fv bundles under
  `wf_propertiesToAssumePerRow`; we decompose into per-shape hypothesis
  sets. Same semantic surface, different packaging. Both are scope-honest
  "the PIL emits rows of this shape on this opcode."
- **Platform axioms** (P1–P4). openvm-fv's RV32 IM scope doesn't
  exercise them; our RV64D scope does. The axioms are scope-honest
  claims about the platform ZisK runs on; retiring them would require
  a platform-config change, not a proof.
- **Sail spec trust** and **transpiler trust**. Both projects accept
  these as inputs to the verification.

## Summary

zisk-fv's proof structure is **weaker than openvm-fv on three axes**,
all of which are closure work (not fundamental rethinks):

1. **Gap 1 — Sail input derivation.** ~150 lines × 5 shape families =
   ~750 lines of `chip_bus_hypotheses`-analogue lemmas. **Phase 5 scope**
   (depends on Gap 3 closure).
2. **Gap 2 — `h_rd_match` derivation (Package C).** ~550 lines across
   three bridges. **Phase 4.5 scope** (Bridges 1+2 shipped session 1).
3. **Gap 3 — Unwired transpile axioms.** ~2500-4000-line axiom-level
   refactor: the 58 `transpile_<OP>` axioms have shape `∃ row :
   ZiskInstructionRow, …` with no connection to concrete `Valid_Main`
   rows. Making them load-bearing requires restating all 58 in
   `Valid_Main`-form and updating ~41 consumer theorems. **Phase 5 scope.**

All other comparison axes are either equal or reflect legitimate
scope differences.

## Plan references

- **Phase 4.5** (`ai_plans/zisk-fv-phase-4-5.md`): closes Gap 2 (9 Arith
  metaplan theorems drop `h_rd_match`) plus Phase 4 deferred completeness
  items (signed MUL/DIV, LD/SD bus shapes, 174 fixtures, verify-phase4
  target).
- **Phase 5** (`ai_plans/zisk-fv-phase-5.md`): closes Gaps 1 and 3 via the
  transpile-axiom refactor (Track H) and `chip_bus_hypotheses`-analogue
  lemmas (Track G). Completes structural parity with openvm-fv.
