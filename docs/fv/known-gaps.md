# Known gaps in the per-opcode equivalence theorems

> **Status (2026-05-13 update):** the gap framing in this document
> remains accurate as a *historical survey* of what the audit
> surfaced, but the path forward has crystallized since this doc was
> first written. The discharge is now a layered piece of work
> tracked by Step 4 of
> `/home/cody/.claude/plans/plan-to-completely-resolve-wild-lynx.md`:
> per-opcode `equiv_<OP>_from_trust` wrappers (Layer 1) discharge
> the promise hypotheses from the trust ledger; the
> `Compliance.lean` dispatcher (Layer 2) dispatches the global
> theorem through those wrappers. The DIV wrapper at commit
> `83532d7` is the first canonical exemplar; see
> `docs/fv/discharge-recipe.md` (the 5-category template) and
> `docs/fv/per-air-axiom-map.md` (per-AIR axiom inventory +
> per-shape gap predictions) for the practical authoring guide. The
> original "Immediate TODO" list below is partially superseded —
> items 1, 2, 3 are done; items 4 (trust gate V3) and the explicit
> per-shape derivation strategies are now Step 4.1 and Step 5 in
> the plan.

## Glossary (canonical terminology)

Plans, PRs, commit messages, and agent prompts touching this work
**must** use the terms below as defined here. Off-cuff synonyms
("dischargeable preconditions", "spurious assumptions", "moving
hypotheses around") fragment the audit trail; the canonical terms
keep the discussion checkable against this document.

| Term                    | Definition |
|-------------------------|------------|
| **promise hypothesis**  | A caller-supplied parameter on a canonical `equiv_<OP>` theorem that asserts an algebraic or structural relationship the theorem could derive from the trust ledger but currently does not. The proof body substitutes the hypothesis without deriving it. Example: `h_match_clo : m.c_0 r_main = v.free_in_c_0 r_binary + … + v.free_in_c_7 r_binary`. The full audit is in this document; the cross-AIR matching family, the Sail-input bridge family, the per-byte range/chain family, the BinaryExtension specifics family, and the Tier-1 loose-element-algebra family are all promise hypotheses. |
| **promise discharge**   | The work of replacing a promise hypothesis with a derivation from the trust ledger (transpile axioms, bus permutation axioms, lookup-soundness axioms, range-check axioms, AIR-validity structures). The result: the theorem still typechecks, but the hypothesis is no longer caller-supplied — it is internally derived from axioms already on the books. **Real promise discharge reduces the trust surface; renaming or splitting a hypothesis without deriving it is laundering, not discharge** (see CLAUDE.md "Anti-laundering principle"). |
| **discharge bridge**    | A Lean file under `ZiskFv/Equivalence/Bridge/<Shape>.lean` that exposes a uniform discharge API for one provider-AIR shape. Consumes the trust-ledger axioms relevant to that shape; produces the per-byte / per-chunk / cross-AIR equations the per-opcode `equiv_<OP>` theorems for that shape need. Step 2 of `/home/cody/.claude/plans/plan-to-completely-resolve-wild-lynx.md`. |
| **trust ledger**        | The 87 axioms in `trust/baseline-axioms.txt`, organized by class in `docs/fv/trusted-base.md`. The project's named, audited trust surface. **Promise discharge does not extend the trust ledger** (modulo small bus-protocol additions like Phase A's OpBus axioms, which fit existing classes). |
| **caller-burden ledger** | `trust/baseline-caller-burden.txt`, the corresponding ledger of every parameter binder on every canonical `equiv_<OP>`. Promise discharge **shrinks** this ledger. The diff IS the audit surface for whether a refactor accomplished real discharge or just laundering (see CLAUDE.md V1 check #8). |
| **anti-laundering metric** | The pair of gates `check-hypothesis-count.sh` (V1 #7) and `check-caller-burden.sh` (V1 #8). Operational meaning of "real promise discharge": every plan PR must reduce or hold both columns of `trust/baseline-hypothesis-count.txt` and show net REMOVALS (not renamings) in `trust/baseline-caller-burden.txt`. |
| **constructibility (separate gap)** | Whether a `Valid_<AIR>` instance can actually be constructed from a real ZisK trace. If `Valid_<AIR>`'s declared constraints are stronger than the actual circuit, the equivalence theorems are vacuous. Not addressed by promise discharge; tracked as a separate concern in CLAUDE.md "Anti-laundering principle" item 4. |

## TL;DR

62 of 63 canonical `equiv_<OP>` theorems carry **promise hypotheses**
— user-supplied parameters that assert algebraic relationships
between Main's columns, Provider AIR columns, loose field elements,
and Sail input/output values, **without those relationships being
derived from the actual ZisK bus protocol or transpilation
contract**. The proofs build because they substitute the hypotheses
into the conclusion; they are *vacuously fine in isolation*. The
hypotheses are unfulfillable from the actual circuit without
substantial new derivation infrastructure.

The trust gate's existing `OUTPUT-EQ` retirement
(`trust/forbidden-param-shapes.txt`) caught the most extreme form of
this pattern (hypotheses that *literally state the conclusion*) and
explicitly retired ten such names: `h_rd_val`, `h_byte_sum`,
`h_bus_execute_matches_sail`, `h_entry_hi_nat`, `h_pc_fgl_lo_nat`,
`h_pci_lo_val`, `h_entry_lo_eq`, `h_high_bytes_signext`,
`h_high_bytes_zeroext`, `h_e1_e2_bytes`. The replacement form is
more granular but **structurally the same gap**: instead of one fat
"the answer = the spec answer" hypothesis, the user now supplies a
constellation of `h_match_clo` + `h_input_r1_circuit` + per-byte
ranges + table-chain hypotheses that **together** still let consistent
witnesses be supplied without those witnesses being tied to the
actual bus emission.

## Concrete examples

### Tier 3 — Provider AIR present, c-lane match assumed (24 opcodes)

Theorems take `Valid_Main` + `Valid_<Provider>` + a row index
`r_binary`, plus `h_match_clo` / `h_match_chi` as user-supplied
algebraic equations:

```lean
-- ZiskFv/Equivalence/Sll.lean (representative)
(h_match_clo : m.c_0 r_main
    = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
      + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
      + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
      + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
```

The proof body substitutes this and never derives it from any bus
axiom.

Affected: `Add` *(only one in this list)*, `Addi`, `And`, `Andi`,
`Or`, `Ori`, `Xor`, `Xori`, `Sll`, `Slli`, `Sra`, `Srai`, `Srl`,
`Srli`, `Shift`, `ShiftLI`, `ShiftR`, `ShiftRA`, `ShiftRAI`,
`ShiftRLI`, `Lb`, `Lh`, `Lw`, `LoadD`, `LoadBU`, `LoadHU`, `LoadWU`.

### Tier 2 — No Provider AIR, loose elements + Main (12 opcodes)

Theorems take `Valid_Main` only — **no `Valid_<Provider>`
parameter**. The provider's columns are loose field elements bound
in the theorem with no AIR backing:

```lean
-- ZiskFv/Equivalence/Slt.lean (representative)
(a0 a1 a2 a3 a4 a5 a6 a7
 b0 b1 b2 b3 b4 b5 b6 b7
 c0 c1 c2 c3 c4 c5 c6 c7
 cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
 fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
 pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
(h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain
   ZiskFv.Airs.BinaryTable.OP_LT a0 b0 c0 cin0 fl0 pi0)
…
(h_match_clo : m.c_0 r_main = fl7)
(h_input_r1_circuit : slt_input.r1_val
  = BitVec.ofNat 64
      (a0.val + a1.val * 256 + a2.val * 65536 + …))
```

The user supplies ~50 loose field elements plus `consumer_byte_match_chain`
hypotheses asserting they satisfy the BinaryTable relation. Then
`h_match_clo` ties Main's `c_0` to one of the loose elements (e.g.
`fl7`). **Nothing links these elements to any Binary AIR row.**

Affected: `Slt`, `Slti`, `Sltu`, `Sltiu`, `Sub`, `Subw`, `Addiw`,
`Addw`, `Auipc`, `Jal`, `Jalr`, `Lui`.

### Tier 1 — No Valid_<AIR> at all (24 opcodes)

Theorems take **no `Valid_<AIR>` parameters**, neither Main nor any
provider:

```lean
-- ZiskFv/Equivalence/Mul.lean (representative)
(a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
(cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
…
(hC31 : a₀ * b₀ = c₀ + cy₀ * 65536)
(hC32 : a₁ * b₀ + a₀ * b₁ + cy₀ = c₁ + cy₁ * 65536)
…
(hC38 : cy₆ = d₃)
(h_byte_lo : e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536
    + e2.x3.val * 16777216 = c₀.val + c₁.val * 65536)
(h_byte_hi : …)
(h_op1 : mul_input.r1_val.toNat
  = ZiskFv.PackedBitVec.MulNoWrap.packed4 a₀.val a₁.val a₂.val a₃.val)
(h_op2 : …)
```

The 4×4 multiplication carry chain itself (`hC31..hC38`) is a
user-supplied equation. The opcode-specific arithmetic identity is
the hypothesis, not the conclusion. A user could fabricate any field
elements satisfying long-multiplication's algebraic identity AND
match them to `e2`'s bytes AND pack them to equal Sail's input
values, and the theorem would close. The actual ZisK Mul circuit
could be doing anything.

Affected: all 6 branches (`Beq`, `Bne`, `Blt`, `Bge`, `Bltu`,
`Bgeu`); all 5 muls (`Mul`, `MulH`, `MulHU`, `MulHSU`, `MulW`); all
8 div/rem variants (`Div`, `Divu`, `Divuw`, `Divw`, `Rem`, `Remu`,
`Remuw`, `Remw`); all 4 stores (`StoreB`, `StoreD`, `StoreH`,
`StoreW`); `Fence`.

### Summary

| Tier | # opcodes | Provider AIR linkage | What's promised by the user |
|------|-----------:|----------------------|-----------------------------|
| 3 | 24 | `Valid_Main` + `Valid_<Provider>` | `m.c_0`/`c_1` equals a specific column-sum on provider |
| 2 | 12 | `Valid_Main` only | `m.c_0`/`c_1` equals a loose field element + table-chain assertions |
| 1 | 24 | none | the entire opcode-arithmetic identity, supplied as loose-element equations |
| (clear) | 1 | bundled `add_circuit_holds`; `matches_entry` derived in proof body | `Add` only |

Cross-checked against `trust/baseline-equiv-axiom-deps.txt` (V2): the
per-theorem axiom closures for many `equiv_<OP>` show that
**`transpile_<OP>` axioms named in docstrings are not actually in
the proof's transitive dependencies.** The transpile axioms are in
the trust ledger but not all are formally consumed.

## Why the existing gates don't catch this

* `check-no-output-eq.sh` (V1) and `check-no-output-eq-v2.sh` (V2)
  catch the 10 retired OUTPUT-EQ-class names + their type
  signatures. The current promise pattern uses different names
  (`h_match_clo`, `h_match_chi`, `h_input_r1_circuit`,
  `h_input_r2_circuit`, `h_byte_*`, `hC*`) and types that are
  legitimately needed in *some* form, so a name- or type-blocklist
  cannot mechanically distinguish unfulfillable-from-circuit shapes
  from legitimate bridging hypotheses.
* `check-axiom-deps.sh` (V2) records the per-theorem axiom closure
  but cannot detect missing axioms — only changes to existing
  closures. A theorem that *should* depend on `transpile_MUL` and
  `op_bus_perm_sound_ArithMul` but instead consumes user-supplied
  hypotheses bypassing both will pass the V2 check trivially.

The gap is fundamentally semantic: detecting it requires checking
whether each hypothesis is structurally derivable from the
trust-ledger axioms + the AIR validators. No current automated
gate does that.

## Why this matters

`lake build` succeeding on `equiv_<OP>` is the project's
formal-verification claim. Per `CLAUDE.md`:

> `lake build` succeeding **is** the formal-verification claim;
> everything else is auxiliary scaffolding.

But what the proofs prove is:

> *if* the user can supply consistent witnesses for the promise
> hypotheses, *then* `equiv_<OP>` holds.

For the per-opcode theorems to constitute an end-to-end claim about
ZisK, every promise hypothesis must be discharged from circuit
witnesses + the trusted bus / transpile axioms. Today, **62 of 63
opcodes have no such discharge** — only `Add` (after a recent
refactor that bundled `matches_entry` into `add_circuit_holds` and
derived it from a new `op_bus_perm_sound_BinaryAdd` axiom)
demonstrates the chain end-to-end.

## Immediate TODO

1. **Treat this as the project's principal open soundness gap.**
   Replace the existing CLAUDE.md status framing ("all 63 RV64IM
   opcodes proved") with one that distinguishes typecheck-success
   from end-to-end discharge. (Done in this PR.)

2. **Decide on the per-shape derivation strategy** for each tier:

   * **Tier 3** needs the OpBus permutation axiom (Phase A of
     `docs/fv/plans/op-bus-and-global-compliance.md` lays the
     groundwork) plus per-byte ↔ packed reconciliation lemmas where
     the bus emits packed sums and the proof consumes per-byte
     forms (e.g. `BinaryExtension`).
   * **Tier 2** needs the OpBus axiom + introduction of
     `Valid_<Provider>` parameters + derivation of the loose
     elements from provider columns + transpile-axiom invocation.
   * **Tier 1** needs all of the above plus introduction of
     `Valid_Main` and the relevant provider AIRs from scratch.

3. **Investigate the `BinaryExtension` layout-convention conflict**
   surfaced by Phase A: the extractor's row-major flattening
   (`Buses.lean::bus_emission_BinaryExtension_0`) disagrees with
   the named-accessor's column-major interpretation
   (`ZiskFv/Airs/Binary/BinaryExtension.lean:40-45` and
   `BinaryExtensionPackedCorrect.lean:91-123`). Resolution requires
   inspecting the PIL2 compiler's symbol-table flattening order.
   Until resolved, deriving `h_match_clo` for SLL/SRL/SRA from the
   bus is blocked.

4. **Strengthen the trust gate** with a check that flags promise
   hypotheses by *shape* — e.g. canonical-theorem parameters of
   the form `m.<col> r_main = <expr involving v.<col> r_binary>`
   that aren't structurally an instance of an existing trust-ledger
   axiom's conclusion. This is V3-class enforcement; the design
   discussion needs to start.

## Discharge-able vs structural caller burden (snapshot 2026-05-12)

`trust/baseline-caller-burden.txt` records every parameter binder
on every canonical `equiv_<OP>` theorem along with a category tag
(`validator | state | entry | range | match | bridge | bus_shape |
transpile | byte_chain | loose | row | instance | other`).

The aggregate breakdown post the Step 1.7b + Step 0b + Step 2c-f
+ Step 2b SLT-family completion work is:

| Category | Count | Discharge-able? | Notes |
|---|---:|---|---|
| `range` | 695 | **YES** | Derive from `*_columns_in_range` axioms (Main / Binary / BinaryAdd / BinaryExtension / Arith). |
| `other` | 611 | no | Structural Sail/state plumbing (`h_input_rd`, `h_rd_idx`, output equation shapes). |
| `bus_shape` | 516 | no | Bus-protocol shape commitments (`h_exec_len`, `multiplicity` pins, `as` pins). Caller-side. |
| `loose` | 440 | **YES** | Loose FGL quantifiers — promote to `Valid_<AIR>` columns at the existential row. |
| `state` | 217 | no | Sail `PreSail.SequentialState` parameters. |
| `transpile` | 171 | no | Per-opcode `transpile_<OP>` axioms threaded as the trust article itself. |
| `byte_chain` | 115 | **YES** | `consumer_byte_match` — derived via `binary_per_byte_lookup_witness` + `bin_table_consumer_wf`. |
| `match` | 98 | **YES** | `h_match_clo`/`chi` — derived via `matches_entry` (Op-Bus perm soundness) + carry_7=0 for AND/OR/XOR rows. |
| `validator` | 86 | no | `Valid_<AIR>` instance parameters. |
| `row` | 69 | **YES** | `r_binary` / `r_arith` / `r_e` — make existential via bridges. |
| `entry` | 67 | no | `MemoryBusEntry` parameters. |
| `bridge` | 59 | **YES** | Input bridges (`h_input_r{1,2}_circuit`, `h_input_r1_extract`) — derive via `SailStateBridge` + transpile axioms + matches_entry. |
| **Total** | **3144** | | of which **~1,476** discharge-able, **~1,668** structural. |

### Why this matters

A naive "aggregate hypothesis binders: 2,078" framing overstates
the remaining work by ~2×. The structural categories
(`state`/`entry`/`validator`/`bus_shape`/`transpile`/`other`) will
not shrink: they're how a caller plumbs the per-opcode theorem
into a concrete context. The discharge surface is the ~1,476
binders in the `range`/`loose`/`byte_chain`/`match`/`row`/`bridge`
classes.

### Per-opcode discharge yield (observed)

From the Step 1.7b / 2b refactors already landed in this branch:

| Refactor shape | Opcodes done | Per-opcode savings |
|---|---|---|
| BinaryAdd (ADD, ADDI) | 2 | 10–12 binders |
| Binary loose-promote (SUB/SUBW/ADDW/ADDIW/SLT/SLTI/SLTU/SLTIU) | 8 | 27–30 binders |
| Binary byte-range only (AND/ANDI/OR/ORI/XOR/XORI) | 6 | ~24 binders |

### Projected Step 3 yield

For the remaining 49 opcodes:

| Shape | # opcodes | Expected per-opcode | Projected total |
|---|---:|---|---|
| BinaryExtension (unblocked by Step 0b cascade) | 15 | 15–25 | 225–375 |
| Arith Mul | 5 | 30–40 | 150–200 |
| Arith Div | 8 | 30–40 | 240–320 |
| Mem loads/stores | 8 | 15–20 | 120–160 |
| ControlFlow | 11 | 5–15 | 55–165 |
| FENCE / etc. | 2 | small | ~10 |
| **Total** | **49** | | **800–1,230 binders** |

That shrinks the discharge-able surface from ~1,476 to ~250–675.
The residual ~250–675 are structurally hard:

* Full 6-field byte-chain witnesses (`consumer_byte_match_chain`
  with `cin`/`flags`/`pos_ind`) for the SUB/SLT-family Tier-2 chain
  ops — `binary_per_byte_lookup_witness` covers 3-field
  `consumer_byte_match` for AND/OR/XOR but not the chain version.
* Per-opcode carry-chain wiring for Arith (hC31..hC38) — CarryChain
  re-exports are in `Bridge.Arith` but the per-equiv projection is
  real work.
* `h_input_imm_*` on ITYPE / U-type / shift-immediate opcodes — the
  immediate value is caller-routed via `transpile_<OP>`'s
  `imm_b_lo`/`imm_b_hi` parameters; no Sail-side axiom links
  `imm_b_lo` to the Sail spec's `<op>_input.imm`, so these stay
  caller-supplied unless we add a separate axiom.

### Bottom line

The remaining work is **bounded** — not "3000 hypotheses to
discharge one by one." It is ~49 opcode refactors averaging ~20
binders each (Step 3), plus ~500–1k LOC for the global compliance
theorem (Step 4) and trust-gate V3 + transparency artifacts (Steps
5–6). All previously-blocking infrastructure (Steps 0–2) is now
in place.

## Step 3.alpha — pre-fan-out artifacts (parallelization unblockers)

Step 3 (per-opcode *promise discharge* refactors across ~47
opcodes in 5 shapes) cannot safely parallelize until three
unblockers land: per-shape *target trust footprint*, per-shape
canonical exemplars, and baseline-contention / worktree mechanics.
This section is the canonical record of all three.

### 3.alpha.1 — per-shape target trust footprint

What each Step 2 bridge **discharges** vs. **accepts as caller-burden**,
and the trust-ledger decision frozen for each shape before Step 3
fans out. Reviewers and agents should consult this row before
authoring a refactor in the shape — divergence from the row is a
laundering risk and should be challenged.

| Shape | Bridge file | Discharges (caller burden REMOVED) | Accepts (caller burden RETAINED) | Decision for fan-out |
|--|--|--|--|--|
| **BinaryAdd** | `Bridge/BinaryAdd.lean` | `r_binary` existential, `matches_entry`, chunk-range hypotheses | (none material) | **Done** — ADD/ADDI already refactored. Not in remaining fan-out. |
| **Binary** | `Bridge/Binary.lean` | `r_binary` existential, `matches_entry`, 24 byte ranges (a/b/c × 0..7) | 8 per-byte `consumer_byte_match` hypotheses, `h_match_clo`/`chi` (carry_7 form), per-byte `h_input_r{1,2}` bridges | **Done conservatively** — 14 Binary-shape opcodes already refactored against the conservative bridge. Deeper discharge (the 6-field `consumer_byte_match_chain` with `cin`/`flags`/`pos_ind` for SUB/SLT-shape chain projection) is deferred to a Step-3-followup PR; **not blocking** fan-out because the 14 Binary opcodes are already done. |
| **Arith** | `Bridge/Arith.lean` | `r_a` existential, `matches_entry` (mul / div primary / div secondary), 16 chunk ranges (a/b/c/d × 0..3), packed-correctness re-exports (`mul_{un,}signed_packed`, `div_{un,}signed_packed`) | `hC31..hC38` carry-chain hypotheses per opcode | **Accept duplication** — packed-correctness re-exports are one-liners; each MUL/DIV equiv consumes the matching re-export directly. Carry-chain orientation differs by signed/unsigned axis so per-opcode wiring is cleaner than bridge lifting. No further bridge work needed before fan-out. |
| **BinaryExtension** | `Bridge/BinaryExtension.lean` | `r_e` existential, `matches_entry`, 9 byte ranges (`free_in_a_0..7` + `free_in_b`) | per-byte `consumer_byte_match` for BinaryExtension table, shift-amount + signed/unsigned mode pins (projected from `matches_entry` at the equiv) | **Smoke-test via SLL exemplar in 3.alpha.2.** Bridge is layout-agnostic (delivers `matches_entry` opaquely); the Step 0b cascade fix only matters at the *projection* step inside each equiv. If SLL exemplar typechecks against the post-cascade column convention, the bridge is good for the 15 BinaryExtension opcodes. |
| **Mem** | `Bridge/Mem.lean` | `load_discharge` (lane match + ∃ r_mem with `wr=0`), `store_discharge` (lane match + ∃ r_mem with `wr=1`) | per-opcode address packing + value packing (consumed at equiv-site against Sail spec) | **As-is sufficient.** LBU/LHU/LWU high-byte-zero is already exposed via `MemoryBus.MemAlignBridge.memalign_subdoubleword_load_high_bytes_zero` (imported by `Bridge/Mem.lean`). LB/LH/LW sign-extension chains through `Circuit/SextLoadBridge.lean` directly at the equiv — this is a circuit module, not a bridge concern; no double-batching conflict. Bridge does not need extension before fan-out. |
| **ControlFlow** | `Bridge/ControlFlow.lean` | `branch_input_bridges_of_read_xreg` (r1 + r2 packed lanes for all 6 branches via shared helper); JALR r1 packed lane via direct use of Step 1.7b `SailStateBridge` | `h_input_imm_*` (linking Main's `imm_b_lo`/`imm_b_hi` columns to Sail spec's `<op>_input.imm` field) for AUIPC / LUI / JAL / JALR + the 6 branches' imm projection | **Accept imm caller-burden** in this fan-out pass. Adding a `transpile_imm_lo_hi` axiom would close it cleanly but triggers a new trust class + CODEOWNER review. Documented as a Step-3-followup; not blocking fan-out. |

**Rule of thumb for parallel agents.** If a refactor wants to
discharge a hypothesis the row above marks as "RETAINED" for the
shape, that's out of scope for this fan-out pass — the
hypothesis stays. If a refactor doesn't discharge a hypothesis
the row marks as "REMOVED", it's incomplete — fix before merge.

### 3.alpha.2 — canonical per-shape exemplars

Each remaining shape gets one canonical refactored equiv on this
branch, *before fan-out*, so each parallel agent has a template.
Status / commit reference per exemplar:

| Shape | Canonical exemplar | Status | Commit |
|--|--|--|--|
| BinaryExtension | SLL | **landed** — 17 binders dropped (`h_a_range` + 16 c-byte 32-bit ranges) via `binary_extension_columns_in_range`; smoke-tests Step 0b cascade | `3687a2d` |
| ControlFlow (branch) | BEQ | **N/A** — `equiv_BEQ` already at minimum form (state inputs + bus shape only, no Provider-AIR cross-AIR promise hypotheses). All 6 branches confirmed at 19-20 binders / 12 hypotheses. No exemplar needed. | (existing) |
| Arith Mul | MUL | **landed** — Tier-2 → Tier-3 promotion: added `(v : Valid_ArithMul, r_a : ℕ)` parameters, replaced 16 loose FGL chunks `a₀..d₃` with `v.a_0 r_a` etc., dropped 16 chunk-range hypotheses via `arith_mul_chunk_ranges_at_holds`. Net reduction: 16 binders, no laundering. | (this commit) |
| Arith Div | DIVU | **landed** — mirror of MUL: added `Valid_ArithDiv` + `r_a`, dropped 16 chunk-range hypotheses via `arith_div_chunk_ranges_at_holds`. Net reduction: 16 binders. | (this commit) |
| Mem load | LD | **landed** — added new trust-ledger axiom `memory_bus_entry_byte_range_perm_sound` (per-byte range soundness for memory-bus entries; same trust class as `memory_bus_register_write_perm_sound`). Dropped `h_e1_range` + `h_e2_range` bundled byte-range hypotheses. Net reduction: 2 bundled binders. | (this commit) |
| Mem store | SD | **N/A** — `equiv_SD` does not carry byte-range hypotheses; already at minimum form for the new axiom's scope. | (existing) |
| ControlFlow (non-branch) | AUIPC + JAL | **landed** — consumed `memory_bus_entry_byte_range_perm_sound` to discharge `h_e_rd_0..7` (8 byte-range hypotheses per opcode). Net reduction: 8 binders each. | (this commit) |

#### 3.alpha.2 exit-criterion analysis

The original 3.alpha exit gate required "five exemplars committed and
tagged" before any Step 3 fan-out. The honest accounting after this
analysis is:

* **One shape unblocked for fan-out: BinaryExtension** (SLL exemplar
  landed; smoke-tested Step 0b cascade). 15 opcodes (SLL/SLLI/SRL/SRLI/
  SRA/SRAI/Shift/ShiftLI/ShiftR/ShiftRA/ShiftRAI/ShiftRLI/Lb/Lh/Lw)
  ready for parallel agent batches following the SLL template.
* **One shape needs no exemplar: ControlFlow branches** (BEQ already
  minimal; the 5 other branches BNE/BLT/BLTU/BGE/BGEU follow the same
  shape and likely already in similar minimal form — confirm before
  fan-out).
* **Three shapes have hard prerequisites that fall outside 3.alpha**:
  Arith Mul (Tier-2 → Tier-3 promotion), Arith Div (same), Mem (new
  memory-bus byte-range axiom), ControlFlow non-branch (same memory
  axiom).

These prerequisites are now visible work. They should land as their
own PRs *before* the corresponding shapes' fan-out, not as part of
the fan-out itself. This means the 3.alpha unblocker for fan-out
applies on a **per-shape basis**: BinaryExtension is unblocked now;
the others unblock as their prerequisite PRs land.

Recommended sequencing now:

1. **Immediate**: Step 3 BinaryExtension fan-out (parallel agents on
   the 15 BinaryExtension-shape opcodes using SLL template).
2. **Confirm branches**: read BNE/BLT/BLTU/BGE/BGEU; if they all
   match the BEQ minimal form, mark ControlFlow-branch shape as
   already-fan-out-complete (no agents needed).
3. **Arith prerequisite PR**: design + author the Tier-2 → Tier-3
   promotion infrastructure (Valid_<AIR> column shape audit + 2 new
   carry-related axioms + ledger entries). Then MUL exemplar lands
   on this branch; then Arith Mul fan-out (5 opcodes); then Arith
   Div fan-out (8 opcodes).
4. **Mem prerequisite PR**: design + author `memory_bus_byte_range_perm_sound`
   axiom + trusted-base.md ledger entry + CODEOWNER review. Then
   LD / SD exemplars; then Mem fan-out (8 opcodes); then AUIPC / JAL
   refactors (parallel with Mem since same blocker).

Each exemplar MUST:
1. Pass `lake build` and V1 + V2 trust gates.
2. Show a **net REDUCTION** in `trust/baseline-caller-burden.txt`
   for its opcode (lines removed > lines added).
3. Show a **non-increase** in
   `trust/baseline-hypothesis-count.txt`'s per-opcode `total=` and
   `hypothesis=`.

The exemplar's diff IS the template for the rest of the shape's
opcodes. Agents authoring follow-on opcodes in a shape are
expected to read the exemplar's diff first.

### 3.alpha.3 — parallelization appendix

#### Baseline-contention strategy

Step 3 sub-PRs all regenerate four shared files:
* `trust/baseline-equiv-axiom-deps.txt`
* `trust/baseline-caller-burden.txt`
* `trust/baseline-hypothesis-count.txt`
* `trust/baseline-axioms.txt` (only if shape adds an axiom)

**Chosen: Option A — serialize regenerate as last commit of each PR.**

Mechanics:
1. Each parallel agent works in its own worktree on its shape's opcodes.
2. Body work (per-opcode refactors, exemplar consumption) is parallel
   across worktrees.
3. The baseline-regen step (`trust/scripts/regenerate.sh` +
   `regenerate-caller-burden.py`) is the **last commit** of each PR.
4. PRs land sequentially in merge order; later PRs rebase on
   whatever landed before, then re-run the regen step as a final
   commit to refresh the baselines against the post-rebase state.

Rationale: cheap to set up; merge friction is bounded to one rebase
per PR. If friction is bad after the first 2-3 shapes land,
switch to Option B (per-AIR baseline split) before Arith batch.

#### Worktree mechanics checklist (per agent)

Before launching an agent for a shape's parallel batch:

1. **Create worktree from current branch tip** (NOT via `isolation:"worktree"`,
   which creates from `origin/main` → stale base). Example:
   ```bash
   git worktree add ../zisk-fv-step3-<SHAPE> <current-branch>
   ```
2. **Symlink `.lake/packages`** to the canonical copy to avoid
   ~10 GiB per worktree:
   ```bash
   cd ../zisk-fv-step3-<SHAPE>/.lake
   rm -rf packages
   ln -s /home/cody/zisk-fv/.lake/packages packages
   ```
3. **Run `lake exe cache get`** immediately — DO NOT skip
   (mathlib cache; ~30 min penalty if skipped). The post-update
   hook side-effect is not reliable.
4. Verify `lake build` succeeds before delegating.

#### Agent prompt template (per parallel batch)

When launching a shape's parallel batch, the agent prompt MUST
include all of the following:

```
Read these files first, in this order:
1. /home/cody/zisk-fv/CLAUDE.md (project context + anti-laundering principle)
2. /home/cody/zisk-fv/docs/fv/known-gaps.md (glossary + Step 3.alpha per-shape target trust footprint)
3. /home/cody/zisk-fv/ZiskFv/Equivalence/<EXEMPLAR>.lean (the canonical template for shape <SHAPE>)
4. /home/cody/zisk-fv/ZiskFv/Equivalence/Bridge/<SHAPE>.lean (the discharge bridge you will consume)

Your task: refactor <LIST OF OPCODE FILES> following the <EXEMPLAR>
template. For each opcode:
* Drop the hypotheses the shape's footprint row marks as REMOVED.
* Retain (do NOT discharge) the hypotheses marked RETAINED — those
  are out of scope for this fan-out pass.
* Internally consume Bridge/<SHAPE>.lean's discharge API exactly
  as <EXEMPLAR> does.

Constraints (NON-NEGOTIABLE):
* Anti-laundering metric must shrink: per-opcode `total=` /
  `hypothesis=` in trust/baseline-hypothesis-count.txt may not grow,
  and caller-burden diff for the opcode must have more removed lines
  than added.
* No new axioms. If you find one is needed, STOP and report — that
  requires a separate trust-ledger PR.
* No new top-level `def`s without marking @[reducible].
* Use the canonical vocabulary (promise hypothesis / promise discharge
  / discharge bridge / trust ledger / caller-burden ledger / anti-
  laundering metric / constructibility) — no ad-hoc synonyms.

Last commit of your PR must be the regenerate-baselines step:
  trust/scripts/regenerate.sh
  python3 trust/scripts/regenerate-caller-burden.py > trust/baseline-caller-burden.txt
Then run trust/scripts/check-all.sh and confirm green before pushing.
```

The bracketed `<…>` slots are the only per-batch customization.
Anything else added to the prompt is at the launcher's discretion;
nothing in the template above may be omitted.

## References

* `trust/forbidden-param-shapes.txt` — the 10 OUTPUT-EQ-class names
  that *were* retired during the "finishing" series (commits
  `aef18ac` etc.).
* `trust/baseline-equiv-axiom-deps.txt` — the V2 per-theorem axiom
  closures. Cross-reference against this to see which `equiv_<OP>`
  closures are surprisingly thin.
* `docs/fv/plans/op-bus-and-global-compliance.md` — the plan whose
  Phase A introduces the OpBus permutation axioms and whose Phase
  B/C would close the discharge chain end-to-end.
* `docs/fv/trusted-base.md` — the human-readable trust ledger; pairs
  with `baseline-axioms.txt`.

## History

The pattern has existed since the project's first commit
(`ad55fcb`, "Phase 1: vertical-slice ADD proof + extractor +
harness", 2026-04-20) and was partially recognized during the
"finishing" series in late April 2026, which retired the 10
OUTPUT-EQ-class names but left the more granular promise-hypothesis
pattern in place. Phase B.1 of
`docs/fv/plans/op-bus-and-global-compliance.md` is the first work
that closes the gap for a specific opcode (`Add`).
