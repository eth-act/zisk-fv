# Known gaps in the per-opcode equivalence theorems

> **Status:** open. This document flags a class of user-supplied
> hypotheses in canonical `equiv_<OP>` theorems that are not derived
> from circuit witnesses or trusted bus axioms, and that constitute
> the practical residual gap between "the theorems typecheck" and
> "ZisK is verified against Sail end-to-end." Removing these
> hypotheses (or deriving them from existing trusted infrastructure)
> is the **immediate TODO** before a global compliance theorem can
> close.

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
