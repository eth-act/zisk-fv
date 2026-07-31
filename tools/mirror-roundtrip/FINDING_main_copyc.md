# Finding: Main `constraint_4` / `constraint_10` are mirrored by a *weakened* copy

Issue eth-act/zisk-fv#304. The mirror-roundtrip gate flags Main's b-side source-C
copy as "copied but weakened": generated `constraint_4_every_row` /
`constraint_10_every_row` (`main/pil/main.pil:386`) are restated by
`sourceCCopyBetween` (`ZiskFv/AirsClean/Main/Circuit.lean:721`), but only in a
form that drops the constraint on the segment-boundary row.

This document records the exact polynomial diff, the `b_src_c` determination, the
soundness trace, and a recommendation. It changes no `ZiskFv/`, `trust/`, `nix/`,
or mirror file. Claims are tagged **PROVED** (canonical algebra + source citation),
**TRACED** (dependency path read out of the current tree), or **HYPOTHESIS**.

---

## 1. Exact polynomial diff — **PROVED**

### The generated constraint (b-side, index 0), `build/extraction/Extraction/Main.lean:85`

Provenance comment: `main/pil/main.pil:386 (b_src_c)*(b[0]-(previous_c))`.
Resolving every `Extraction.Circuit.main c (id := 1) (column := N)` against the
pilout symbol table (`PilOut.symbols`, via `tools/mirror-roundtrip/lanes.py` /
`tools/pilout-roundtrip/pilout_atoms.witness_column_names`):

| lane in emitted Lean | pilout symbol |
| --- | --- |
| `main(1,2)` | `Main.b[0]` |
| `main(1,3)` | `Main.b[1]` |
| `main(1,4)` (rotation −1) | `Main.c[0]` at previous row (`'c[0]`) |
| `main(1,5)` (rotation −1) | `Main.c[1]` at previous row (`'c[1]`) |
| `main(1,13)` | `Main.b_src_imm` |
| `main(1,14)` | `Main.b_src_mem` |
| `main(1,17)` | `Main.b_src_ind` |
| `main(1,36)` | `Main.b_src_reg` |
| `preprocessed(0)` (`pre(0)`) | fixed column `Main.SEGMENT_L1` |
| `exposed(3)` | air value `Main.segment_previous_c[0]` |
| `exposed(4)` | air value `Main.segment_previous_c[1]` |

So the emitted `constraint_4_every_row` is, with
`B := 1 − b_src_mem − b_src_imm − b_src_ind − b_src_reg`, `L := SEGMENT_L1`,
`x := b[0]`, `p := 'c[0]`, `s := segment_previous_c[0]`:

```
B · ( x − previous_c ) = 0,   where   previous_c = L·(s − p) + p
```

This is a literal transcription of `main.pil:377` (`const expr previous_c =
SEGMENT_L1 * (segment_previous_c[index] - 'c[index]) + 'c[index];`) and
`main.pil:386`. It holds on **every row**; there is no `(1 − L)` factor.

### The mirror, `ZiskFv/AirsClean/Main/Circuit.lean:721`

```
sourceCCopyBetween#0 :
  (1 − curr.core.segment_l1)
    · (1 − b_src_mem − b_src_imm − b_src_ind − b_src_reg)
    · (curr.core.b_0 − prev.core.c_0) = 0
= (1 − L) · B · (x − p)
```

### The relationship

```
generated        = B·(x − p) − B·L·(s − p)
mirror           = (1 − L)·B·(x − p)
(1 − L)·generated = mirror − (L − L²)·B·(s − p)
```

Therefore **`mirror = (1 − L)·generated` exactly iff `L² = L`** (i.e. `SEGMENT_L1`
boolean). Over the free lane variables the raw canonical symmetric difference is
non-zero — the check reports **10 monomials**, which is precisely the term
`(L − L²)·B·(s − p)` (the `pre(0)`-and-`exposed(3)` monomials: `s·L`, `s·L·b_src_*`
on the generated side; `x·L`, `x·L·b_src_*` on the mirror side). The tool's own
cofactor search collapses this to the single line:

```
IMPLIED BY generated #4: this clause is (1 - pre(0)) * that constraint
... WEAKER than the generated constraint, not stronger.
```

The fixed column is `col fixed SEGMENT_L1 = [1,0...]` (`main.pil:19`): boolean, and
`= 1` only on row 0. So under the actual fixed-column values `mirror =
(1 − segment_l1)·generated` holds exactly, and **nothing else** distinguishes the
two sides — there is no second discrepancy. The `(L − L²)` residue is an artifact
of the tool holding fixed-column *values* out of scope, not a real algebraic gap.

**Semantics.** On `segment_l1 = 0` rows (`previous_c` collapses to `p = 'c[0]`):
mirror and generated are the *same* polynomial, `B·(x − p) = 0`. On the boundary
row `segment_l1 = 1` (`previous_c` collapses to `s = segment_previous_c[0]`):
generated is `B·(x − s) = 0` — b must equal the previous segment's carried-in c —
while the mirror is `0 = 0`, vacuous. **The mirror drops the constraint exactly on
the segment-boundary row, and only there.**

---

## 2. Is `b_src_c = 1 − b_src_mem − b_src_imm − b_src_ind − b_src_reg`? — **PROVED, yes**

- **PIL source.** `b_src_c` is a `const expr` (`main.pil:338`) defined identically
  in both configuration branches:
  - `main.pil:350` (`stack_enabled`): `b_src_c = 1 - b_src_mem - b_src_imm - b_src_ind - b_src_reg;`
  - `main.pil:355` (else): `b_src_c = 1 - b_src_mem - b_src_imm - b_src_ind - b_src_reg;`

  (Contrast `a_src_c`, which *does* differ between branches — `... - a_src_sp` vs
  `... - a_src_reg` at `main.pil:349`/`:354`. `b_src_c` does not, so there is no
  configuration ambiguity on the b-side.)
- **Pilout symbol table.** The four selectors the generated constraint subtracts
  (`main(1,14)`, `main(1,13)`, `main(1,17)`, `main(1,36)`) resolve to
  `b_src_mem`, `b_src_imm`, `b_src_ind`, `b_src_reg` — the same four the mirror
  names.
- **Canonicaliser corroboration.** The two sides share **30 of 40** monomials; the
  entire `b_src_c` expansion is common to both. The only monomials that differ are
  the `segment_previous_c` / `SEGMENT_L1` boundary terms of §1.

**Conclusion:** the mirror's `b_src_c` factor is *identical* to the generated one.
The sole discrepancy is the missing `(1 − segment_l1)` factor (equivalently, the
dropped `segment_previous_c` public-input term). There is no second finding here.

---

## 3. Does the weakening cost soundness? — **TRACED: no, and it does not reach the root theorem as a hole**

### 3a. Direction: `sourceCCopyBetween` is a *hypothesis*, not a discharged guarantee

`sourceCCopyBetween` enters through the Main component's `transition` field:

```
componentWithRomMemAndOpBus (def :948) { transition := pcHandshakeTransition }   -- Circuit.lean:954
pcHandshakeTransition idx prev curr := transitionBetween (eval prev) (eval curr)  -- Circuit.lean:942
transitionBetween prev curr := pcHandshakeBetween prev curr ∧ sourceCCopyBetween prev curr  -- Circuit.lean:734
```

In the Clean framework a component's `transition : Input F → Input F → Prop` is an
*additive adjacent-row constraint* the AIR imposes
(`.lake/.../Clean/Air/FlatComponent.lean:16-18`), collected over the table by
`Table.TransitionConstraints` (`FlatComponent.lean:177`). It is part of the
**acceptance** predicate: `AcceptedZiskTrace` carries
`transitions_hold : witness.TransitionConstraints`
(`ZiskFv/Compliance/AcceptedZiskTrace.lean:126`), and `root_soundness`
(`ZiskFv/Soundness.lean:54`) takes an `AcceptedZiskTrace` as its hypothesis
(`Soundness.lean:48` calls this the "PC-handshake certificate").

So `sourceCCopyBetween` is something an accepted trace **satisfies and the proof may
assume** — not something the component must prove to a caller. **Weakening a
hypothesis is the soundness-safe direction**: `accepted → valid_sail` proved from
*fewer* facts is a stronger, still-sound result. Unsoundness would require the
mirror to assert *more* than the circuit (an over-strong validator); it asserts
strictly less.

Moreover the weaker assumption is genuinely *justified* by the real AIR: given
`L ∈ {0,1}`, `constraint_4 ⇒ sourceCCopyBetween#0` on every row (on `L=0` they are
equal; on `L=1` the mirror is vacuous). No unsound assumption is smuggled in — the
mirror is a sound consequence of the emitted constraint, just a lossy one.

### 3b. Where it is consumed: only on `segment_l1 = 0`, where mirror = generated

The generated `Extraction/Main.lean` file is imported by **no** `ZiskFv/` module, so
the only route the C-copy reaches any proof is the mirror. Every soundness consumer
of the Main transition demands the non-boundary case explicitly:

- **b-side C-copy.** The sole consumer is `source_c_copy_lanes_of_between`
  (`ZiskFv/Compliance/TraceLevelExport/StepStrongControlStore.lean:383`), which takes
  `h_segment : current.core.segment_l1 = 0` and only then extracts
  `b_0 = prev.c_0 ∧ b_1 = prev.c_1` from `h_transition.2`. Its one call site is the
  **JALR unaligned-operand** case (`.../Dispatcher.lean:1649`), where `h_segment` is
  supplied by `mainTable_fixed.segment_l1_succ` — the within-segment *successor*
  row. (JALR is why only the b-side got a mirror at all: its rs1 operand is sourced
  from the prior instruction's c within a spin sequence.)
- **PC handshake.** `AcceptedZiskTrace.mainTransition_to_next_pc`
  (`ZiskFv/Compliance/MainTransition.lean:98`) likewise requires
  `segment_l1 (i+1) = 0`. (The PC handshake, unlike the C-copy, *is* genuinely
  `(1 − SEGMENT_L1)`-gated in the PIL at `main.pil:410`, so `pcHandshakeBetween` is a
  faithful restatement, not a weakening.)

On `segment_l1 = 0` rows the mirror is **byte-for-byte the same polynomial** as the
generated constraint (§1). So the soundness proof reads the transition only in the
region where mirror = generated; it never touches the weakened `segment_l1 = 1`
half. The weakening is therefore invisible to — and unused by — the current proof.

### 3c. The boundary row is the boot / cross-segment seam, and the docstring rationale is real

In the single-segment model `segment_l1 = 1` occurs only at row 0
(`mainFixedValues`, `Circuit.lean:752-757`; `SEGMENT_L1 = [1,0,...]`,
`main.pil:19`). There the generated constraint forces `b[0] = segment_previous_c[0]`
— the *previous segment's* final c, threaded as the public air value
`segment_previous_c` (`airval segment_previous_c[RC]`, `main.pil:75`; `exposed(3/4)`
in the emitted Lean). This is the cross-segment continuation datum, and it is
already declared out of scope:

- `ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean:20-21`: "a segment
  does not contain its own starting state, it is carried in from boot".
- `ZiskFv/AirsClean/RegisterBoundary.lean:28-30`: "The cross-segment continuation
  terms (the `MAIN_CONTINUATION_ID` block and `main.pil:454`'s
  `sel:(1-main_last_segment)` continuation pull) are out of scope (#103/#76)."

The docstring's stated reason for the weakening — "Clean's transition interface has
no public-input surface" — is **real, not an excuse**: `Component.transition`
(`FlatComponent.lean:16-18`) is `Input F → Input F → Prop`, two row inputs with no
environment and no air-value/public accessor. `segment_previous_c` is an `airval`;
the two-row `transition` *physically cannot reference it*. Stating the
within-segment form gated by `SEGMENT_L1` is the faithful restatement of everything
the interface can express.

**HYPOTHESIS (not mechanically verified):** that no *other* path makes the current
theorem depend on the boundary datum. This rests on (i) the emitted constraint being
imported nowhere in `ZiskFv/`, and (ii) an exhaustive read of the references to
`sourceCCopyBetween` / `source_c_copy_lanes_of_between` (all are the JALR
`segment_l1 = 0` case above, or completeness-side witness constructions in
`ZiskFv/Compliance/*SpinWitness*`, which are not soundness). It is a read of the
current tree, not a proof of non-dependence.

---

## 4. Recommendation — **(b): a real, already-tracked #103/#76 cross-segment scope item**

Among the task's options:

- **Not (c)** — this is not an untracked unproven obligation, and not unsound. The
  weakening is soundness-safe (weaker hypothesis, genuinely implied by the circuit),
  and the proof provably (§3b) never reads the dropped half.
- **It is (b)** — the dropped content (boundary-row `b = segment_previous_c`) is the
  cross-segment continuation seam already declared #103/#76 scope
  (`RegisterBoundary.lean:30`), the same seam that leaves the Main
  `#0/#19/#20/#21/#38` boundary cluster unmodeled.

**Nuance that keeps it out of the raw-gap bucket.** Unlike `#0/#19/#20/#21/#38`
(modeled *nowhere*, in any form), `#4/#10` **are** faithfully modeled for the
in-scope `segment_l1 = 0` region; only the out-of-scope `segment_l1 = 1` boundary
term is dropped, and dropped for a genuine interface reason. This is *correctly
scoped*, not *missing*. The honest label is: "in-scope (within-segment) region
backed exactly; boundary term is #103/#76 cross-segment scope, unstatable in the
current `transition` interface", not an unqualified gap.

**Contrast the a-side (`#3/#9`, `a_src_c`, `main.pil:385`)**, a *separate* finding
outside this task: it has **no** mirror at all — not even the within-segment form —
because no opcode proof currently consumes the a-side C-copy (only JALR's b-side is
used). That too is soundness-safe (unused), but it is not even scoped, and it should
be surfaced independently.

**Concrete recommendation to the owner:**

1. **Declare**, not fix. Record Main `#4/#10`'s boundary term (`segment_l1 = 1`) as
   #103/#76 cross-segment scope, cited to `main.pil:75` (`segment_previous_c`
   airval), `main.pil:377/386` (`previous_c`), `main.pil:454`
   (`MAIN_CONTINUATION_ID`), and `RegisterBoundary.lean:30`. Add it next to the
   `#0/#19/#20/#21/#38` cluster in whatever the tool/handover uses to declare scope,
   with the note that it differs from that cluster by being backed in-scope.
2. **Teach the tool** to treat "cofactor `= (1 − SEGMENT_L1)` × generated, boolean
   fixed column, remainder declared #103/#76" as *in-scope coverage plus a declared
   boundary delegation*, rather than a bare `GAP` + `STRENGTHENING` pair — analogous
   to how it already handles the out-of-root Mem delegations. The cofactor search
   already computes exactly the fact needed; only the classification/label is
   missing.
3. **No proof change** is required for the current single-segment `root_soundness`.
   Closing the boundary term is part of the #103/#76 cross-segment work, and would
   *first* require giving the Clean `transition` interface a public-input / airval
   surface (or an equivalent accessor) so the boundary equation
   `b = segment_previous_c` can be stated at all. That is an interface change, not a
   local mirror edit, and should not be attempted to make the gate green.

---

## Appendix: reproduction

```bash
# generated polynomial + provenance
sed -n '85,86p;117,118p' build/extraction/Extraction/Main.lean

# mirror
sed -n '712,733p' ZiskFv/AirsClean/Main/Circuit.lean

# PIL source (needs the zisk submodule checked out)
sed -n '19p;75p;338p;349,355p;377p;384,386p' zisk/state-machines/main/pil/main.pil

# canonical diff + cofactor conclusion
python3 tools/mirror-roundtrip/check_mirrors.py --air Main 2>&1 \
  | grep -nA14 'GAP  Main #4\|STRENGTHENING\|IMPLIED BY'

# lane resolution (column -> pilout symbol)
python3 - <<'PY'
import sys; sys.path[:0]=['tools/mirror-roundtrip','tools/pilout-roundtrip']
import lanes, pilout_atoms, pilout_wire
po = pilout_wire.load('build/zisk.pilout'); ref = lanes._find_air(po,'Main')
n = pilout_atoms.witness_column_names(po, ref)
for c in (2,3,4,5,13,14,17,36): print(c, n[(1,c)])
print('exposed(3) =', lanes.exposed_report(po,'Main').names[('air_value',3)])
PY
```
