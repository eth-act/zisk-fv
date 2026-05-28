# Discharge recipe — authoring `equiv_OP` wrappers

> **Status:** canonical. This document codifies the five-category
> discharge pattern crystallized by the DIV pilot (commits `75629e5`,
> `349c799`, `83532d7`; final form
> `ZiskFv/Compliance/Wrappers/Div.lean`). Every future
> `equiv_<OP>` wrapper authored on top of an existing
> canonical `equiv_<OP>` follows this template. Read this end-to-end
> before authoring a wrapper for a new opcode; the structure is not
> a tutorial, it is the contract.

## When to use this doc

You are writing this doc's prescribed code when **all** of the
following hold:

* The canonical `equiv_<OP>` theorem (`ZiskFv/Equivalence/<OP>.lean`)
  already typechecks, but carries *promise hypotheses* — caller-supplied
  parameters whose canonical names appear in the
  `match | bridge | byte_chain | loose` columns of
  `trust/baseline-caller-burden.txt` for the opcode.
* You want to expose a single wrapper that consumes only *trust-ledger*
  axioms + structural bus shape + Sail-side state predicates, and
  derives the promise hypotheses internally.
* The wrapper lives **outside** the canonical surface (under
  `ZiskFv/Compliance/Wrappers/<OP>.lean` or the future
  `Compliance.lean`), so the V1 anti-laundering metric on the
  canonical theorem is unaffected.

If you are modifying the canonical theorem itself, this is not your
document — read `docs/fv/known-gaps.md`'s 3.alpha per-shape target
trust footprint instead.

## Vocabulary refresher

This document uses the canonical project terminology defined in
`docs/fv/known-gaps.md#glossary-canonical-terminology`. The terms with
load-bearing meaning here are: **promise hypothesis**, **promise
discharge**, **discharge bridge**, **trust ledger**, **caller-burden
ledger**, **constructibility**. Read that glossary first if these
terms are not already second nature; off-cuff synonyms (e.g.
"dischargeable preconditions", "spurious assumptions") fragment the
audit trail.

## The 5 discharge categories

Every promise hypothesis on a canonical `equiv_<OP>` falls into one
of these five categories. The category determines which trust-ledger
class (`docs/fv/trusted-base.md`) you cite and which discharge
infrastructure you reuse.

### 1. Lane-match (byte ↔ chunk packing)

**Shape.** A hypothesis bridging a memory-bus entry's byte cells
(`e2.x0..x7`) to the provider AIR's chunk columns
(`v.a_0..a_3` for Arith, `v.free_in_c_0..c_7` for Binary, etc.).
Canonical names: `h_byte_lo`, `h_byte_hi`, `h_e1_e2_bytes` (retired
form), `h_match_clo`, `h_match_chi`.

**DIV pilot witnesses.**

* `h_byte_lo` discharged at `Wrappers/Div.lean:280-326`. Chain:
  `main_external_arith_emission_bundle` (`MemBridge.lean:553`, trust
  class #4(g)) delivers `e2.x0..x3.val pack = (m.c_0 r_main).val`; the
  op-bus `matches_entry` projection at `Wrappers/Div.lean:287-290`
  delivers `m.c_0 r_main = v.a_0 r_a + v.a_1 r_a * 65536`; an FGL→ℕ
  lift (`h_pair_lift` defined at `Wrappers/Div.lean:302-317`, consuming
  `arith_div_columns_in_range` from class #6b(a)) closes the chain.
* `h_byte_hi` discharged at `Wrappers/Div.lean:327-339`. Same bundle for
  the `e2.x4..x7 → m.c_1 r_main` side; `matches_entry` projects
  `m.c_1 r_main = v.bus_res1 r_a`; then
  `div_bus_res1_eq_a_hi` (`Airs/Arith/Bridge1.lean:79`) bridges
  `bus_res1 = v.a_2 + v.a_3 * 65536` under the DIV-primary mode pins,
  which require `arith_table_op_div_rem_main_selector_pin` (class
  #6b(j)) — see category 2 below.

**Generalization.** Every opcode with an rd-write needs lane-match
discharge. The bundle name varies by op-class (the trust ledger
exposes parallel bundles in `MemBridge.lean`: `main_load_emission_bundle`
4(d), `main_sext_load_emission_bundle` 4(e), `main_store_pc_emission_bundle`
4(f), `main_external_arith_emission_bundle` 4(g)). Match your opcode
to the bundle covering its op-set.

**Trust class.** Typically #4 (memory-bus emission bundle soundness),
plus an op-bus `matches_entry` projection that comes for free with
the `Valid_<Provider>` row (no axiom).

**Author discipline.** The trust gate enforces axiom-locality (a new
bundle goes in `MemBridge.lean`, listed in
`trust/allowed-axiom-files.txt`) but not category-correctness. If the
bundle's hypotheses do not pin the opcode's `is_external_op` / `op`
mode column, you have not discharged the lane match; you have
imported it under a different name.

### 2. Mode pins (opcode literal ↔ mode column)

**Shape.** A hypothesis like `v.sext r_a = 0`, `v.m32 r_a = 0`,
`v.div r_a = 1`, `m.main_div r_main = 1`, `m.main_mul r_main = 0`.
Pins one of the provider AIR's mode columns to a constant given the
row's opcode literal. Canonical names: `h_sext`, `h_m32`, `h_div`,
`h_main_div_one`, `h_main_mul_zero`.

**DIV pilot witnesses.**

* `h_sext`, `h_m32`, `h_div` discharged at `Wrappers/Div.lean:236-237`
  via `arith_table_op_div_rem_signed_mode_pin v r_a h_op_arith`
  (declared `Airs/Arith/Ranges.lean:386`, trust class #6b(h)).
* `h_main_div_one`, `h_main_mul_zero` discharged at
  `Wrappers/Div.lean:241-243` via
  `arith_table_op_div_rem_main_selector_pin v r_a h_op_arith` then
  `.1 h_op_arith_div` (declared `Airs/Arith/Ranges.lean:427`, trust
  class #6b(j)).

**Generalization.** Per-AIR, per-mode-column. Each provider AIR's
lookup-table axiom family covers its own mode columns. For Arith the
family lives in `Airs/Arith/Ranges.lean` (class #6b); analogous
classes exist for BinaryExtension's `op_is_shift` pin (class #6(c))
and Binary's `carry_bits_in_range` pin (class #6(d)).

**Trust class.** #6b (Arith table lookups) for Arith-family; #6
sub-classes per-AIR.

**Author discipline.** The opcode literal hypothesis
`h_op_arith : v.op r_a = 186 ∨ v.op r_a = 187` is itself derived
from the `matches_entry` op-slot equality plus the Main-side opcode
pin (`Wrappers/Div.lean:223-229`). Do not accept it as a parameter.

### 3. Sign-witness pins (signed and W-mode ops only)

**Shape.** A hypothesis like `np = MSB(packed4 c[])`,
`nb = MSB(packed4 b[])`, `nr = np ∨ d[] = 0`. Pins a sign-witness
column to the most-significant bit of an input/output chunk packing.
Canonical names: implicit (these typically appear as algebraic
consequences in `h_op1`, `h_op2`, `h_nr_pin`).

**DIV pilot witnesses.**

* `arith_div_np_eq_msb_of_dividend` (`Airs/Arith/Ranges.lean:502`,
  class #6b(k)) — pins `np` to the MSB of the dividend's packed4.
  Consumed at `Wrappers/Div.lean:464-465`.
* `arith_div_nb_eq_msb_of_divisor` (`Airs/Arith/Ranges.lean:530`,
  class #6b(l)) — pins `nb` to the MSB of the divisor's packed4.
  Consumed at `Wrappers/Div.lean:466-467`.
* `arith_table_op_div_rem_signed_d_sign_pin` (declared earlier;
  class #6b(d)) — pins `nr = np ∨ d[] = 0`. Consumed at
  `Wrappers/Div.lean:245-258` to produce `h_nr_pin` in the shape
  `equiv_DIV` expects (the disjunctive boundary form).

**Generalization.** Per-AIR, per-signed-or-W operation. Only the
signed (and W-mode) variants of MUL/DIV need MSB-pins; the unsigned
variants take a trivial witness (`np = 0`). The PIL arith_table
lookup enforces the relation via the legend at `arith.pil:222-229`
(`na = a3, nb = b3, np = c3, nr = d3`) on the signed-mode rows of
`arith_table_data.rs::ARITH_TABLE`.

**Trust class.** #6b (Arith table lookups).

**Author discipline.** The MSB-pins are *not* derivable from the
carry-chain; they are independent arith_table consequences. If you
catch yourself trying to derive `np = MSB(c)` from the carry
constraints, stop — that path does not exist on the prove side.

### 4. Range/bound (range-table or lookup-table derived bounds)

**Shape.** A hypothesis pinning a column or column-combination to a
range, magnitude bound, or arithmetic constraint enforced by an
AIR-internal lookup. Canonical names: `h_a0_lt..h_d3_lt` (chunk
ranges), `h_r_abs` (signed-remainder magnitude bound), `h_r_sign`
(signed-remainder sign agreement), `h_a_range` and friends.

**DIV pilot witnesses.**

* Chunk ranges `h_a0_lt..h_d3_lt` discharged at `Wrappers/Div.lean:298-301`
  via `arith_div_columns_in_range v r_a` (class #6b(a)). This is the
  "structural" range axiom that the canonical `equiv_DIV` already
  consumes transitively; the wrapper consumes it directly to lift
  FGL→ℕ in the lane-match composition.
* `h_r_abs`, `h_r_sign` discharged at `Wrappers/Div.lean:488-499` via
  `arith_div_remainder_bound v r_a h_sext h_m32 h_div h_op_arith`
  (class #6b(i)), composed with `h_op1` / `h_op2` (category 5) to
  rewrite into the `r2_val.toInt` / `r1_val.toInt` shapes that
  `equiv_DIV` consumes.

**Generalization.** Per-AIR, per-operation-class. Each provider AIR
exposes its own range / bound axioms in `Airs/<AIR>/Ranges.lean`.

**Trust class.** #6b (Arith range-table) for Arith; #6 sub-classes
per-AIR.

**Author discipline.** A bound axiom that asserts a magnitude or
algebraic-shape consequence (rather than a column range) must have
a PIL citation to the specific `assumes_operation` invocation that
enforces the bound (e.g. `arith.pil:274` for the Euclidean-remainder
bound consumed by `arith_div_remainder_bound`).

### 5. Operand bridges (Sail `read_xreg` → chunk lane equation)

**Shape.** A hypothesis bridging Sail's register-read output (e.g.
`div_input.r1_val.toInt`) to the provider AIR's chunk packing (e.g.
`packed4 c[0..3] - np * 2^64`). Canonical names: `h_op1`, `h_op2`,
`h_input_r1_circuit`, `h_input_r2_circuit`, `h_input_r1_extract`.

**DIV pilot witnesses.**

* `h_op1` discharged at `Wrappers/Div.lean:469-475` via
  `signed_packed_toInt_eq_of_read_xreg`
  (`Equivalence/Bridge/SailStateBridge.lean:190`). Inputs: the Sail
  `read_xreg` predicate `h_input_r1`, the unsigned `r1_val.toNat =
  packed4` identity (formerly derived from the DIV transpile contract +
  op-bus `matches_entry` lane projections + chunk-range bounds; see
  `Wrappers/Div.lean:347-435`), the chunk-range bundle, and the
  `np = MSB` pin from category 3.
* `h_op2` discharged symmetrically at `Wrappers/Div.lean:476-482`.
* The unsigned companion `packed_lane_eq_of_read_xreg`
  (`SailStateBridge.lean:90`) is used at `Wrappers/Div.lean:356-358`
  and `:362-364` to deliver the `r{1,2}_val = BitVec.ofNat 64 …`
  step that feeds into the signed form.

**Generalization.** **Cross-shape and largely DONE.** The generic
infrastructure in `ZiskFv/Equivalence/Bridge/SailStateBridge.lean`
covers every shape that reads a register and packs the result into
chunks. Two helpers:

* `packed_lane_eq_of_read_xreg` — unsigned form. Use when the
  provider AIR consumes `r_val.toNat`.
* `signed_packed_toInt_eq_of_read_xreg` — signed form, two's-complement.
  Use when the provider AIR consumes `r_val.toInt` and exposes a
  sign-witness column.

**Trust class.** None (pure-Lean bridges, no axioms). The trust
inputs they consume are the Sail `read_xreg` predicate (a SPEC-PRE
caller obligation), the `transpile_<OP>` row contract (class #1),
the op-bus `matches_entry` projection (free from `Valid_<Provider>`),
and category 3's sign-witness pins.

**Author discipline.** Do *not* add a new bridge in
`SailStateBridge.lean` for an opcode that fits an existing helper.
If your opcode's operand shape genuinely differs (e.g. ITYPE with an
immediate, RTYPE with a third register), add a new helper there
rather than per-opcode in the wrapper file.

## The wrapper template

This section walks through `equiv_DIV`'s signature and
proof outline so a future author has a template to clone.

### Signature shape

The wrapper's parameter block has seven sections in this order
(`Wrappers/Div.lean:154-213`):

1. **Sail-side inputs.** `state`, the input record (`div_input`),
   `r1 r2 rd : regidx`. Pass-through from the canonical theorem.
2. **Structural bus rows.** `exec_row`, `e0 e1 e2`. Pass-through.
3. **AIR validators + row indices.** `(m : Valid_Main C FGL FGL)
   (r_main : ℕ)`, `(v : Valid_<Provider>) (r_a : ℕ)`. In
   `Compliance.lean` `(m, v)` will be shared across all opcodes; per-opcode
   work supplies the row indices.
4. **Activation / opcode pins on Main.** `h_main_active`,
   `h_main_op_<OP>`. These pin Main's `is_external_op` and `op`
   columns on the chosen row.
5. **Op-bus permutation handshake.** `h_match_primary : matches_entry
   (opBus_row_Main m r_main) (opBus_row_<Provider> v r_a)`. In
   `Compliance.lean` this is delivered by the relevant
   `op_bus_perm_sound_<Provider>` axiom; the wrapper accepts it
   explicitly to keep the shape simple.
6. **Structural bus / exec shape.** `h_exec_len`, the multiplicity /
   `as` pins on each entry, `h_nextPC_matches`, `h_rd_idx`.
   Pass-through.
7. **Sail-side state predicates (SPEC-PRE).** `h_input_r1`,
   `h_input_r2`, `h_input_rd`, `h_input_pc`, plus opcode-specific
   preconditions like `h_op2_ne`, `h_no_overflow`. These remain
   caller obligations — they live in Sail's state, not in the
   circuit.
8. **Universal-per-row constructibility.** Per-row constraints from
   the provider AIR (`h_row_constraints`, plus booleanity /
   sign-XOR closures). In `Compliance.lean` these collapse into a
   single `∀ r, <provider>_row_well_formed v r` parameter.

### Proof outline

The proof body composes the five categories in a strict order
(`Wrappers/Div.lean:218-509`):

1. **Derive the opcode literal on the provider AIR's `op` column.**
   Project from `h_match_primary` (op-bus `matches_entry`) + the
   Main-side `h_main_op_<OP>` pin. `Wrappers/Div.lean:222-229`.
2. **Unpack the row-constraint bundle.** `Wrappers/Div.lean:230-234`.
3. **Discharge category 2 (mode pins).** `Wrappers/Div.lean:236-243`.
4. **Discharge any opcode-specific lookup-consequence pins** (e.g.
   `h_nr_pin` for DIV's signed-remainder closure).
   `Wrappers/Div.lean:244-258`.
5. **Discharge category 1 (lane-match)** using the emission bundle +
   op-bus projection + FGL→ℕ lift. `Wrappers/Div.lean:259-339`.
6. **Discharge category 5 (operand bridges)** by first deriving the
   unsigned packed4 identities (transpile + op-bus + chunk-range
   composition), then composing with category 3's MSB pins via
   `signed_packed_toInt_eq_of_read_xreg`. `Wrappers/Div.lean:340-482`.
7. **Discharge category 4 (range/bound)** rewriting via category 5's
   results. `Wrappers/Div.lean:483-499`.
8. **Delegate to the canonical theorem.** Pass every derived
   hypothesis through. `Wrappers/Div.lean:500-509`.

Step ordering matters: category 5's signed bridges consume
category 3's MSB pins, and category 4's `arith_div_remainder_bound`
rewrites via category 5's `h_op1` / `h_op2`. The dependency graph
forces 2 → 3 → 5 → 4; categories 1 and 2 are mutually independent
(both consume only `h_match_primary` + the Main pins).

## Pilot-then-mass-author workflow

### Why pilots come first

Every shape (BinaryExtension, Arith Mul / Div, Binary, Mem, ControlFlow,
RTYPEW, etc.) has its own emission-bundle, mode-pin, and
sign-witness axioms. A pilot for the shape proves that the bundle
of trust-ledger axioms is *sufficient* to discharge every category
for at least one opcode. Without that proof of sufficiency, fanning
out to multiple opcodes in the shape risks discovering, mid-batch,
that the bundle is missing a pin — at which point every in-flight
wrapper must be revisited.

The DIV pilot took three commits (`75629e5`, `349c799`, `83532d7`)
to land. Three commits is *the cheap path*: it added 5 new axioms
across two trust classes (#4 and #6b), each pinning a single
consequence that the discharge required. Each pilot commit cited
the PIL line, audited the class fit, and ran the trust gate.

### What "pilot done" looks like

A pilot for shape `<S>` is complete when:

1. `equiv_<OP>` for one canonical opcode in shape `<S>`
   typechecks (`lake build` green).
2. Every promise hypothesis on the wrapper's `equiv_<OP>` delegation
   call is discharged from a trust-ledger axiom — no `sorry`, no
   `admit`, no caller-supplied promise hypothesis at the wrapper
   level.
3. The new axioms (if any) all fit existing trust classes from
   `docs/fv/trusted-base.md`. Each new axiom has a PIL citation in
   its docstring and a row entry in the trust-class table.
4. Both V1 and V2 trust gates pass (`trust/scripts/check-all.sh` and
   `trust/scripts/check-all-semantic.sh`).
5. The pilot's caller burden — the parameter binder count and shape
   — is strictly smaller than the canonical `equiv_<OP>`'s. The
   promise hypotheses are gone; what remains is the structural
   bus shape, the Sail-side state predicates, and constructibility
   obligations (row-constraint bundles, validator instances).

### Mass-authoring within a shape

Once a pilot is done, the per-opcode wrappers in the same shape
follow the pilot's structure mechanically. The work is:

* Match the new opcode to its `transpile_<OP>` row contract.
* Find the appropriate emission bundle (`MemBridge.lean`).
* Find the appropriate mode-pin axiom family (`Airs/<AIR>/Ranges.lean`).
* If the opcode is signed/W and the pilot is unsigned/non-W (or vice
  versa), add the matching MSB / W-pin axiom — the trust class
  already exists; only the specific consequence needs a new entry.
* Copy the pilot's proof structure and adjust the projection
  indices on `matches_entry` (different `opBus_row_<Provider>`
  shapes pack the column slots in different orders).

If the new opcode needs a *new* trust class — not just a new
consequence in an existing class — STOP. Adding a new class is a
separate CODEOWNER-reviewed PR; the wrapper PR cannot land until
that PR is in.

## Anti-laundering checks specific to wrapper authoring

The trust gate's V1/V2 checks enforce the canonical-theorem
anti-laundering metric. The wrapper file lives outside that surface
(under `Compliance/`), so the metric does not directly apply.
Two wrapper-specific checks substitute:

1. **Caller-burden must shrink.** Count the wrapper's parameter
   binders and compare to the canonical `equiv_<OP>`'s. If the
   wrapper has more binders than the canonical theorem, you did
   not discharge; you laundered. The DIV pilot's signature has
   35 binders / 22 hypotheses vs.  `equiv_DIV`'s 43/32
   (`Wrappers/Div.lean:144-145`); the 8-binder drop *is* the discharge.
2. **New axioms must fit existing classes with PIL citations.** Any
   new axiom in the wrapper's discharge path must (a) live in a
   file listed in `trust/allowed-axiom-files.txt`, (b) match an
   existing trust class in `docs/fv/trusted-base.md`, and (c) have
   a docstring with PIL line + Rust source citations. The DIV
   pilot's three new axioms — `arith_table_op_div_rem_signed_mode_pin`
   (class #6b(h)), `arith_div_remainder_bound` (class #6b(i)),
   `arith_table_op_div_rem_main_selector_pin` (class #6b(j)),
   `arith_div_np_eq_msb_of_dividend` (class #6b(k)),
   `arith_div_nb_eq_msb_of_divisor` (class #6b(l)) — all sit in
   the same class as the pre-existing
   `arith_table_op_div_rem_signed_d_sign_pin` (class #6b(d)) with
   PIL citations to `arith.pil:286-287` + `arith_table_data.rs`.
3. **Bridges should be cross-shape if possible.** Category 5
   (operand bridges) is generic; resist the temptation to add a
   DIV-specific helper to the wrapper file. The generic
   `signed_packed_toInt_eq_of_read_xreg` covers every signed
   register-read operand; a new bridge belongs in
   `SailStateBridge.lean`, not in `Compliance/Wrappers/<OP>.lean`.

## Cross-shape generic infrastructure (already built — DON'T re-author)

Before authoring a new helper in the wrapper file, check whether
existing infrastructure covers your need.

* **`Equivalence/Bridge/SailStateBridge.lean`** — Sail `read_xreg`
  → packed-lane equations.
  * `packed_lane_eq_of_read_xreg` (line 90) — unsigned form.
  * `signed_packed_toInt_eq_of_read_xreg` (line 190) — signed form
    consuming a sign-witness MSB pin.
* **`Equivalence/Bridge/Arith.lean`** — chain-witness helpers,
  packed-correctness re-exports (`mul_{un,}signed_packed`,
  `div_{un,}signed_packed`). Per-mode discharges already exist;
  consume them rather than re-deriving the carry-chain projection.
* **`Airs/MemoryBus/MemBridge.lean`** — the emission-bundle axioms
  family. One bundle per op-class (load / sext-load / store-pc /
  external-arith); pick the one covering your opcode.
* **`Airs/OperationBus/Bridge.lean`** — the op-bus permutation
  soundness axioms. Six axioms covering the six provider AIRs;
  delivered to the wrapper as the `h_match_primary` parameter.

## Per-AIR vs. cross-shape distinction

A new axiom or bridge sits in one of two places:

* **Per-AIR axiom** — lives in `Airs/<AIR>/Ranges.lean` (or
  `Airs/<AIR>/<Sub>Bridge.lean`). Pins a consequence on `<AIR>`'s
  columns. The arith_table mode pin family (#6b(d)/(h)/(j)/(k)/(l))
  is the canonical example: each axiom pins a different mode/sign
  column on the *same* arith_table lookup. Use this category when
  your axiom's conclusion mentions only one provider AIR's columns
  and the PIL citation is to that AIR's `.pil` file.
* **Cross-shape bridge** — lives in
  `Equivalence/Bridge/SailStateBridge.lean` (or a sibling
  cross-shape bridge file). A *pure-Lean* lemma chaining the trust
  ledger to a Sail-side consequence. No axioms. The category 5
  operand bridges are the canonical example: their inputs are
  trust-ledger consequences (`transpile_<OP>` + chunk-range +
  MSB-pin), their output is a `r_val.toInt` equation Sail consumes,
  and the proof is a calculation. Use this category when your
  helper's inputs and outputs span multiple AIRs or bridge to Sail.

The placement decision determines audit surface: per-AIR axioms
are CODEOWNER-reviewed via the `trust/baseline-axioms.txt` hash
diff; cross-shape bridges are reviewed via the normal Lean PR
review of the bridge file's diff.

## Sibling reference: `docs/fv/per-air-axiom-map.md`

A sibling document — `docs/fv/per-air-axiom-map.md` — is being
authored in parallel as the per-AIR catalog of which mode-pin /
range / sign-witness axioms exist for each provider AIR, with their
shape-applicability and the wrapper opcodes that consume them. When
that doc exists, the per-AIR sections of this recipe (categories 2,
3, 4) should cite it for the canonical axiom-to-opcode mapping;
this recipe will continue to be the structural template.

Until that doc lands, the canonical sources for the per-AIR axiom
catalog are `Airs/<AIR>/Ranges.lean` (declarations) and
`docs/fv/trusted-base.md`'s class table (one-line descriptions +
PIL citations).
