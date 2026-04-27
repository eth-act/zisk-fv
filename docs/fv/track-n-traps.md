# Track N — `h_rd_val` retirement: traps and idioms

Library-reference notes harvested during Phase 1 keystone implementation
(`feature/track-n-h-rd-val`). These are durable facts about the Lean
proof environment that future agents extending the BitVec-lift family
(K1-B, K1-C, K3, K4, and the Phase 2 derivation lemmas) need to know.

## K1-A findings (BinaryAddPackedCorrect, commit `f92a1ca`)

### 1. FGL-packed `.val` is **not** the raw Nat sum

The natural packing `a_packed := a_0 + a_1 · 2^32 : FGL` can exceed
`GL_prime = 2^64 - 2^32 + 1`: the maximum value is `2^64 - 1`, and
`2^64 - 1 > GL_prime`, so `a_packed.val ≠ a_0.val + a_1.val · 2^32`
in general. The `mod GL_prime` introduced by `ZMod` is *not* a no-op
even under per-chunk range bounds.

**Implication for the BitVec lift.** Statements of the form

```lean
BitVec.ofNat 64 (a_packed v row).val
  = BitVec.ofNat 64 (a_0.val + a_1.val · 2^32)
```

do **not** hold — they fail at the `(2^64 - 2^32, 2^64)` window where
`mod GL_prime` wraps but `mod 2^64` does not.

**Mitigation: state theorems in chunk-`.val` form.** Phrase
conclusions as

```lean
BitVec.ofNat 64 ((v.a_0 row).val + (v.a_1 row).val * 4294967296)
```

where each chunk's `.val` is taken individually and combined at the
ℕ level. The Goldilocks-no-wrap bound is then automatic from the
per-chunk range bounds (`a_0.val < 2^32 ∧ a_1.val < 2^32 ⟹
a_0.val + a_1.val · 2^32 < 2^64 < 2 · GL_prime`).

This is a **breaking deviation from the plan's signature.** The plan
wrote `BitVec.ofNat 64 (a_packed v row)` as if `a_packed : FGL` could
be lifted directly. In practice, downstream Phase 2 derivation lemmas
must consume the chunk-level form.

### 2. `simp only [BitVec.toNat_add]` causes kernel deep-recursion

```
simp only [BitVec.toNat_add]
-- (kernel) deep recursion detected
```

Same for `simp only [BitVec.toNat_ofNat]` on goals that mention
`BitVec.ofNat 64 n` for several distinct `n`. Lean's kernel ends up
trying to compute `2^64` recursively to verify the simp rewrite.

**Mitigation: use `rw` instead of `simp only` for these lemmas.**

```lean
rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
```

`rw` produces a lighter proof term — the kernel can verify it without
expanding `2^64` numerically.

### 3. Carry-chain ℕ lift idiom

To lift a field equation `x = y : FGL` to `x.val = y.val : ℕ` under
range bounds:

```lean
have h_rhs_cast : <rhs FGL expr>
    = (((<rhs Nat expr> : ℕ) : FGL)) := by push_cast; ring  -- not rfl!
have h_lhs_cast : <lhs FGL expr>
    = (((<lhs Nat expr> : ℕ) : FGL)) := by push_cast; ring
rw [h_lhs_cast, h_rhs_cast] at h_fgl
have heq := congr_arg Fin.val h_fgl
simp only [Fin.val_natCast] at heq
omega   -- closes via range bounds + boolean cases
```

**`push_cast; ring`, not `push_cast; rfl`** — the latter triggers a
definitional-equality check that recurses into `2^64` computation.

### 4. Final BitVec close: strip mods then `Nat.add_mul_mod_self_right`

After `BitVec.eq_of_toNat_eq` and the `rw` chain through `BitVec.toNat_add`
+ `BitVec.toNat_ofNat`, the goal is

```
(a_nat + b_nat) % 2^64 = c_nat
```

where the carry chain says `a_nat + b_nat = c_nat + k₁ · 2^64`.
Rewrite the LHS into the form `c_nat + k₁ · (2^64)` (via plain `ring`
with the chain hypotheses), then close with

```lean
rw [Nat.add_mul_mod_self_right]   -- (x + k · m) % m = x % m
exact Nat.mod_eq_of_lt h_c_bound
```

## Project-wide invariants reminded by K1-A

- **Factored form `4294967296 * 4294967296`** is required wherever
  `2^64` appears in carry-chain coefficients. `ring` and
  `linear_combination` treat `4294967296 * 4294967296` and
  `18446744073709551616` as different polynomial atoms even though
  they're numerically equal. (Documented in CLAUDE.md trap #2.)

- **Never re-quantify `[Field FGL]`** at the lemma level — declare it
  once globally in `Fundamentals/Goldilocks.lean`. (CLAUDE.md trap #1.)

## `store_pc = 1` opcode rd-write: the hi-half infrastructure gap

This section captures findings from Wave B.6 retry (Track N) for the
N-Jump-UTYPE archetype's JAL/JALR/AUIPC opcodes. Tier-1 retirement of
the OUTPUT-EQ parameters on `h_rd_val_jut_jal/jalr/auipc` in
`Equivalence/RdValDerivation/JumpUType.lean` is **not feasible with
the infrastructure currently in tree**. Future agents should not
attempt the upgrade until the gaps below are filled.

### Architectural setting

ZisK multiplexes opcode semantics through a single Main AIR row. The
`store_value[0]` PIL expression (`main.pil:311`) is

```
  store_value[0] = store_pc * (pc + jmp_offset2 - c_0) + c_0
```

For `store_pc = 0` opcodes (ADD, ADDI, LUI, MUL, ...) this collapses
to `c_0`, so the rd-write low half flows through the existing `c_0`
column. The `register_write_lanes_match` predicate
(`Airs/MemoryBus.lean:140-144`) — which ties memory-bus entry
`memory_entry_lo/hi` to Main's `c_0`/`c_1` — therefore lifts the
byte-bus rd-write back to Main columns directly.

For `store_pc = 1` opcodes (JAL, JALR, AUIPC) the formula evaluates
to `pc + jmp_offset2`. There is no Main column that exposes either
the lo or hi 32-bit half of `pc + jmp_offset2` separately — Main only
carries `pc : ℕ → FGL` as a single field element. The byte-level
decomposition that the memory-bus entry needs lives only inside the
PIL permutation argument tying the bus entry's 8 byte lanes to the
`store_value` formula's two 32-bit halves.

### Lo-half: partial Spec coverage

The current Spec layer provides:

* `Spec/Jal.jal_store_value` —
  `store_pc * (pc + jmp_offset2 - c_0) + c_0 = pc + jmp_offset2 : FGL`.
* `Spec/Jalr.jalr_store_value` — same shape.
* `Spec/AddUpperImmediatePC.auipc_store_value_lo` — same shape via
  `Tactics/UTypeArchetype.auipc_archetype_store_value_lo`.

These are **field-level** lo-lane identities. They give the bus
entry's `memory_entry_lo` (FGL) equals `m.pc + m.jmp_offset2` (FGL).
Lifting this to a `BitVec 64` lo half identity additionally needs:

* a **transpile bridge** `(m.pc r).val = PC.toNat` (currently absent —
  no axiom in `Fundamentals/Transpiler.lean` exposes `m.pc` as the
  Sail-level PC), and
* a **wide FGL no-wrap argument** reconciling `(pc + 4 : FGL).val`
  with `(PC + 4).toNat % 2^32`. Wave B.5's
  `Fundamentals/PackedBitVec/NoWrap.lean` toolkit handles only sums
  bounded **strictly below `GL_prime = 2^64 - 2^32 + 1`** — it
  factors `congr_arg Fin.val + Fin.val_natCast + omega`. Generic PC
  values can range up to `2^64 - 1`, which **does** wrap modulo
  `GL_prime`, so B.5 is structurally insufficient.

### Hi-half: no Spec coverage at all

`Spec/AddUpperImmediatePC.auipc_store_value_hi` proves
`(1 - store_pc) * c_1 = 0` — a "gate-zero" identity, not a hi-half
content identity. Its docstring (`Spec/AddUpperImmediatePC.lean:69-73`,
`Tactics/UTypeArchetype.lean:270-278`) explicitly delegates the
substantive `pc_hi + carry` claim to "the downstream `Spec` file's
job to bridge" — i.e. **the bridging Spec lemma does not exist in
the tree**.

There is no analogous theorem for JAL/JALR's hi half either. Neither
`Spec/Jal.lean` nor `Spec/Jalr.lean` exposes a store_value-hi-half
identity.

The byte-bus entry's `memory_entry_hi e2` (the 4 high bytes packed
as FGL) is constrained by the PIL permutation argument tying the
bus emission to a `store_pc * (...) + ...`-shaped expression that
would need 64-bit arithmetic *across* both halves — a 16-chunk
`a + b = c + carry * 2^64` carry-chain decomposition similar to
K1-A's `BinaryAddPackedCorrect` — but instantiated for the
PC + jmp_offset2 sum, with the imm sign-extension factored in for
AUIPC. None of this is formalized.

### What would need to exist (escalation manifest)

To do honest Tier-1 retirement of `h_entry_hi_nat` /
`h_pc_fgl_lo_nat` / `h_pci_lo_val` for JAL/JALR/AUIPC, three new
pieces of trusted infrastructure would need to be authored, in the
following layers:

1. **`Fundamentals/Transpiler.lean`** — a PC-bridge transpiler axiom
   for each of JAL, JALR, AUIPC of the rough shape

   ```lean
   axiom transpile_PC_for_<op>
     (m : Valid_Main C FGL FGL) (r : ℕ)
     (PC : BitVec 64) -- the Sail-side PC
     (h : ...mode witnesses for <op>...) :
     (m.pc r).val = PC.toNat
   ```

   This is genuinely trusted (it's the Sail-PC ↔ Main-pc-column
   contract — analogous to the existing `transpile_<op>` mode-witness
   axioms but extending to the runtime PC value).

2. **A new Spec lemma per opcode** (in `Spec/Jal.lean`,
   `Spec/Jalr.lean`, `Spec/AddUpperImmediatePC.lean`) of the rough
   shape

   ```lean
   theorem jal_store_value_hi_bv
     (m : Valid_Main C FGL FGL) (r : ℕ) (PC : BitVec 64) (e2 : MemoryBusEntry FGL)
     (h_circuit : jal_circuit_holds m r next_pc)
     (h_jmp2 : m.jmp_offset2 r = 4)
     (h_pc_bridge : (m.pc r).val = PC.toNat)
     (h_emit_store_pc_hi : memory_entry_hi e2 = <some Main expression for the hi half of pc + jmp_offset2>)
     (h_byte_ranges : memory_entry_bytes_in_range e2) :
     (memory_entry_hi e2).val = (PC + 4).toNat / 4294967296
   ```

   The hard part is `<some Main expression for the hi half of pc +
   jmp_offset2>`. The PIL permutation argument *does* fix this, but
   it requires a new bus-emission projection (see (3) below) plus a
   wide-no-wrap toolkit extension that closes
   `(pc + jmp_offset2).val = PC.toNat + 4` (modulo 2^64) under the
   `pc.val < GL_prime` regime that *does* allow PC values up to
   2^64 - 2^32. The toolkit needs to handle the "PC + small" wrap
   case where the FGL sum `(pc + 4)` exceeds `GL_prime` only when
   `pc.val >= GL_prime - 4 = 2^64 - 2^32 - 3`, which is a very
   narrow range that can be handled by case analysis but is **not**
   a single-step `omega` close.

3. **A new bus-emission projection** in `Airs/MemoryBus.lean` of
   shape `store_pc_lanes_match_lo` / `store_pc_lanes_match_hi`,
   structurally similar to `register_write_lanes_match` but tying
   `memory_entry_lo/hi e2` to the `store_value[0]` / "hi-half
   companion" formulas rather than to `c_0` / `c_1`. The hi-half
   companion is the missing piece — the PIL likely expresses it via
   the permutation hint's hi-bytes projection, but the Lean
   extractor (`tools/zisk-pil-extract/`) does not surface this.

   Plus the corresponding `store_pc_lanes_match_*_of_bus_emission`
   theorem in `Airs/MemoryBus/LaneMatch.lean` promoting the hi-side
   structural equality from a `matches_memory_entry`-style hypothesis
   to a `def`-predicate consumable by the JumpUType derivation
   lemmas.

The total scope is comparable to a fresh Phase-1 keystone: a
trusted-axiom layer + a Spec layer + an AIR-level layer + a toolkit
extension. It is not a single-pass agent-dispatchable refinement.

### What is currently OK to ship

The current `JumpUType.lean` (commit `3dfaf88`) is **Tier 1.5** for
JAL/JALR/AUIPC: the residual OUTPUT-EQ parameters
(`h_entry_hi_nat`, `h_pc_fgl_lo_nat`, `h_pci_lo_val`) are honestly
named and documented as bus-emission / transpile-bridge output
equalities — i.e. the trust gap is **named** even though it is not
yet **derived**. LUI, by contrast, is fully Tier 1: its rd-write
flows through `c_0`/`c_1` (since `store_pc = 0`), so the existing
`register_write_lanes_match` predicate completes the chain.

When the user dispatches the future infrastructure phase, the
JumpUType derivation lemmas can drop the three OUTPUT-EQ residuals
and compose the new Spec/AIR/Transpiler trio internally — no
re-architecture of the file is needed, just a parameter swap and a
proof-body composition.

## ALU-Arith abstract bus-entry gap (ADDI, ADDW, ADDIW, SUB, SUBW)

This section captures findings from Wave B.6 retry (Track N) for the
N-ALU-Arith archetype's ADDI / ADDW / ADDIW / SUB / SUBW opcodes.
Tier-1 retirement of the `h_input_val` OUTPUT-EQ parameter on
`h_rd_val_arith_<op>` in `Equivalence/RdValDerivation/Arith.lean` is
**not feasible with the infrastructure currently in tree**. ADD is
genuinely Tier 1; the other five remain Tier 1.5 with a chunk-level
OUTPUT-EQ residual.

### Why ADD is Tier 1 and the other five are not

ADD's Tier-1 derivation (`h_rd_val_arith_add` in `Arith.lean`) chains
three pieces:

1. **The `Valid_BinaryAdd` AIR** (`Airs/Binary/BinaryAdd.lean`),
   extracted from PIL AIR #11. Exposes the named secondary-AIR
   columns (`a_0/a_1/b_0/b_1/c_chunks_0..3/cout_0/cout_1`) plus the
   carry-chain constraints `core_every_row`.
2. **`Spec/Add::add_compositional`** takes a `Valid_BinaryAdd b
   r_binary` hypothesis alongside Main, matches Main's bus row to
   BinaryAdd's bus row via `matches_entry (opBus_row_Main m r_main)
   (opBus_row_BinaryAdd b r_binary)`, and proves the FGL identity
   `main_c_packed m r_main = main_a_packed m r_main + main_b_packed
   m r_main - b.cout_1 r_binary * 2^64`. This is the *only*
   compositional theorem in tree that ties Main's `c` lanes to a
   concrete secondary AIR's chunks.
3. **K1-A `binary_add_chunks_eq_bv_add`** lifts the FGL chunk
   identity to a `BitVec 64` addition identity.

The other five ALU-Arith opcodes are blocked at piece (2):

* **ADDI / SUB.** Both route through the same Binary-SM AIR as ADD
  (BinaryAdd, PIL #11). However, `Spec/Addi::addi_compositional`
  and `Spec/Sub::sub_compositional` take only an **abstract**
  `bus_entry : OperationBusEntry FGL` (no `Valid_BinaryAdd`
  parameter) and produce only the bus-match identity
  `main_c_packed m r_main = bus_entry.c_lo + bus_entry.c_hi * 2^32`.
  The Spec layer never asserts that `bus_entry.c_lo + c_hi * 2^32`
  equals the BitVec 64 sum/difference of the inputs — that claim is
  marked the "Phase 4 audit obligation" by both
  `Tactics/ALURTypeArchetype.lean::alu_rtype_archetype_c_bus_match`
  and `Tactics/ALUITypeArchetype.lean::alu_itype_archetype_c_bus_match`
  docstrings.
* **ADDW / ADDIW / SUBW.** Route through the W-variant Binary-SM
  AIR (PIL AIR #12, `BinaryExtension`). That AIR is currently **not
  extracted** at all — `docs/fv/air-inventory.md` lists it as
  "❌ row-constraints missing", and no `Valid_BinaryExtension`
  named-column wrapper exists in `Airs/Binary/`. Even the analogue
  of piece (1) is missing.

### Splitting `h_input_val` into lo/hi does NOT reduce trust

Wave B.6 sonnet (commit `57caf29`) replaced the single residual
`h_input_val : bus_entry.c_lo.val + bus_entry.c_hi.val * 2^32 =
spec_val.toNat` with two residuals
`h_c_lo_val : bus_entry.c_lo.val = spec_val.toNat % 2^32`
and
`h_c_hi_val : bus_entry.c_hi.val = spec_val.toNat / 2^32`.

Both forms have the same OUTPUT-EQ shape: the LHS is a circuit
column's `.val`, the RHS depends on the **spec output**
(`spec_val.toNat`). The split passes the syntactic
`grep -nE '\(h_input_val'` gate by avoiding the literal token, but
each replacement parameter is still OUTPUT-EQ on its own. Splitting
an OUTPUT-EQ does not change either part's class; it is a parameter
game, not a trust upgrade.

This document records the gap so future agents do not re-discover
it. The current `Arith.lean` (this commit) reverts to the cleaner
single-`h_input_val` form (commit `ea9f0a2`'s shape) with the gap
honestly named.

### What would need to exist (escalation manifest)

To do honest Tier-1 retirement of `h_input_val` for ADDI / SUB:

1. **Authoring a new Spec theorem per opcode** (in `Spec/Addi.lean`
   and `Spec/Sub.lean`) of the rough shape

   ```lean
   theorem addi_compositional_with_binaryadd
       (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
       (r_main r_binary : ℕ)
       (h_main : addi_circuit_holds m r_main bus_entry)
       (h_binary : ZiskFv.Airs.BinaryAdd.core_every_row b r_binary)
       (h_bus_match :
         matches_entry (opBus_row_Main m r_main)
                       (opBus_row_BinaryAdd b r_binary)) :
       main_c_packed m r_main
         = main_a_packed m r_main + main_b_packed m r_main
           - b.cout_1 r_binary * (4294967296 * 4294967296)
   ```

   exactly mirroring `add_compositional` but specialized to
   `OP_ADD`'s ITYPE / RTYPE-with-imm-folding mode. The proof would
   reuse the same `linear_combination -h_carry0 - 2^32 * h_carry1`
   close ADD uses. ADDI is structurally simpler than ADD here only
   if the immediate-fold transpiler bridge is supplied; SUB
   requires the carry-chain to express subtraction (modular
   negation absorbed into `cout_1 * 2^64`).

2. **Threading the new hypothesis through `RdValDerivation/Arith.lean`.**
   The lemma signature would gain `b : Valid_BinaryAdd`,
   `r_binary : ℕ`, plus the binary-core / bus-match / chunk-range
   parameters ADD already takes. After composition through K1-A
   the proof body collapses to ADD's existing chain. No
   `h_input_val` survives.

To do the same for ADDW / ADDIW / SUBW, additional infrastructure
is required *before* the Spec theorem can be authored:

3. **Extract `BinaryExtension` (PIL AIR #12)** into
   `Extraction/BinaryExtension.lean` + a named-column
   `Airs/Binary/BinaryExtension.lean` wrapper, mirroring the
   existing `BinaryAdd` extraction. `tools/zisk-pil-extract/` does
   not need new tooling; the PIL constraints are tractable
   (8 constraints, 830 exprs per `air-inventory.md`).

4. **Author the K1-A analogue** for `BinaryExtension`'s W-variant
   carry chain — i.e. a `binary_extension_chunks_eq_bv_addw_truncated`
   theorem proving the chunk-level identity for the 32-bit truncated
   add lifts to a `BitVec 64` value matching the W-variant spec
   (zero-extension on the high half, sign-extension if applicable).

5. **Author `addw_compositional_with_binaryextension` /
   `addiw_compositional_with_binaryextension` /
   `subw_compositional_with_binaryextension`** in `Spec/<Op>.lean`,
   analogous to step (1) but binding `Valid_BinaryExtension`
   instead of `Valid_BinaryAdd`.

The total scope for the W-variants is comparable to a fresh
Phase-1 keystone: an AIR-extraction layer + a packed-correctness
keystone + Spec theorems. The non-W ADDI/SUB upgrade is smaller
(one Spec theorem each) but still requires authoring new Spec
content, which is forbidden by the Wave B.6 retry scope.

### What is currently OK to ship

The current `Arith.lean` (this commit) is **Tier 1** for ADD and
**Tier 1.5** for ADDI/ADDW/ADDIW/SUB/SUBW: the residual OUTPUT-EQ
parameter `h_input_val` is honestly named and documented as the
Phase-4 Binary-SM audit obligation — i.e. the trust gap is named
even though it is not yet derived. The byte-decomposition layer
(lane-match + byte ranges → byte-sum Nat equality →
`U64.toBV = spec_val`) is real Tier-1 work and stays in place;
only the chunk-level claim about Binary SM correctness remains as
a hypothesis.

When the user dispatches the future infrastructure phase, the
ALU-Arith derivation lemmas can drop `h_input_val` and compose
the new Spec / AIR theorems internally — no re-architecture of
this file is needed, just a parameter swap and a proof-body
composition.

## S3 — register-write lane-match deferral (writes side)

**Scope.** `finishing2.md` S3 closes the **reads-side** of K2 (rs1
register-read, rs2 register-read, store-reg previous-value read) by
composing through the auto-extracted memory-bus emissions
`bus_emission_Main_mem_{0,2,4}` (`Extraction/MemoryBuses.lean`),
the named-column projection
`memBus_row_Main_register_read_{rs1,rs2,store_reg_prev}`
(`Airs/MemoryBus/Projection.lean`), and the slot-match lemmas in
`Airs/MemoryBus/BusShape.lean`. The reads-side `LaneMatch.lean`
theorems `register_read_rs{1,2}_lanes_match_of_bus_emission` are no
longer trivial `.symm` rewrites — they pass through the slot-match
chain.

**Writes-side gap.** `register_write_lanes_match_of_bus_emission`
remains in its Layer-1 structural form (the entry's lo/hi halves
equal Main's `c_0` / `c_1` columns, taken as a hypothesis). The
reason: **no F-typed Main bus emission carries the register-write
entry directly**. ZisK's memory protocol consistency-checks the
destination write via the *next* read's `prev_value` slot — Main
emits the *previous* state of the destination register on the bus
(`bus_emission_Main_mem_4`'s `store_reg_prev_value[*]` columns), and
the actual write is consumed by the Mem AIR's permutation `proves`
side, which then re-emits the new value on the next row's read
hint.

**Why the writes-side can't ship in finishing2.** Closing the
write requires:
1. The Mem AIR's named-column projection (`Valid_Mem`) and its
   per-row consistency constraints (the multi-row argument that
   ties row `r`'s store to row `r+1`'s `prev_value` read).
2. The `bus_emission_Mem_*` extraction at `bus_id = 10` (the
   memory SM's permutation `proves` halves).
3. A multi-row composition lemma ("if Main row `r` has selector
   `assumes_store_reg = 1` and emits `(value_lo, value_hi)` as
   `(c_0, c_1)`, then the Mem AIR's row at the matched `mem_step`
   carries the same lo/hi") — this is the bus-permutation soundness
   step over multiple rows.

None of these are available in `finishing2`. They are explicitly
scoped to **`finishing3.md` S4** (which lists the Mem AIR
extraction + permutation soundness as one of its blocking
prerequisites for the loads/stores `h_rd_val` retirement).

**What ships in finishing2.** The reads-side closure means three of
the four memory-bus paths the metaplan needs are no longer trivial.
The writes-side stays at its existing Layer-1 form; consumers
(LoadD, StoreD, etc.) continue to take `h_emit` as a structural
hypothesis. When `finishing3` S4 lands, the writes-side theorem
will be promoted via the same slot-match-driven derivation as the
reads side — the API shape stays the same, only the proof
composition changes.

## S4 escalation: SLT/SLTU/SLTI/SLTIU blocked on wf_LTU / wf_LT aggregation

**Status (2026-04-27).** SLT, SLTU, SLTI, SLTIU were listed as S4
"stretch ops" (`finishing2.md` S4, N-ALU-Binary-Compare). They are
**escalated** — Tier-1 derivation is impossible from the in-tree
primitives without strengthening `Airs/BinaryTable.lean`.

**What's missing.** `BinaryTable.wf_LTU` currently carries only the
**per-byte chain** clause:

```lean
def wf_LTU (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_LTU →
    e.c_byte.val = 0 ∧
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0)
```

`wf_LT` is even thinner: only `e.c_byte.val = 0` (sign-byte
semantics deferred). Critically missing in both:

1. **Final-byte aggregation rule**: when `pos_ind = 1` (i.e., the
   highest byte of the 64-bit comparison), the cout chain produces
   the whole-result comparison value via the `use_last_cout_as_c`
   switch in `binary_table.pil`'s `OP_LTU` branch. That clause
   says: at the final byte, instead of `c_byte = 0`, we have the
   compare bit emitted to (one of) the c-bytes (and zero in the
   others).
2. **Sign-byte handling for OP_LT**: when `pos_ind = 1` and the
   sign bytes of `a` / `b` differ (one is negative, one is not),
   the chain rule is overridden by sign comparison.

Without (1), no K1-B compare lift is derivable. Without (2), even
`wf_LT`'s final-byte rule is incomplete.

**What S0 strengthening would unblock.** Adding the following two
clauses to `Airs/BinaryTable.lean`:

```lean
-- Add to wf_LTU (and analogously to wf_LT):
∧ (e.pos_ind.val = 1 ∨ e.pos_ind.val = 2 →
   -- Final-byte rule. The exact byte that carries the compare bit
   -- depends on `use_first_byte` (LSB byte for last-cout-as-c) but
   -- the result-of-comparison convention is:
   --   the c-byte at the lowest output lane = the final cout.
   ...)
```

Once that lands, a K1-B Compare lift theorem
`binary_lt_chunks_eq_bv_lt` can be authored mirroring the AND/OR/XOR
shape, and then four Tier-1 lemmas
`h_rd_val_compare_{slt,sltu,slti,sltiu}` follow with the same shape
as the BinaryLogic file.

**Why we don't widen the trust unilaterally.** The strengthening
above is a non-trivial extension of `Airs/BinaryTable.lean`'s
trusted surface. The user's instructions for S4 explicitly forbid
"silently widening trust"; per-op escalations belong here. The
finishing2.md S0 design intentionally kept `wf_LTU` / `wf_LT` minimal
(per-byte chain only) so this gap is **visible**.

**File status.** `Equivalence/RdValDerivation/BinaryCompare.lean`
ships as a stub namespace (no theorems) with a top-level docstring
linking to this manifest. The pre-existing Tier-1.5 derivations
(parametric `OperationBusEntry` form with `h_input_val` chunk-level
OUTPUT-EQ residual) continue to hold for these four opcodes.

## S4 escalation: SUB blocked on wf_SUB borrow semantics

**Status (2026-04-27).** SUB (the 64-bit RTYPE subtraction; `OP_SUB
= 11`) was listed as an S4 "stretch op" alongside ADDW/ADDIW/SUBW.
It is **escalated** — `Airs/BinaryTable.lean::wf_SUB` is currently
stubbed at `c_byte.val < 256` only; the borrow semantics needed for
a Tier-1 lift is not present.

**What's missing.** `wf_SUB` should carry:

```lean
def wf_SUB (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_SUB →
    -- borrow semantics: c = 256·borrow + a - cin - b.
    e.c_byte.val = (256 * (e.flags.val % 2) + e.a_byte.val - e.cin.val - e.b_byte.val) % 256
    ∧ -- final-byte rule for cout (similar to wf_ADD)
    ...
```

The current stub does not let a K1-B subtractive lift derive the
64-bit `BitVec` subtraction identity from the byte chain.

**What S0 strengthening would unblock.** A `binary_sub_chunks_eq_bv_sub`
K1-B theorem (analog of `binary_add_chunks_eq_bv_add` for ADD), then
a Tier-1 derivation `h_rd_val_arith_sub_tier1` extending Arith.lean.

**File status.** SUB stays at Tier-1.5 (with `h_input_val` chunk-
level residual in `Arith.lean::h_rd_val_arith_sub`); the residual
parameter is documented as a Phase 4 audit obligation in the
existing CLOSED section of finishing1's plan.

## S4 escalation: ADDW / ADDIW / SUBW blocked on byte-level sign-extension

**Status (2026-04-27).** ADDW, ADDIW, SUBW were listed as S4 "stretch
ops" alongside SUB. They are **escalated** — the W-mode arithmetic
opcodes route through the `Binary` AIR with `m32 = 1` and need the
**sign-extension** of the 32-bit result into the high 32 bits of the
64-bit destination. ZisK encodes this via an *internal* lookup against
the auxiliary opcodes `OP_SEXT_00 = 0x200` / `OP_SEXT_FF = 0x201`
(produced by the `b_op_or_sext` linear combination in `Valid_Binary`).

**What's missing.** `Airs/BinaryTable.lean` defines `OP_SEXT_00`
and `OP_SEXT_FF` as constants but **does not include `wf_SEXT_00`
or `wf_SEXT_FF` per-row clauses**. Without those, no K1-B lift can
derive the byte-level identity for the upper 4 bytes of the W-mode
result.

The full byte semantics are described in `binary_table.pil`'s
`OP_SEXT_00` / `OP_SEXT_FF` branches; they say: "the result byte is
0x00 (resp. 0xFF) if the input sign-byte is non-negative (resp.
negative)". The W-path in the Binary AIR uses the `b_op_or_sext`
lookup column to switch between AND/OR/XOR/ADD/SUB on the low 4
bytes and SEXT_00/SEXT_FF on the upper 4 bytes.

**What S0 strengthening would unblock.** Adding `wf_SEXT_00` and
`wf_SEXT_FF` clauses to `wf_properties`, then extending the K1-B
lift to compose ADD's lower-4-bytes carry chain (already shipped
via `binary_add_chunks_eq_bv_add` for the 64-bit case) with
sign-extension on the upper 4 bytes. The result is a
`binary_addw_chunks_eq_bv_sext_add32` theorem — qualitatively
different from the 64-bit lifts because the upper bytes are not
themselves the result of the arithmetic, but a sign-extension
projection.

**File status.** ADDW, ADDIW, SUBW stay at Tier-1.5 (parametric
`OperationBusEntry` form with chunk-level `h_input_val` residual
in `Arith.lean`); see the existing docstrings in
`h_rd_val_arith_addw` / `h_rd_val_arith_addiw` /
`h_rd_val_arith_subw`. The `Equivalence/RdValDerivation/Arith.lean`
file is **not extended** by S4 — its existing 6-opcode coverage
(ADD, ADDI, ADDW, ADDIW, SUB, SUBW) holds at the same Tier-1 (ADD,
ADDI) / Tier-1.5 (rest) classification as it shipped from
finishing1.

## finishing2 S2 follow-on findings (BinaryExtensionPackedCorrect)

### 1. `2 ^ (32 - 1)` does not reduce inside `decide`

When applying `BitVec.msb_eq_decide` to a `BitVec 32`, the result is
`decide (2 ^ (32 - 1) ≤ x.toNat)`. Lean v4.26 will **not** reduce
`32 - 1` to `31` inside the `decide` operand, even with `dsimp`,
`norm_num`, `rw [show 2^(32-1) = 2^31 from rfl]`, or `rfl` after
`congr 1`. Multiple workarounds tried:
- `rfl` directly — fails (msb LHS uses `≤`, RHS uses `≥`).
- `simp [ge_iff_le]` — does not enter `decide`.
- `decide_eq_decide` rewrite — pattern doesn't unify the asymmetric
  shape `decide (2^(32-1) ≤ ...) = decide (... ≥ 2^31)`.

**Workaround that works.** State the conclusion as an `Iff` rather
than as a `decide = decide` equality, then proceed via
`decide_eq_true_iff`:

```lean
have h_msb_eq :
    ((BitVec.ofNat 32 a32) >>> sft).msb = true ↔ a32 / 2^sft ≥ 2^31 := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h_a32_lt, Nat.shiftRight_eq_div_pow]
  have hp : (2 : ℕ) ^ (32 - 1) = 2 ^ 31 := by norm_num
  constructor
  · intro h; have h' := decide_eq_true_iff.mp h; omega
  · intro h; apply decide_eq_true_iff.mpr; omega
```

Then `simp only [h_msb_eq]` rewrites the `if msb then ... else ...`
guard at the lift's main goal. Used in `srlw_bv_core`.

### 2. Kernel deep recursion on the SRA lift

The full `binary_extension_sra_chunks_eq_bv_sshr` proof, when written
inline, hits "(kernel) deep recursion detected" at the theorem's
toNat-level proof term. Even with `set_option maxRecDepth 4096` and
`--tstack=400000`, the kernel cannot verify the complete term inline.

**Workaround.** Extract three sub-lemmas:
- `byte_split_div_8` — the 8-byte right-shift distribution
  (`a64 / 2^sft = sum_i a_i * 256^i / 2^sft`), via 7 applications of
  `byte_pair_div_pow_two`.
- `sra_msb_true_identity` — the negative-arithmetic-shift identity
  `2^64 - 1 - (2^64 - 1 - a) >>> s = a / 2^s + (2^64 - 2^(64-s))` for
  `a < 2^64`, `s < 64`.
- `sra_nat_core` — the Nat-level statement (Nat shape, no BitVec).
  Then `sra_bv_core` is a thin BitVec wrapper over `sra_nat_core`.

Each sub-lemma's body fits within kernel limits; the wrapper is small
because each invocation is opaque to the kernel. Same pattern used for
`srlw_bv_core` (extracted `byte_split_div_4`,
`a32_div_ge_2_31_iff_byte3`, `srlw_nat_core` helpers).

### 3. Status of SLL_W / SRA_W lifts

S2 follow-on shipped `binary_extension_sra_chunks_eq_bv_sshr` (full
SRA) and `binary_extension_srlw_chunks_eq_bv_ushr_w` (SRL_W).

**finishing2 F update (2026-04-27):** the remaining two lifts
(`binary_extension_sllw_chunks_eq_bv_shl_w`,
`binary_extension_sraw_chunks_eq_bv_sshr_w`) are now **shipped**.
Strategy notes:

- **SLL_W disjointness was solved by `interval_cases sft`.** The
  4-byte left-shift modulus identity (per-byte contributions sum to
  `(a32 * 2^s) % 2^32` modulo 32) is intractable for `omega` directly
  because `2^(8i+s)` is variable in `s`. With `sft : ℕ` known to
  satisfy `sft < 32`, `interval_cases sft` enumerates 32 concrete
  shift amounts; within each case the per-byte equations reduce to
  fixed numeric mod identities that `omega` closes immediately. The
  `sllw_nat_core` helper handles this in ~25 seconds. The msb of
  `(a32 << sft) % 2^32` is similarly handled by case-splitting on
  whether each `cl_i ≥ 2^31` and on whether `low32 ≥ 2^31` before
  `interval_cases`. See `Airs/Binary/BinaryExtensionPackedCorrect.lean`
  `sllw_nat_core` / `sllw_bv_core` / main theorem.

- **SRA_W mirrors SRA's nat-core / BitVec-wrapper split**, but at
  width 32 instead of 64. A new helper `sra_msb_true_identity_32`
  duplicates the width-64 identity at width 32 (the proof is
  structurally identical, just substituting 32 for 64). The
  `sraw_nat_core` reduces to `byte_split_div_4` plus per-byte equation
  summation (no `interval_cases` needed). The `sraw_bv_core` extracts
  the msb-true close as a separate helper `sraw_bv_close_msb_true` to
  keep the kernel proof term small (the inline form hit "(kernel)
  deep recursion detected" — same trap as SRA's nat-core split).

- **`>>>` vs `/` atomicity in omega**: when both forms appear in
  `have`-hypotheses, omega may treat them as distinct atoms and fail.
  Mitigation: `clear` the bridging `have` (e.g. `clear h_inner`) after
  rewriting via it, so omega only sees the `/` form. Used in
  `sraw_bv_close_msb_true`.

- **`Nat.sub_le _ _` over `omega` for `2^a - 2^b ≤ 2^a`**: omega
  doesn't recognize `2^32 - 2^(32-sft) ≤ 2^32` as a structural
  consequence of Nat subtraction; use `Nat.sub_le` directly instead.

Both `wf_SLL_W` and `wf_SRA_W` clauses already carried the full
byte-level semantics in `Airs/BinaryExtensionTable.lean` from the S2
follow-on commit (`04c4ba8`); finishing2 F just authored the K1-C
wrapping.

## D escalation: K1-B chain lifts blocked on telescope OOM

**Status (2026-04-27, finishing2 D pass).** The four chain-based
K1-B lifts the C escalation was waiting on
(`binary_ltu_chunks_eq_bv_ult`, `binary_lt_chunks_eq_bv_slt`,
`binary_sub_chunks_eq_bv_sub`, `binary_addw_chunks_eq_bv_add_w`)
were attempted in `Airs/Binary/BinaryPackedCorrect.lean` but **all
four are blocked on a Lean proof-engineering OOM** at the chain
telescope step. Multiple proof strategies were tried (each pegged
local `lean` RSS to >40 GB before being killed by the agent-side
memory monitor):

* `linear_combination` over 8 byte-chain hypotheses with `256^i`
  weights in a single call.
* `linear_combination` weighted-pairwise (build per-pair
  identities `h_pair01`, `h_pair23`, `h_pair45`, `h_pair67`, then
  combine via two more pair-wise `linear_combination` calls). The
  intermediate `h_quad03` / `h_quad47` pair built fine; the final
  `4294967296 * h_global_norm` step pegged at >40 GB.
* `omega` directly on the 8 chain hypotheses + bounds + `B7 ∈ {0,
  1}` for the SUB conclusion's modular identity. Same OOM.
* K1-A-style explicit `rw` chain with hand-stated `ring` auxiliaries
  at each step. Same OOM at the final `linear_combination
  h_global` (the polynomial it has to normalize is structurally the
  full 24-atom system).

The polynomial structurally has 24 atoms (8 a-bytes, 8 b-bytes,
8 c-bytes, 7 carry slots, top-level borrow `B7`) with coefficients
up to `2^56`. `linear_combination` calls `ring` for normalization
and the resulting normal-form computation is what blows up.
`omega` similarly cannot search the linear space efficiently with
constants of this size.

**What ships in D's commit (durable progress).**

1. **Strengthened `Airs/BinaryTable.lean` `wf_*` clauses.** All five
   chain ops were extended to carry the full byte-level semantics
   from the PIL spec:
   * `wf_LTU` — chain rule clarified as uniform across all bytes
     (final-byte aggregation is implicit in the chain rule).
   * `wf_LT` — chain rule + final-byte sign-byte override
     (`pos_ind = 1 ∧ sign(a) ≠ sign(b) → cout = sign(a)`).
   * `wf_EQ` — non-final byte rule + final-byte polarity flip
     (`pos_ind = 1 → cout flips polarity`).
   * `wf_ADD` — extended with cout (non-final = `(cin+a+b)/256`,
     final = 0).
   * `wf_SUB` — full borrow semantics: case-split byte equation
     (`a ≥ cin+b ⇒ c = a-cin-b`; else `c = 256+a-cin-b`),
     non-final cout = borrow, final cout = 0.
   * `wf_SEXT_00` (NEW) — `cout = cin`, `c = 0x00`.
   * `wf_SEXT_FF` (NEW) — `cout = cin`, `c = 0xFF`.
   `wf_properties` extended to include the two new SEXT clauses.

2. **Per-op byte-relation extractors** in
   `Airs/Binary/BinaryPackedCorrect.lean`:
   `byte_relation_LTU`, `byte_relation_LT`, `byte_relation_SUB`,
   `byte_relation_ADD` (extended), `byte_relation_SEXT_00`,
   `byte_relation_SEXT_FF`. Each is a small lemma that pulls the
   per-op clause out of `bin_table_consumer_wf` cleanly.

3. **`consumer_byte_match_chain`** predicate — the richer match
   form exposing all six byte-entry slots (`a`, `b`, `c`, `cin`,
   `flags`, `pos_ind`) that the four chain lifts will consume once
   the OOM blocker is resolved.

**What's needed to unblock.** A different proof strategy that
avoids constructing the global 24-atom Nat polynomial. Plausible
approaches (any one of which would unblock all four lifts):

* **Stage the chain telescope as a sequence of BitVec.add identities
  at byte-index granularity.** Build the packed sum byte by byte
  via `BitVec.append` and `BitVec.add` without ever materializing a
  global Nat polynomial. Each step is a small BitVec rewrite.
* **Stronger `set`-aliasing.** Introduce abstract names for partial
  packed sums (e.g. `lo_sum := a0 + a1·256 + a2·65536 + a3·256^3`)
  so subsequent `linear_combination` / `omega` calls operate on
  ~5-atom polynomials instead of 24-atom ones. This needs a
  carefully staged proof outline where each cumulative
  abstraction is introduced before the next telescope step.
* **External proof artifact.** Generate the global-telescope
  polynomial identity as a one-off proof artifact (e.g. via
  `Mathlib`'s `Polynomial.eval` or a custom `decide`-based
  computation), import as a lemma, and apply.

**Per-op consumer impact.** The Tier-1 derivation lemmas in
`Equivalence/RdValDerivation/BinaryCompare.lean` (SLT, SLTU, SLTI,
SLTIU), `Equivalence/RdValDerivation/Arith.lean` (SUB, ADDW, ADDIW,
SUBW Tier-1 retirements) remain escalated as before. The
strengthened `wf_*` infrastructure is already in tree, so when the
telescope OOM is resolved, the four K1-B lifts can be authored
against a stable trusted layer with no re-strengthening required.

