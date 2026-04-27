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
