# finishing5 — store_pc=1 archetype Tier-1 (JAL, JALR, AUIPC)

**Branch:** TBD (likely `feature/track-n5-store-pc`).
**Predecessor:** `finishing1.md` ships ADD/LUI/ADDI/SUB Tier-1; this
plan covers the three opcodes that route through ZisK's `store_pc=1`
bus-emission path, where the trust gap is structurally different.

## Goal — h_rd_val Tier-1 retirement for 3 opcodes

| Opcode | rd-write | Sail spec output |
|---|---|---|
| JAL | link register: `rd ← pc + 4` | `PC + 4 : BitVec 64` |
| JALR | link register: `rd ← pc + 4` | `PC + 4 : BitVec 64` |
| AUIPC | rd ← `pc + (imm << 12 sign-extended)` | `PC + BitVec.signExtend 64 (imm ++ 0#12)` |

These opcodes have **Tier-1.5 discharge lemmas in tree** at
`ZiskFv/ZiskFv/Equivalence/RdValDerivation/JumpUType.lean` (commits
`a063edf` + `3dfaf88`; LUI in the same file is genuinely Tier-1
already and is in finishing1's scope). Each takes residual OUTPUT-EQ
parameters (`h_entry_hi_nat`, `h_pc_fgl_lo_nat`, `h_pci_lo_val`,
etc.) that this plan retires.

## Why this needs its own plan — the store_pc=1 gap

ZisK multiplexes opcode semantics through Main's `store_value[0]`
expression (`vendor/zisk/state-machines/main/pil/main.pil:311`):

```
  store_value[0] = store_pc * (pc + jmp_offset2 - c_0) + c_0
```

For `store_pc = 0` opcodes (ADD, ADDI, LUI, MUL, …) this collapses
to `c_0`, so the rd-write low half flows through Main's `c_0`
column and the existing `register_write_lanes_match` predicate
(`Airs/MemoryBus.lean:140-144`) ties memory-bus entry lanes to
Main's `c_0`/`c_1`.

For `store_pc = 1` opcodes (JAL, JALR, AUIPC) the formula evaluates
to `pc + jmp_offset2`. **There is no Main column that exposes
either the lo or hi 32-bit half of `pc + jmp_offset2` separately** —
Main only carries `pc : ℕ → FGL` as a single field element. The
byte-level decomposition that the memory-bus entry needs lives only
inside the PIL permutation argument tying the bus entry's 8 byte
lanes to `store_value[0]`'s two 32-bit halves.

Wave B.6 retry (commit `442ef86`) appended a thorough escalation
manifest to `docs/fv/track-n-traps.md` for this gap. This plan
implements that manifest.

## Scope items

### S1. Transpile contract: PC bridges

New axioms in `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean` exposing
the Sail-PC ↔ Main-`pc`-column correspondence for each store_pc=1
opcode:

```lean
axiom transpile_PC_for_JAL
    (m : Valid_Main C FGL FGL) (r : ℕ) (PC : BitVec 64)
    (h : ...JAL mode witnesses...) :
    (m.pc r).val = PC.toNat

axiom transpile_PC_for_JALR ...
axiom transpile_PC_for_AUIPC ...
```

These are CLAUDE.md trusted-surface (Sail-PC ↔ ZisK Main-pc-column
contract) — analogous to the existing `transpile_<op>` mode-witness
axioms but extending to the runtime PC value.

### S2. Wide-PC no-wrap toolkit extension

The B.5 `Fundamentals/PackedBitVec/NoWrap.lean` toolkit assumes both
sides of an FGL equation are `< GL_prime = 2^64 - 2^32 + 1`. But
`m.pc.val` can range up to `2^64 - 1`, which exceeds GL_prime.

New file `ZiskFv/ZiskFv/Fundamentals/PackedBitVec/WidePCNoWrap.lean`
(or extension to existing file). Required lemma:

```lean
-- Given pc.val < 2^64 (no GL_prime constraint), conclude
-- (pc + small_offset : FGL).val behaves like
-- (PC.toNat + small_offset) % 2^64
-- with case analysis on whether pc.val + offset < GL_prime
-- (no wrap) or wraps once.
theorem fgl_pc_plus_offset_to_bv64
    (pc_fgl : FGL) (PC : BitVec 64) (offset : ℕ)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_small : offset ≤ 4096) :
    BitVec.ofNat 64 ((pc_fgl + (offset : FGL)).val % 4294967296)
      = BitVec.ofNat 64 ((PC.toNat + offset) % 4294967296)
-- (and hi-half analog)
```

Case analysis on `pc.val + offset < GL_prime` vs the narrow window
`[GL_prime - offset, GL_prime)` where the FGL sum wraps once.

### S3. New Spec hi-half lemmas

For each of JAL, JALR, AUIPC, author a `<op>_store_value_hi_bv`
theorem in the corresponding Spec file:

```lean
-- ZiskFv/ZiskFv/Spec/Jal.lean (extending existing)
theorem jal_store_value_hi_bv
    (m : Valid_Main C FGL FGL) (r : ℕ)
    (PC : BitVec 64) (e2 : MemoryBusEntry FGL)
    (h_circuit : jal_circuit_holds m r next_pc)
    (h_jmp2 : m.jmp_offset2 r = 4)
    (h_pc_bridge : transpile_PC_for_JAL m r PC ...)
    (h_emit_hi : memory_entry_hi e2 = <expression bridging Main columns to bus entry hi half>)
    (h_byte_ranges : memory_entry_bytes_in_range e2) :
    (memory_entry_hi e2).val = (PC + 4).toNat / 4294967296
```

The `h_emit_hi` parameter is supplied by S4 below — it's the new
bus-emission projection that today doesn't exist. Each Spec lemma
composes S1 + S2 + the bus-emission projection to derive the
hi-half output equality.

Authoring sites:
- `ZiskFv/ZiskFv/Spec/Jal.lean`
- `ZiskFv/ZiskFv/Spec/Jalr.lean`
- `ZiskFv/ZiskFv/Spec/AddUpperImmediatePC.lean` — `auipc_store_value_hi_bv`
  (the existing `auipc_store_value_hi` proves only the gate-zero
  identity `(1 - store_pc) * c_1 = 0`; the substantive bridge is
  what's missing).

### S4. New AIR-level bus-emission projections

New definitions + theorems in `ZiskFv/ZiskFv/Airs/MemoryBus.lean`
and `ZiskFv/ZiskFv/Airs/MemoryBus/LaneMatch.lean`:

```lean
-- Airs/MemoryBus.lean (extension)
def store_pc_lanes_match_lo (m : Valid_Main ...) (r : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  memory_entry_lo e = m.store_pc r * (m.pc r + m.jmp_offset2 r - m.c_0 r) + m.c_0 r

def store_pc_lanes_match_hi (m : Valid_Main ...) (r : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  -- hi-half analogue; the PIL permutation hint determines this
  ...

-- Airs/MemoryBus/LaneMatch.lean (extension)
theorem store_pc_lanes_match_lo_of_bus_emission
    (m : Valid_Main ...) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_emit : ...) :
    store_pc_lanes_match_lo m r e

theorem store_pc_lanes_match_hi_of_bus_emission ...
```

The hi-half is the hardest piece. The PIL likely expresses it via
the permutation argument's hi-bytes projection, but the Lean
extractor (`tools/zisk-pil-extract/`) does not surface it (memory
bus extraction stubs ExtF-typed slots). Closing this requires
either:

- (a) Hand-authoring the projection by reading
  `vendor/zisk/state-machines/main/pil/main.pil` directly and
  encoding the permutation-faithful expression for the hi half.
- (b) Extending the extractor to surface the missing slots.

Option (a) is more tractable in the short term; option (b) is the
right long-term move but is its own scope.

### S5. Tier-1 upgrade for `RdValDerivation/JumpUType.lean`

For JAL, JALR, AUIPC (LUI is already Tier-1; leave alone): replace
the existing OUTPUT-EQ residual parameters with internal composition
of S1 (transpile_PC axioms) + S2 (wide-PC no-wrap) + S3 (new Spec
hi-half lemmas) + S4 (new AIR predicates).

**Hard semantic gate:** every parameter on each
`h_rd_val_jut_<op>` lemma is one of {CIRCUIT-CONSTRAINT,
LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN}. No OUTPUT-EQ
parameters survive.

### S6. Phase 3 cleanup — remove h_rd_val from 3 metaplan theorems

For `Equivalence/{Jal, Jalr, Auipc}.lean`:

1. Remove `h_rd_val :` from metaplan theorem signatures.
2. Replace with upgraded Tier-1 discharge call.
3. Add new circuit-hypothesis parameters as needed.

## Verification gates

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv

# After S1
lake build ZiskFv.Fundamentals.Transpiler

# After S2
lake build ZiskFv.Fundamentals.PackedBitVec.WidePCNoWrap

# After S3
lake build ZiskFv.Spec.Jal
lake build ZiskFv.Spec.Jalr
lake build ZiskFv.Spec.AddUpperImmediatePC

# After S4
lake build ZiskFv.Airs.MemoryBus
lake build ZiskFv.Airs.MemoryBus.LaneMatch

# After S5
lake build ZiskFv.Equivalence.RdValDerivation.JumpUType

# After S6
for op in Jal Jalr Auipc; do
  echo -n "$op: " ; grep -c 'h_rd_val :' "ZiskFv/ZiskFv/Equivalence/${op}.lean" 2>/dev/null || echo 0
done
# expected: 0 each

# Final
cd ZiskFv && lake build
# expected: 0 errors, 0 sorries
```

## Out of scope

- LUI — already Tier-1 in finishing1 (uses `store_pc = 0` path
  through `register_write_lanes_match`).
- Loads/stores — covered by finishing3 (those use a different
  bus-emission path through the Mem AIR).
- Branches — don't write rd; `h_rd_val` doesn't apply.

## Status / next action

Plan only. Branch not started. Predecessors: finishing1 must close
first; finishing3 helpful (the Mem AIR work in finishing3 may
incidentally surface bus-emission infrastructure that S4 can reuse,
but is not strictly required).

Total scope is comparable to a fresh Phase-1 keystone (S1: trusted
axiom layer; S2: toolkit extension; S3: Spec layer; S4: AIR layer;
S5+S6: per-opcode upgrade + cleanup), not a single agent dispatch.
The `docs/fv/track-n-traps.md` "store_pc=1 opcode rd-write: the
hi-half infrastructure gap" section (commit `442ef86`) has additional
detail on each piece.
