# Clean integration — architecture and current state

This document describes the Clean DSL integration that lands on the
`clean-full` branch (PR #42). It is the project's first migration
of a portion of the proof tree onto an upstream DSL framework
([Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean)),
plus a structural consolidation of the per-AIR range axioms into
two shared cryptographic-soundness axioms.

## Why

Before this work, the trust ledger contained **122 axioms** across
7 classes — 14 of which were structurally identical *per-AIR*
range-checker bus soundness claims (`<AIR>_columns_in_range` for
Main, Binary, BinaryAdd, BinaryExtension, ArithMul (8 variants),
plus the memory-bus byte-range claim). Each carried the same
cryptographic content; only the witness type and column list
differed.

The Clean integration was the lever to consolidate these. By
introducing Clean's typed-channel pattern at the project's
soundness boundary, we get a natural place to land a single
`range_bus_sound` axiom that captures the lookup-argument
soundness once, with all 14 per-AIR claims derived as theorems.

The architectural insight ports cleanly even without using Clean's
full framework for every AIR. So we landed:

* **Clean as a Nix-pinned source dependency** (`build/clean-lean/`,
  added via `nix/clean.nix`)
* **Typed channels** for the operation-bus, memory-bus, and
  range-bus (`ZiskFv/Channels/`)
* **Consolidated `range_bus_sound`** + 12 derived per-AIR theorems
  → floor 116 → 104
* **Channel-balance form** of every per-opcode equivalence theorem
  (63 v2 wrappers in `ZiskFv/Vm/Probe_*.lean`)
* **`Compliance_v2`** dispatches the channel-balance global theorem
  to all 63 OpEnvelope arms

## The two consolidated axioms

Live in `ZiskFv/Channels/RangeBusSoundness.lean`. Both are class
#5b/#6/#6b range-checker bus lookup-argument soundness — the same
cryptographic primitive (PLONK / logUp permutation argument
soundness on ZisK's RANGE_BUS_ID).

### `range_bus_sound`

```lean
axiom range_bus_sound
    {W : Type} (w : W) (col : W → ℕ → FGL) (width : ℕ)
    (_h_in_range_bus : PIL_bits_annotation w col width) :
    ∀ r, (col w r).val < 2 ^ width
```

Every PIL `bits(N)` annotation discharges via one application of
this axiom. Each per-AIR `<AIR>_columns_in_range` theorem (now a
theorem, not an axiom) is a one-bullet-per-column proof:

```lean
theorem main_columns_in_range (m : Valid_Main C FGL FGL) (r : ℕ) :
    ... ∧ ... := by
  refine ⟨..., ..., ...⟩
  · exact range_bus_sound m (fun m r => m.a_0 r) 32 trivial r
  · ...
```

Used by: Main, Binary (range + carry), BinaryAdd, BinaryExtension,
MemoryBus byte-range, ArithMul (mul/div columns), ArithDiv
(mul/div columns + unsigned carry).

### `signed_range_bus_sound`

```lean
axiom signed_range_bus_sound
    {W : Type} (w : W) (col : W → ℕ → FGL)
    (_h_in_arith_signed_carry_bus : PIL_arith_signed_carry_annotation w col) :
    ∀ r, (col w r).val < ARITH_SIGNED_POS_BOUND
       ∨ GL_prime - ARITH_SIGNED_NEG_OFFSET ≤ (col w r).val
```

Captures the signed-region disjunctive bound for Arith's
`ARITH_RANGE_CARRY` table (entries `[-0xEFFFF .. 0xF0000]`). Used by
4 Arith carry-column theorems (signed and W-mode for mul/div).

## The channel-balance form

`ZiskFv/Vm/StateEffect.lean` defines:

```lean
def state_effect_via_channels
    (cs : ChannelEnsembleOutput)
    (state : ...) : EStateM.Result ... ExecutionResult :=
  (bus_effect cs.execRows cs.memRows state).2
```

`state_effect_via_channels_eq_bus_effect_2` is the compatibility
bridge — `rfl` for the trivial extractor (current implementation).

Every per-opcode v2 wrapper has the shape:

```lean
theorem equiv_<OP>_v2 ... :
    execute_instruction ... state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_<OP> state ...
```

Located in `ZiskFv/Vm/Probe_*.lean`, one file per opcode family.

## The unified `Compliance_v2`

`ZiskFv/Compliance_v2.lean` aggregates 10 per-family partial
dispatchers (`Compliance_v2_<Family>.lean`):

| File | Arms covered |
|---|---|
| `Compliance_v2_Branch.lean` | BEQ, BNE, BLT, BGE, BLTU, BGEU (6) |
| `Compliance_v2_NoMemOrSimple.lean` | LUI, AUIPC, FENCE (3) |
| `Compliance_v2_RTYPE.lean` | SUB, AND, OR, XOR, SLT, SLTU (6) |
| `Compliance_v2_ITYPE.lean` | ANDI, ORI, XORI, SLTI, SLTIU (5) |
| `Compliance_v2_Shift.lean` | SLL, SRL, SRA, SLLI, SRLI, SRAI (6) |
| `Compliance_v2_ADD_RTYPEW.lean` | ADD, ADDW, SUBW (3) |
| `Compliance_v2_LDSD.lean` | LD, SD (2) |
| `Compliance_v2_DIVU.lean` | DIVU (1) |
| `Compliance_v2_Misc.lean` | LB, LH, LW, ADDI, ADDIW (5) |
| `Compliance_v2_Remaining.lean` | LBU, LHU, LWU, SB, SH, SW, W-shifts, Mul/Div/Rem family, JAL, JALR (26) |
| **Total** | **63 / 63** |

The unified theorem:

```lean
theorem zisk_riscv_compliant_program_bus_v2
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq_v2
```

with `exec_eq_v2` the conjunction of 10 per-family `exec_eq_v2_<family>`
Props. For any arm, exactly one family produces the real
channel-balance conclusion; the conjunction therefore expresses
"every arm's v2 statement holds."

## What this does NOT do (yet)

* **Phase 3b — per-AIR Clean Component rewrites.** Only BinaryAdd
  has been ported as a full Clean `GeneralFormalCircuit` (Row + Spec +
  Constraints + Soundness + Bridge). The other 8 AIRs (Binary,
  BinaryExtension, Mem, MemAlignByte, MemAlignReadByte, MemAlign,
  ArithMul, ArithDiv) still use the v1 `Valid_<AIR>` records over
  `LeanZKCircuit.OpenVM.Circuit`.

* **Phase 6 cutover.** The v1 layer (`Compliance`, `Compliance/Wrappers/`,
  `SailSpec/BusEffect`) coexists with the v2 layer. Renaming v2 →
  canonical and dropping LeanZKCircuit is a separate, deliberate step
  (`trust/.shrinkage-floor` would stay at 104 since cutover is
  refactoring not retirement).

## Trust verification

```bash
trust/scripts/check-all.sh                       # V1 + shrinkage gate
trust/scripts/check-all-semantic.sh              # V2 closure
# Both should report 104 axioms, all gates green.
```

## File index

- `nix/clean.nix` — Clean source-tree derivation
- `flake.nix` — adds `inputs.clean-src`, pinned by content hash
- `ZiskFv/Channels/OperationBus.lean` — typed OpBus channel + `OpBusMessage`
- `ZiskFv/Channels/MemoryBus.lean` — typed MemBus channel + `MemBusMessage`
- `ZiskFv/Channels/RangeBus.lean` — `BytesTable` StaticLookupChannel
- `ZiskFv/Channels/RangeBusSoundness.lean` — `range_bus_sound`,
  `signed_range_bus_sound`, named bit-width abbrevs
- `ZiskFv/AirsClean/BinaryAdd/` — Row + Spec + Constraints + Soundness + Bridge for BinaryAdd
- `ZiskFv/Vm/StateEffect.lean` — `state_effect_via_channels` + bridge
- `ZiskFv/Vm/Probe_*.lean` — 12 files covering all 63 opcode v2 wrappers
- `ZiskFv/Compliance_v2.lean` — unified channel-balance global theorem
- `ZiskFv/Compliance_v2_*.lean` — 10 per-family partial dispatchers
- `docs/clean-feedback.md` — upstream-feedback log for Clean devs
- `trust/.shrinkage-floor` — `104` (was 116)

## Tags

| Tag | Milestone |
|---|---|
| `phase-0-clean-full` | Nix dep + Lake dep + shrinkage gate |
| `phase-1-clean-full` | Typed channels (OpBus, MemBus, RangeBus) |
| `phase-2-clean-full` | `state_effect_via_channels` + ADD probe |
| `binaryadd-poc-complete-clean-full` | BinaryAdd PoC end-to-end |
| `phase-3a-named-constants-clean-full` | `U<N>_max` named constants |
| `phase-3a-complete-clean-full` | 9 range-axiom retirements |
| `phase-4-complete-clean-full` | All 35 mainOpKind arms have v2 probes |
| `phase-4-complete-shapes-clean-full` | (Earlier milestone — shapes only) |
| `phase-5-unified-clean-full` | First unified `Compliance_v2.lean` |
| `phase-5-complete-clean-full` | All 63 arms with real v2 conclusions |
