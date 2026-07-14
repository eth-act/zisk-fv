# `ZiskFv/EquivCore/`

Per-opcode **core** equivalence theorems — the bottom of the equivalence stack.
The top-level files here (`Add.lean`, `Addi.lean`, …, `Xori.lean`, one per
RV64IM opcode) each contain the core `equiv_<OP>` / `equiv_<OP>_sail` theorem in
the **`execute = bus_effect`** form:

```lean
equiv_<OP> :
  ∀ (state : SailState) (exec_row : ExecRow) (mem_row : MemRow)
    <promise hypotheses in safe trust classes>,
    LeanRV64D.Functions.execute (.<shape> …) state
      = (bus_effect exec_row mem_row state).2
```

Both sides live in Sail's state space. The LHS is the Sail RV64 spec's monadic
`execute`; the RHS is `SailSpec.BusEffect.bus_effect` applied to circuit-side
rows. The theorem's parameters are restricted to a fixed allowlist of safe trust
classes (`CIRCUIT-CONSTRAINT`, `LANE-MATCH`, `RANGE`, `TRANSPILE-BRIDGE`,
`TRANSPILE-PIN`); the forbidden shapes are listed in
`trust/forbidden-param-shapes.txt` / `trust/forbidden-types.txt` and enforced
uniformly by the trust gate across every opcode (no carve-outs — the load
opcodes were closed by deriving their cross-entry rd-value byte equations from
circuit witnesses in `ZiskCircuit/LoadDerivation.lean` and
`ZiskCircuit/SextLoadBridge.lean`).

## Where this sits in the stack (dependency direction, bottom → top)

1. **`EquivCore/<Op>.lean` (here)** — the `execute = bus_effect` core theorem,
   carrying promise hypotheses.
2. **`Compliance/Wrappers/<Op>.lean`** — imports `EquivCore.<Op>` and produces
   `ZiskFv.Compliance.equiv_<OP>` in the *channel-balance* form, discharging the
   promise hypotheses from the trust ledger.
3. **`Equivalence/<Op>.lean`** — a thin re-export *above* the wrapper: it imports
   `Compliance.Wrappers.<Op>` and is essentially
   `exact ZiskFv.Compliance.equiv_<OP> …`, restating the canonical channel-balance
   theorem `execute_instruction … = state_effect_via_channels …`.
4. The global theorem chains the `Equivalence/`/`Wrappers/` results via
   `OpEnvelope` and the `Compliance/Dispatch/` families.

So the *canonical channel-balance* per-opcode theorems live in
`ZiskFv/Equivalence/`; this directory (`EquivCore/`) holds the *core*
`execute = bus_effect` theorems those build on. (The two directories are one
letter apart and hold different theorems — a known naming hazard, see
`docs/refactor/05-inconsistencies-and-correctness.md` N1.)

## Subdirectories

- **`Bridge/`** — cross-AIR equivalence machinery shared across many opcodes:
  arith, binary, binary-add, binary-extension, mem, control-flow,
  sail-state-bridge, state-bridge.
- **`WriteValueProofs/`** — shared rd-value derivations factored across opcode
  families that share a derivation pattern: arith, binary-compare, binary-logic,
  binary-shift, jump+utype, mul/div/rem signed and unsigned, sail-bridge.
- **`Promises/`** — the per-shape promise bundles the core theorems take as
  hypotheses and the wrappers discharge.

To start auditing one opcode, read its `<Op>.lean` here (the core), the matching
`Compliance/Wrappers/<Op>.lean` (which discharges its promises), the
`Equivalence/<Op>.lean` re-export, and the relevant `ZiskCircuit/<Op>.lean` file
for the circuit side. The `<Op>` Sail-side bridge is in `SailSpec/<op>.lean`
(lowercase).
