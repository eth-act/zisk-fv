# `ZiskFv/Equivalence/`

Per-opcode canonical equivalence theorems. The 63 top-level files
(`Add.lean`, `Addi.lean`, …, `Xori.lean`, one per RV64IM opcode)
each contain the **canonical** `equiv_<OP>` theorem:

```lean
equiv_<OP> :
  ∀ (state : SailState) (exec_row : ExecRow) (mem_row : MemRow)
    <promise hypotheses in safe trust classes>,
    LeanRV64D.Functions.execute (.<shape> …) state
      = (bus_effect exec_row mem_row state).2
```

Both sides live in Sail's state space. The LHS is the Sail RV64
spec's monadic `execute`; the RHS is `SailSpec.BusEffect.bus_effect`
applied to circuit-side rows. The theorem's parameters are restricted
to a fixed allowlist of safe trust classes (`CIRCUIT-CONSTRAINT`,
`LANE-MATCH`, `RANGE`, `TRANSPILE-BRIDGE`, `TRANSPILE-PIN`); the
forbidden shapes are listed in `trust/forbidden-param-shapes.txt` /
`trust/forbidden-types.txt` and enforced uniformly by the trust gate
across all 63 opcodes (no carve-outs — the 7 load opcodes were closed
by deriving their cross-entry rd-value byte equations from circuit
witnesses in `ZiskCircuit/LoadDerivation.lean` and
`ZiskCircuit/SextLoadBridge.lean`).

Each canonical theorem is wrapped by a `equiv_<OP>_from_trust`
theorem in `ZiskFv/Compliance/FromTrust/<Op>.lean`, which discharges
the promise hypotheses from the trust ledger; the global theorem
chains those wrappers via `OpEnvelope`.

## Subdirectories

- **`Bridge/`** — cross-AIR equivalence machinery shared across many
  opcodes: arith, binary, binary-add, binary-extension, mem,
  control-flow, sail-state-bridge, state-bridge.
- **`WriteValueProofs/`** — shared rd-value derivations factored
  across opcode families that share a derivation pattern: arith,
  binary-compare, binary-logic, binary-shift, jump+utype, mul/div/rem
  signed and unsigned, sail-bridge.

To start auditing one opcode, read its `<Op>.lean` here, the matching
`FromTrust/<Op>.lean` in `Compliance/`, and the relevant `ZiskCircuit/<Op>.lean`
file for the circuit side. The `<Op>` Sail-side bridge is in
`SailSpec/<op>.lean` (lowercase).
