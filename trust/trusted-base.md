# Trusted Base

This is the narrative source of truth for zisk-fv's current trust boundary.
The generated machine ledgers live under [`generated/`](generated/).

## Claim

The intended soundness claim is:

> Assuming the Sail-to-Lean extraction and ZisK RV64IM circuit-to-Lean
> extraction are trusted, every state transition accepted by the modeled ZisK
> RV64IM circuits is a valid RISC-V state transition.

The global Lean theorem is:

```text
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

This theorem is a conditional global compliance theorem over an already
constructed `OpEnvelope`. Its explicit
`ZiskFv.Compliance.OpEnvelope.completenessBurden` and
`ZiskFv.Compliance.OpEnvelope.AcceptedFullMemoryBusRowsTraceAtEnvelope` premises mark
the current caller-side witness burden: row specs, table/provider evidence,
route facts, and, for load envelopes only, accepted chronological raw
memory-bus rows plus selected read-row cursor data are supplied rather than
derived by a global accepted-trace completeness theorem.

Current generated counts:

| Surface                                                                | Count | Ledger                                                                                       |
| ---                                                                    | ---:  | ---                                                                                          |
| Source Lean trust declarations                                         | 0     | [`generated/baseline-axioms.txt`](generated/baseline-axioms.txt)                             |
| Transitive project-axiom closure of `zisk_riscv_compliant_program_bus` | 0     | [`generated/baseline-zisk-riscv-compliant.txt`](generated/baseline-zisk-riscv-compliant.txt) |

The semantic trust gate checks the global closure against the source ledger
modulo [`tolerated-completeness-axioms.txt`](tolerated-completeness-axioms.txt).

The extraction assumptions are part of the project premise but outside the
Lean axiom ledger:

- Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
- ZisK RV64IM circuit-to-Lean extraction from flake-pinned ZisK/PIL inputs.

## Current Classes

## Retired Row-Shape Bridge

The former RV64-to-ZisK hand-written row-shape axiom surface has been removed from the
active Lean trust ledger. The live opcode literals, lane helpers,
register-pointer decoding helper, and row/state helper structures live in
`ZiskFv/RowShape/Contract.lean`.

Canonical per-opcode theorem closures no longer mention any retired
row-shape bridge names. The route obligations that used to be hidden behind
that contract are now explicit caller/envelope facts or are derived from row
provenance and provider rows: static mode/control pins from provenance,
runtime source/data lanes from caller facts, and jump/PC facts from explicit
route obligations.

## Retired Memory State Load Bridge

The former source axiom tying arbitrary Sail load state directly to a Mem row
has been removed.
Load correctness now consumes an explicit
`ZiskFv.ZiskCircuit.MemTrace.MemoryTraceAgreement` premise threaded through
the load trace context, and `MemModel.lean` only projects the resulting byte
facts. The global theorem's memory premise is now load-scoped: non-load
envelopes discharge it as `Unit`, while load envelopes require accepted
chronological raw memory-bus rows, a split selecting the concrete read row in
those rows, and Sail/replay agreement at that cursor derived internally from
the projected bus-event replay object.

## Platform Profile

There are no project axioms for the current platform profile. PMP, PMA,
CLINT, and Zicfilp branches are discharged by ordinary Lean theorems in
`ZiskFv/SailSpec/Auxiliaries.lean`, using the global RISC-V profile
hypotheses carried by opcode proofs: machine mode, PMP disabled by the Sail
configuration, one ZisK physical-memory PMA region, aligned accesses, no HTIF,
C disabled in `misa`, and `mseccfg` readability.

These facts still define the verification target, but they are no longer in
the trusted axiom ledger.

## Clean Completeness

The former Clean component completeness placeholders have been retired. The
old dedicated completeness-axiom module no longer exists, and the six former
declarations are no longer source-ledger entries.

Clean components still expose `GeneralFormalCircuit.completeness`, but those
fields are now ordinary Lean proofs conditional on explicit prover-side row
facts. They do not add trust declarations and they still do not state
per-opcode output equality.

## Global Completeness Boundary

The public theorem does not yet prove that an accepted full trace constructs
the required `OpEnvelope`. The explicit `OpEnvelope.completenessBurden`
premise is an audit marker for that missing global witness-construction layer;
there is no default theorem discharging it from an arbitrary envelope. Load
arms expose their memory burden separately as
`OpEnvelope.AcceptedFullMemoryBusRowsTraceAtEnvelope`: non-load envelopes
discharge it as `Unit`; load envelopes require chronological raw memory-bus
rows, a replay-sound accepted trace for the rows' read/write projection, a
selected raw-row cursor pinned to the envelope's concrete read row, initial
memory agreement, and Sail state-at-cursor equality. The selected full-memory
cursor is derived internally by projecting rows to memory-bus events and
replaying the prior bus events. The remaining global gap is deriving those raw
rows, row-projected replay soundness, and selected cursors from accepted AIR
trace data.

## ArithTable And DIV/REM Audit Conclusions

The opcode-shaped ArithTable axiom family has been retired from the active
trust shape. `generated/baseline-arith-table-op-axioms.txt` remains as a
guardrail so new `arith_table_op_*` trust facts cannot be added silently.

Active conclusions:

- True finite-table projections are now derived from row-native
  `ArithTableSpec` witnesses rather than trusted as opcode-shaped facts.
- False static claims such as unconditional W-mode `sext = 0` or static
  `np_xor` cannot be reintroduced; they must be replaced by dynamic proofs or
  explicit defect gates.
- `DIVU`, `REMU`, `DIVUW`, and `REMUW` are retired from the broad dynamic
  witness defect by deriving unsigned range, W high-chunk, nonzero-divisor,
  quotient high-zero, and remainder-bound facts from Clean ArithDiv/Binary
  evidence plus the unsigned Euclidean identity.
- Signed `DIV`, `DIVW`, `REM`, and `REMW` remain defect-gated because the
  signed remainder-bound route exposes an `LT_ABS_NP` byte-chain mismatch.
- Signed `MUL`, `MULH`, and `MULHSU` remain defect-gated for signed witness
  soundness under malicious witness construction.

The active defect boundaries and retirement criteria are in
[`defects.md`](defects.md).

## Active Caller Burden

The generated anti-laundering ledgers are:

- [`generated/baseline-hypothesis-count.txt`](generated/baseline-hypothesis-count.txt)
- [`generated/baseline-caller-burden.txt`](generated/baseline-caller-burden.txt)
- [`generated/baseline-wrapper-caller-burden.txt`](generated/baseline-wrapper-caller-burden.txt)
- [`generated/baseline-equiv-axiom-deps.txt`](generated/baseline-equiv-axiom-deps.txt)

Promise discharge must visibly reduce caller burden, unless a documented
structural-unpacking exception explains why added structural witnesses collapse
into shared global-theorem evidence.

## Not In This Ledger

The trust ledger does not enumerate the Lean kernel, mathlib,
LeanZKCircuit, the Sail-to-Lean compiler output, or flake-pinned upstream
inputs. Their audit surface is the Lake/Nix configuration and `flake.lock`,
not `generated/baseline-axioms.txt`.
