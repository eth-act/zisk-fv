# Defect ledger

This ledger tracks known defects that affect the formal verification claim.
It is paired with the design in
[`defect-ledger-design.md`](defect-ledger-design.md).

The ledger is not the trust ledger. Do not add axioms to cover these rows.
Each open defect must either block the unqualified theorem or appear as an
explicit exception predicate in the theorem statement.

## Open / mitigated defects

### ZISK-DEFECT-ARITH-TABLE-TRUST-SHAPE

| Field | Value |
|-------|-------|
| `kind` | `trust-shape` |
| `status` | `retired-in-lean` |
| `affected` | None in `Defects.UsesOpcodeSpecificArithTableAxiom`. The false opcode-shaped declarations for `MUL`, `MULH`, `MULHSU`, `MULW`, unsigned-W DIV/REM, and signed-W DIV/REM have been deleted from `ZiskFv.Airs.Arith.Ranges`. |
| `condition` | Opcode-specific ArithTable conclusions are trusted directly instead of proved from shared table membership plus finite projections. |
| `evidence` | See [`trusted-base.md`](trusted-base.md) "Current correction: ArithTable trust shape" and [`clean-integration-plan.md`](clean-integration-plan.md) C3/C4. |
| `claim impact` | This trust-shape defect no longer blocks the defect-aware theorem. The ordinary zero-sorry invariant is restored for this cleanup; the remaining signed-MUL limitation is tracked separately as `ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`. |
| `retirement condition` | Met for the defect predicate: every C3/C4 constructor is removed from `Defects.UsesOpcodeSpecificArithTableAxiom`; proof closures for repaired arms consume shared lookup/permutation membership plus proved finite-table projections, not false opcode-shaped ArithTable facts. |

### ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS

| Field | Value |
|-------|-------|
| `kind` | `circuit-soundness` |
| `status` | `open` |
| `affected` | Arith signed multiplication witness relation for `MUL`, `MULH`, and `MULHSU` under malicious witness construction. |
| `condition` | A malicious witness can select signed-multiply table rows where the product-sign witness is not `na XOR nb`; the carry-chain then describes an absolute/product-shape relation rather than the intended two's-complement signed result. |
| `evidence` | Clean finite-table counterexamples show `MULH` and `MULHSU` rows with `na = 1`, opposite unsigned/nonnegative operand sign, and `np = 0`. The range-table shape admits positive `d3` for that branch, so the signed high-half proof cannot recover Sail semantics from the old `np_xor` shortcut. Executable repro: a separate ZisK worktree at commit `0142ab5d7` was branched as `repro/mulh-mulhsu-malicious-witness-demo` and run on 2026-05-22 with Docker image `zisk-arith-mul-repro:mulh-demo`. Stock ZisK accepted and verified malicious proofs for all three shapes: `MUL(-1,1)=1`, `MULH(-1,1)=0`, and `MULHSU(-1,1)=0`. The bad row family uses `na = 1`, `nb = 0`, `np = 0`, `c = 1`, `d = 0`, carries `[-1,-1,-1,-1,0,0,0]`; for high-half cases this contradicts Sail, which returns `0xffffffffffffffff`, not `0`. |
| `claim impact` | This is not a normal opcode input exception. The global theorem now explicitly takes `h_known_bugs : Defects.NoKnownDefect env`, and the affected `MUL`, `MULH`, and `MULHSU` wrapper/canonical theorems carry a visible `h_no_signed_mul_witness_defect : False` binder. This is claim weakening, not promise discharge. |
| `retirement condition` | Upstream constraints reject the malicious witness, or Lean proves the affected witness shape impossible from the real constraints and shared table/lookup boundaries. The repro must fail in verifier/prover mode after the fix. |

### ZISK-DEFECT-FENCE-INCOMPLETE

| Field | Value |
|-------|-------|
| `kind` | `implementation-semantic` |
| `status` | `open-needs-triage` |
| `affected` | RV64I `FENCE`; `ZiskFv/SailSpec/fence.lean`; `ZiskFv/EquivCore/Fence.lean`; `ZiskFv/Compliance/Wrappers/Fence.lean`. |
| `condition` | ZisK appears to implement FENCE as `nop()` / `PC += 4`; the exact unsupported behavior relative to the intended RV64IM platform model still needs to be pinned down. |
| `evidence` | `ZiskFv/SailSpec/fence.lean` cites the transpiler lowering and proves the no-op Sail subset under Machine mode and the Sail concurrency stub. User report: ZisK does not currently support FENCE completely. |
| `claim impact` | FENCE should stay in opcode coverage, but the theorem should be named or hypothesized as compliance for the `FenceNopEquivalent` subset until the full support boundary is explicit. |
| `retirement condition` | Either prove the current no-op model is the full in-scope RV64IM platform behavior, or update ZisK and the proof so FENCE compliance no longer needs a defect predicate. |

## Retired defects

None yet.
