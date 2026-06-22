import ZiskFv.Compliance
import ZiskFv.Completeness.Rv64im

/-!
# `ZiskFv.Top` — the two public results (start here)

This is the front door to zisk-fv. The project proves **two** results about
ZisK's RV64IM zkVM circuit versus the Sail RISC-V spec. They are honest *halves*,
not one theorem: soundness quantifies over per-opcode circuit witnesses;
completeness over an abstract decoder interface. **There is no Lean dependency
edge between them** (`ZiskFv.Compliance` does not import `ZiskFv.Completeness`),
so they are deliberately kept as two named siblings rather than fused — a single
combined "correctness" theorem would have to manufacture a connection that does
not exist.

Both results are **conditional**: each takes clearly-named hypotheses that this
Lean build *assumes* rather than proves. None of the assumptions is vacuous (the
antecedents are satisfiable), but the force of each theorem is exactly as strong
as those assumptions. The tables below say, per assumption, what it means and
what — if anything — discharges it.

## 1. Soundness — `zisk_riscv_soundness`

For one RV64IM opcode's circuit-witness bundle (`Compliance.OpEnvelope`, one arm
per opcode), the ZisK circuit's post-state equals the Sail spec's post-state —
*given* three assumptions:

| assumption (hypothesis) | meaning | discharged? |
|---|---|---|
| `aeneasBridgeTrust` | concrete decoded Main-AIR column values for the row (e.g. BEQ: `is_external_op = 1 ∧ op = OP_EQ ∧ m32 = 0 ∧ set_pc = 0 ∧ store_pc = 0 ∧ jmp_offset2 = 4`) | **NO** — supplied by the generated Aeneas decoder, which is not imported into this Lean build (4.28-vs-4.30 toolchain split). Checked *outside* Lean by the Aeneas extraction-fidelity gates (`check-aeneas-*`). A proved reduction (`*OfExtractedShape` + `RowProvenance`) shows it follows from a `MainRowProvenance`, but that reduction is not on this theorem's path. |
| `memoryTimelineConstructionEvidence` | loads only (`True` for the other 56 arms): a generated memory-replay trace contains the read row, with the load's Sail state aligned to the replay prefix | **NO** — the whole-execution replay induction is open. A proved, axiom-clean reduction (`loadMemoryTimelineEvidence_of_constructionEvidence`) turns it into the timeline evidence the load cores need; the existential itself is assumed. |
| `NoKnownDefect` | this envelope is outside every ledgered defect region | claim-**WEAKENING**, not discharge. On signed `MUL`/`MULH`/`MULHSU` and signed `DIV`/`DIVW`/`REM`/`REMW` it is provably `False`, so soundness makes **no claim** there. Real coverage is **54 of 63 opcodes**. See `trust/defects.md` (one defect has an end-to-end Docker repro, codygunton/zisk#5). |

The conclusion is the per-arm channel-balance equation `Sail.execute … = (bus_effect …).2`.

## 2. Completeness — `zisk_riscv_completeness`

For every Sail-executable RV64IM word outside the known FENCE decode gap, the
ZisK decode→lower→materialize→opcode path covers it and supplies the row-local
input — **relative to a caller-supplied `Completeness.Rv.Interface`** whose 8
fields are uninterpreted predicates that are **never instantiated in this tree**.
So this standalone theorem is a *typed contract*, not a proof of ZisK
completeness; the real discharge (build a concrete interface from the production
decoder + prove the 6 hypotheses) lives in the external Aeneas harness.

Completeness is really **three disconnected fragments**, none wired to each other
or to soundness:
  * **real, partial:** the Clean per-AIR `completeness` obligations in
    `ZiskFv/AirsClean/*/Circuit.lean` (125 genuine proofs) — honest inputs yield
    an accepting row; scope = row-local (Arith unsigned-only, Binary via the
    table-index route).
  * **this contract:** `zisk_riscv_completeness` (decode coverage, uninstantiated).
  * **orphaned:** `ZiskFv/Completeness/Rv64im/SailDecode.lean` (188 real Sail
    theorems; the would-be discharge of the `sailExecutable` hypothesis, not yet
    wired in).

## Navigating down (soundness)

`zisk_riscv_soundness` → 10 per-family dispatchers (`Compliance/Dispatch/*`,
pure routing) → 63 canonical `equiv_<OP>` (`Equivalence/<Op>`) → the real
Sail↔circuit proofs (`EquivCore/<Op>`). Stop at the dispatchers unless debugging
a specific family.
-/

namespace ZiskFv

/-- **Soundness** of ZisK's RV64IM circuit against the Sail spec, per opcode.

See the module docstring (`ZiskFv.Top`) for the meaning + discharge status of
each assumption and the 54/63 defect scope. This is a *conditional* theorem: it
assumes `aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`, and
`NoKnownDefect`, none of which are discharged inside this Lean build. -/
@[reducible] def zisk_riscv_soundness :=
  @ZiskFv.Compliance.zisk_riscv_compliant_program_bus

/-- **Completeness** (decode coverage) of ZisK's RV64IM circuit, as a typed
contract over an (uninstantiated) decoder `Rv.Interface`.

See the module docstring (`ZiskFv.Top`): this is a contract, not a standalone
proof of completeness — the 6 hypotheses are discharged in the external Aeneas
harness, and the real per-AIR constructibility lives separately in
`AirsClean/*/Circuit.lean`. -/
@[reducible] def zisk_riscv_completeness :=
  @ZiskFv.Completeness.Rv64im.rv64im_completeness

end ZiskFv
