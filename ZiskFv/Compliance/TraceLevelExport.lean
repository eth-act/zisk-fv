import ZiskFv.Compliance.TraceLevelExport.Base
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl
import ZiskFv.Compliance.TraceLevelExport.EnvOf
import ZiskFv.Compliance.TraceLevelExport.StepStrongAluArith
import ZiskFv.Compliance.TraceLevelExport.StepStrongControlStore
import ZiskFv.Compliance.TraceLevelExport.StepStrongLoadMext
import ZiskFv.Compliance.TraceLevelExport.StepStrongSignedM
import ZiskFv.Compliance.TraceLevelExport.Dispatcher
import ZiskFv.Compliance.TraceLevelExport.BootSegmentMemorySeed

/-!
# TraceLevelExport.lean — P5 trace-level export (channel-balance form)

This is the achievable closure of #61.  It exports the per-opcode
`construction_<op>_sound` theorems to a single trace-level statement
(`root_soundness`, in `ZiskFv/Soundness.lean`) in the channel-balance form:
given an accepted full-ensemble trace and a program binding, with each row's
residual split three ways — `ziskStep i : ZiskStep` (which op decoded + its
`Claim_<op>`), `rowDecodes i : RowDecode` (the circuit-checkable `Decode_<op>`),
`inputsAgree i : InputsAgree` (the cross-world `Inputs_<op>`) — plus the
trace-local per-row defect-exclusion obligation `h_known_bugs`, EVERY row satisfies the
canonical per-step channel-balance conclusion (`= state_effect_via_channels …`)
— the SAME conclusion the OLD global theorem `zisk_riscv_compliant_program_bus`
produces — with NO caller-supplied `OpEnvelope`.  The envelope for each row is
constructed/lifted INSIDE, per row, by `stepSound_of_evidence` dispatching the
reassembled `RowData_<op>` to the matching `stepStrong_<op>`.

> The earlier, weaker `bus_effect`-form export (`RowConstructionData` /
> `StepCompliance` / `stepCompliance_of_rowData` /
> `zisk_compliant_of_accepted_trace`) has been REMOVED as redundant: the
> channel-balance export below is defeq-stronger (it implies the `bus_effect`
> form via `state_effect_via_channels_eq_bus_effect_2`) and nothing depended on
> the weaker form.

## The per-row split (`ZiskStep` / `RowDecode` / `InputsAgree`)

`ZiskStep trace i` is a sum type — one arm per RV64IM opcode — carrying that op's
`Claim_<op>` (decoded operand / destination indices + committed bus row).
`RowDecode`/`InputsAgree` then compute the matching `Decode_<op>` / `Inputs_<op>`
residual.  Together (`RowData_<op>`, reassembled by `toRowData_<op>`) they package
EXACTLY each construction's genuinely-irreducible residual binders (decode pins,
Sail reads, operand/lane bridges, PC-provenance/next-row pins; for loads also
`MemoryTimelineEvidence` + the Mem-AIR provider linkage).  They do NOT package
the bucket-(a) op-bus provider-match
evidence: that is derived INSIDE each construction from `trace.channels_balanced`
(via the `exists_*_provider_row_matches_*` Layer-A lemmas).

## Coverage (stated explicitly — NOT hidden)

The strengthened export covers **all 63 RV64IM archetypes**.  Three sound
routes are used, all yielding the identical channel-balance proposition the
global theorem produces:

1. **Env-constructed route (22 op-bus ALU arms)** — `SUB AND OR XOR SLT SLTU`,
   `ANDI ORI XORI SLTI SLTIU`, `SLL SRL SRA SLLI SRLI SRAI`, `ADD ADDI`,
   `SUBW ADDW ADDIW`.  The matching `OpEnvelope.<op>` arm is **constructed from
   the accepted trace** per row (re-running each construction's
   `exists_*_provider_row_matches_*` + input-packing derivations) and fed to
   `zisk_riscv_compliant_program_bus`.  Its three hypotheses are discharged in
   place: `aeneasBridgeTrust` from the derived row-binding facts,
   `memoryTimelineConstructionEvidence` trivially (non-load arms), and
   `NoKnownDefect` assembled locally via `noKnownDefect_of_shapes` (the three
   defect shapes are vacuous for a non-defect constructor — `False` / `False` /
   `True` — so the threaded `h_known_bugs` obligation for these arms is `True`).

2. **Direct-lift route (27 control-flow + U-type + store + load + M-ext-unsigned
   arms)** — `BEQ BNE BLT BGE BLTU BGEU`, `LUI AUIPC`, `JAL JALR`,
   `SB SH SW SD`, `LB LH LW LD LBU LHU LWU`, `MULW MULHU DIVU DIVUW REMU REMUW`.
   Each `construction_<op>_sound` already proves the `bus_effect`-form per-step
   conclusion over the real trace row, and `state_effect_via_channels` is
   `@[reducible]`-defeq to `bus_effect.2`.  So
   `rw [state_effect_via_channels_eq_bus_effect_2]` + the construction theorem
   yields the same channel-balance proposition the global theorem produces.  The
   6 M-ext-unsigned arms lift the FAITHFUL loose-bound (`<983041`) construction,
   NEVER the canonical equiv's tight (`<131072`) carry bound, so they are
   non-vacuous and sound.

3. **Env-constructed defect-narrowed route (7 signed-M arms + FENCE)** —
   `MUL MULH MULHSU DIV REM DIVW REMW` and `FENCE`.  Each CONSTRUCTS its
   `OpEnvelope.<op>` (= `<op>EnvOf`) from the trace row and assembles
   `NoKnownDefect (<op>EnvOf …)` of that SPECIFIC env via `noKnownDefect_of_shapes`,
   feeding its threaded row-data forge-negation into the one matching slot (NOT a
   selector-∀, NOT a contradictory `False`-binder).  The signed-M defect predicates
   are the EXACT witness-conditional forge shapes — MUL/MULH/MULHSU exclude only
   the np-forge `np=0 ∧ na⊕nb=1` (`SignedMulForge`, defeq `MaliciousSignedMulWitnessShape`);
   DIV/REM/DIVW/REMW exclude only the `|r|=|d|` `LT_ABS_NP` false positive
   (`DivRemForge` / `DivRemForgeW`, defeq `ArithDivDynamicWitnessShape`,
   codygunton/zisk#5).  The row-data bridge lemmas below still show the
   instantiated step evidence is not contradictory: for the concrete arith
   witness row carried by `RowData_<op>`, the matcher-instantiated predicate is
   exactly the `NoKnownDefect` fact needed by the corresponding `OpEnvelope`.
   The exported defect gate (`RowOutsideDefectRegion`) is stronger than that
   instantiated fact: it is now trace-local and universally ranges over arith
   witness rows whose operation-bus entry matches the accepted Main row.  This
   universal is satisfiable for honest traces because an operation-bus match pins
   the result lanes as well as opcode/operands; a forged witness computing a
   different result cannot match the honest Main row.  A forge-shaped witness
   that happened to match the honest result is conservatively excluded too.  For
   DIV/REM, divisor values are reconstructed from witness chunks rather than
   from `InputsAgree` or Sail operands.  FENCE remains row-local through the
   honest pins (`fm=0, rs1=x0, rd=x0`), and MULH/MULHSU sign facts are derived
   from the indexed Arith range-table evidence exposed by #169.

## Threaded defect-exclusion hypothesis (`h_known_bugs`)

The `h_known_bugs` premise is the per-step defect-exclusion obligation
(`RowOutsideDefectRegion`), stated over the accepted ZisK trace row (no
`OpEnvelope`, `SailTrace`, or `InputsAgree` detour).  It is threaded — via
`stepSound_of_evidence` — to each
`stepStrong_<op>`.  It takes two shapes across the 63 arms, all SATISFIABLE for
honest traces with honest Main-row results (so this export is NOT vacuous):
  * **Non-defect arms** (op-bus ALU + M-ext-unsigned + control-flow / U-type /
    store / load): no defect obligation — the arm is `True`.  Each `stepStrong_<op>`
    builds `NoKnownDefect` of its own env locally via `noKnownDefect_of_shapes`
    (the three defect shapes are vacuous for a non-defect constructor).
  * **8 defect-capable arms** (MUL/MULH/MULHSU/DIV/REM/DIVW/REMW + FENCE): the
    trace-local matcher requires the forge-negation (`¬ SignedMulForge` /
    `¬ DivRemForge` / `¬ DivRemForgeW`) for every arith witness row whose
    operation-bus row matches the accepted Main row, or FENCE-known-good
    (`FenceKnownGood`) directly from the decoded Main row.  This universal is a
    strict trace-side obligation, not merely the old caller-supplied row fact:
    `matches_entry` includes the result lanes, so an honest Main row is not
    matched by a forge witness that computes a different result.  The dispatcher
    later instantiates the universal with the arith row evidence already present
    in `Inputs_<op>`; each instantiated predicate is definitionally equal to the
    corresponding `<op>EnvOf` `OpEnvelope` defect shape via the bridge lemmas in
    `EnvOf`, proving the strong step still receives the exact fact it expects.

## Non-vacuity

The hypotheses are SATISFIABLE for a real trace.  `trace : AcceptedZiskTrace` is the
committed full-ensemble witness; each `rowData i` carries TRUE facts of the real
row `mainOfTable trace.program trace.mainTable` at index `i` (decode pins, lane
bridges, Sail reads of `binding i`), and `execRow` is a genuine
top-level ∀-binder inside each arm (the real execution-bus row).  No arm contains
a contradictory hypothesis pair; no `False.elim` is used.

## Residual roll-up

The irreducible residuals carried per arm bottom out in the existing project
residuals — none introduces a new `ZiskFv.*` axiom:
* loads `h_memory_timeline` and sub-doubleword store
  `StoreRmwMemoryCoherenceEvidence` → **#76** (memory timeline), plus the
  Mem-AIR `h_mem_*` provider linkage on loads;
* `h_nextPC_matches` (conditional next-PC) → **#100 — now DISCHARGED** for ALL 63
  opcodes: derived from the `AcceptedZiskTrace.transitions_hold` PC-handshake
  certificate (`Compliance/MainTransition.lean`, `Compliance/Pilot/*NextPC.lean`),
  no longer a residual. See `trust/trusted-base.md` ("Accepted-Trace Certificates")
  for the trust-surface accounting + the within-segment (`i+1 < length`) boundary;
* the signed loads (`lb`/`lh`/`lw`) carry `h_static` + `h_match` — the
  sign-extension `BinaryExtension` op-bus lookup linkage that
  `construction_{lb,lh,lw}_sound` themselves take as residual binders.

This file introduces **0 new `ZiskFv.*` axioms**: its trust closure is the union
of the constructions' closures.
-/
