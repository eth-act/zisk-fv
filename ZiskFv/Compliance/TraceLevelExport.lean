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

/-!
# TraceLevelExport.lean — P5 trace-level export (channel-balance form)

This is the achievable closure of #61.  It exports the per-opcode
`construction_<op>_sound` theorems to a single trace-level statement in the
channel-balance form: given an accepted full-ensemble trace, a program binding,
and a per-row CLASSIFICATION (`rowData : ∀ i, StrongRowConstructionData …`), plus
the per-row defect-exclusion obligation `h_known_bugs`, EVERY row of the trace
satisfies the canonical per-step channel-balance conclusion
(`= state_effect_via_channels …`) — the SAME conclusion the OLD global theorem
`zisk_riscv_compliant_program_bus` produces — with NO caller-supplied
`OpEnvelope`.  The envelope for each row is constructed/lifted INSIDE, per row,
from `rowData i` to the matching `stepStrong_<op>`.

> The earlier, weaker `bus_effect`-form export (`RowConstructionData` /
> `StepCompliance` / `stepCompliance_of_rowData` /
> `zisk_compliant_of_accepted_trace`) has been REMOVED as redundant: the
> channel-balance export below is defeq-stronger (it implies the `bus_effect`
> form via `state_effect_via_channels_eq_bus_effect_2`) and nothing depended on
> the weaker form.

## What `StrongRowConstructionData` is (and is NOT)

`StrongRowConstructionData trace binding i` is a sum type — one arm per RV64IM
opcode.  Each arm carries a single `RowData_<op>` payload that packages EXACTLY
that construction's genuinely-irreducible residual binders (decode pins, Sail
reads, operand/lane bridges, the `execRow` ∀-binder + exec facts,
`h_nextPC_matches`; for loads also `MemoryTimelineEvidence` + the Mem-AIR
provider linkage).  It does NOT package the bucket-(a) op-bus provider-match
evidence: that is derived INSIDE each construction from `trace.channels_balanced` (via the
`exists_*_provider_row_matches_*` Layer-A lemmas).

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
   `NoKnownDefect` from the threaded `h_known_bugs` (non-defect ops — TRUE, not a
   contradictory hypothesis).

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
   `OpEnvelope.<op>` (= `<op>EnvOf`) from the trace row and asks for the GENUINE
   `NoKnownDefect (<op>EnvOf …)` of that SPECIFIC env (NOT the `EnvNoKnownDefectFor`
   selector-∀, NOT a contradictory `False`-binder).  The signed-M defect predicates
   were NARROWED from the old opcode-wide `| .mul .. => True` form to the EXACT
   witness-conditional forge shapes — MUL/MULH/MULHSU exclude only the np-forge
   `np=0 ∧ na⊕nb=1` (`MaliciousSignedMulWitnessShape`); DIV/REM/DIVW/REMW exclude only
   the `|r|=|d|` `LT_ABS_NP` false positive (`ArithDivDynamicWitnessShape`,
   codygunton/zisk#5).  Honest rows are NEVER excluded, so every arm is SATISFIABLE
   for a real honest signed-M row (anti-vacuity witnesses
   `honest_<op>_witness_not_forge`); FENCE is likewise satisfiable for an honest FENCE
   row (`fm=0, rs1=x0, rd=x0`).  A documented sign-range residual `na = MSB` is carried
   per signed-M row (the real circuit enforces it via the arith.pil indexed range
   lookup; the FV model collapsed it to FULL — dischargeable, issue #114).

## Threaded defect-exclusion hypothesis (`h_known_bugs`)

The `h_known_bugs` premise is the per-row defect-exclusion obligation
(`StepNoKnownDefect`).  It is threaded — via `stepComplianceStrong_of_rowData` —
to each OpEnvelope-route `stepStrong_<op>`, which feeds it to the old global
theorem in place of an internally-proved `NoKnownDefect`.  It takes three shapes
across the 63 arms, all SATISFIABLE for an honest row (so this export is NOT
vacuous):
  * **Non-defect arms** (op-bus ALU + M-ext-unsigned + control-flow / U-type /
    store / load): `EnvNoKnownDefectFor` on the arm's non-defect constructor,
    TRIVIALLY true — see `envNoKnownDefectFor_of_nondefect`.
  * **7 signed-M arms** (MUL/MULH/MULHSU/DIV/REM/DIVW/REMW): the GENUINE
    `NoKnownDefect (<op>EnvOf …)` of the SPECIFIC env, true for any honest row
    because the defect predicates were narrowed to the exact forge shapes (the
    np-forge / `|r|=|d|` witnesses) that an honest row never matches.
  * **FENCE**: the GENUINE `NoKnownDefect (fenceEnvOf …)` of the honest FENCE env,
    true for an honest FENCE row (`fm=0, rs1=x0, rd=x0`).

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
* loads/stores `h_memory_timeline` / RMW-preservation reads → **#76** (memory
  timeline), plus the Mem-AIR `h_mem_*` provider linkage;
* branches + JAL/JALR `h_nextPC_matches` (conditional next-PC) → **#100**
  (cross-row control flow);
* the signed loads (`lb`/`lh`/`lw`) carry `h_static` + `h_match` — the
  sign-extension `BinaryExtension` op-bus lookup linkage that
  `construction_{lb,lh,lw}_sound` themselves take as residual binders.

This file introduces **0 new `ZiskFv.*` axioms**: its trust closure is the union
of the constructions' closures.
-/
