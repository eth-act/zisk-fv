import ZiskFv.Compliance.Dispatch.Branch
import ZiskFv.Compliance.Dispatch.NoMemOrSimple
import ZiskFv.Compliance.Dispatch.RTYPE
import ZiskFv.Compliance.Dispatch.ITYPE
import ZiskFv.Compliance.Dispatch.Shift
import ZiskFv.Compliance.Dispatch.ADD_RTYPEW
import ZiskFv.Compliance.Dispatch.LDSD
import ZiskFv.Compliance.Dispatch.DIVU
import ZiskFv.Compliance.Dispatch.Misc
import ZiskFv.Compliance.Dispatch.Remaining
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.AeneasBridgeTrust

/-!
# Compliance.lean — unified channel-balance global theorem

This file aggregates the ten per-family dispatchers in
`Compliance/Dispatch/` into the global theorem
`zisk_riscv_compliant_program_bus`.

`OpEnvelope.exec_eq` is the conjunction of the ten per-family
conclusions. For any `OpEnvelope` arm, *exactly one* family's
`exec_eq_<family>` produces the real channel-balance statement; the
others return `True`. The conjunction is therefore exactly "this
arm's channel-balance statement holds". `zisk_riscv_compliant_program_bus`
proves the conjunction by invoking each dispatcher in turn.

## Coverage

All 63 RV64IM opcode arms are covered with a real (non-`True`)
channel-balance statement, partitioned across the ten dispatchers:

| Dispatcher (`Compliance/Dispatch/`) | Arms                                       |
|-------------------------------------|--------------------------------------------|
| `Branch`        | BEQ, BNE, BLT, BGE, BLTU, BGEU (6)                            |
| `NoMemOrSimple` | LUI, AUIPC, FENCE (3)                                        |
| `RTYPE`         | SUB, AND, OR, XOR, SLT, SLTU (6)                             |
| `ITYPE`         | ANDI, ORI, XORI, SLTI, SLTIU (5)                             |
| `Shift`         | SLL, SRL, SRA, SLLI, SRLI, SRAI (6)                          |
| `ADD_RTYPEW`    | ADD, ADDW, SUBW (3)                                          |
| `LDSD`          | LD, SD (2)                                                   |
| `DIVU`          | DIVU (1)                                                     |
| `Misc`          | LB, LH, LW, ADDI, ADDIW (5)                                  |
| `Remaining`     | the remaining 26 (loads/stores/W-shifts/Mul/Div/Rem/JAL/JALR)|

## Trust note

The global theorem explicitly assumes `env.aeneasBridgeTrust`, the visible
boundary for Aeneas-backed row-lowering facts that are still carried as
`OpEnvelope` fields while generated Aeneas Lean is not imported by the main
proof.

It also assumes `env.memoryTimelineConstructionEvidence`, the single visible
construction residual for load arms: the generated replay trace contains the
selected load row, and the load Sail state aligns with the selected replay
prefix. Non-load arms impose no memory-timeline obligation.

`zisk_riscv_compliant_program_bus` is the single public global theorem. It is
defect-aware while `trust/defects.md` contains open claim-weakening defects:
the `h_known_bugs` binder is orthogonal to the validity witnesses already
bundled in `OpEnvelope`. Validity says the current modeled constraints hold;
`h_known_bugs` says this envelope is not inside a ledgered defect region.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- Unified per-arm conclusion: conjunction of the ten family-
    specific `exec_eq_<family>` Props. Exactly one family fires
    non-trivially for any given arm; the others are definitionally `True`,
    so for any *concrete* arm 9 of the 10 family conjuncts collapse to `True`.

    NOTE (legibility wart, scheduled to be split out — see PLAN_ARCH_CLARIFICATION
    step S9): the first two conjuncts `aeneasBridgeTrust` and
    `memoryTimelineConstructionEvidence` are ALSO hypotheses of
    `zisk_riscv_compliant_program_bus`, discharged there by `exact h_bridge` /
    `exact h_memory_construction`. They are assumed, not proved; including them in
    the conclusion adds no information. The honest content is the 10 family
    conjuncts (the channel-balance equations); the trust residuals belong only in
    the hypothesis list. -/
def OpEnvelope.exec_eq (env : OpEnvelope state m r_main) : Prop :=
  env.aeneasBridgeTrust            -- echoed hypothesis (assumed, not proved); see S9
    ∧ env.memoryTimelineConstructionEvidence  -- echoed hypothesis (assumed); see S9
    ∧ env.exec_eq_branch
    ∧ env.exec_eq_nomem
    ∧ env.exec_eq_rtype_binary
    ∧ env.exec_eq_itype_binary
    ∧ env.exec_eq_shift
    ∧ env.exec_eq_add_rtypew
    ∧ env.exec_eq_ldsd
    ∧ env.exec_eq_divu
    ∧ env.exec_eq_misc
    ∧ env.exec_eq_remaining

/-- **Soundness of ZisK's RV64IM circuit against the Sail spec, per opcode**
    (the project's soundness half — public alias `ZiskFv.zisk_riscv_soundness`,
    see `ZiskFv/Top.lean`).

    For any `OpEnvelope` arm, the channel-balance form of the conclusion
    (`= state_effect_via_channels …`, defeq `(bus_effect …).2`) holds, given the
    three conditional assumptions below. None is discharged inside this Lean
    build; see `ZiskFv/Top.lean` for what covers each gap. In particular the
    `NoKnownDefect` carve-out is provably `False` on the 7 signed-M/Div defect
    opcodes, so real coverage is **54 of 63**. -/
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope state m r_main)
    -- assumed: concrete decoded Main-AIR column values (Aeneas decoder, not
    -- imported here; checked by the external extraction gates).
    (h_bridge : env.aeneasBridgeTrust)
    -- assumed: loads only — a generated mem-replay trace contains the read row,
    -- prefix-aligned (whole-execution replay induction is open).
    (h_memory_construction : env.memoryTimelineConstructionEvidence)
    -- claim-weakening: this envelope is outside every ledgered defect region;
    -- provably `False` on the 7 signed MUL*/DIV*/REM* defects → no claim there.
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_bridge
  · exact h_memory_construction
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift env
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env h_memory_construction
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc env h_memory_construction
  · exact zisk_riscv_compliant_program_bus_remaining env h_memory_construction h_known_bugs

end ZiskFv.Compliance
