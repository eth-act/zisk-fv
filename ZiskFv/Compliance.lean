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

No new axioms — the closure is exactly the union of the 63 wrappers'
closures plus the trivial `state_effect_via_channels_eq_bus_effect_2`
bridge. The V2 trust gate enforces this.

`zisk_riscv_compliant_program_bus` is the single public global theorem. It is
conditional on `OpEnvelope.completenessBurden`, which marks that the theorem
starts from an already-constructed envelope rather than proving accepted-trace
completeness. Load-memory replay evidence is exposed separately as an
`OpEnvelope.AcceptedMemoryTraceConstruction`, from which the theorem derives
`OpEnvelope.acceptedMemoryTraceContext`. It is also defect-aware while
`trust/defects.md` contains open claim-weakening defects: the `h_known_bugs`
binder is orthogonal to the validity witnesses already bundled in
`OpEnvelope`. Validity says the current modeled constraints hold;
`h_known_bugs` says this envelope is not inside a ledgered defect region.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- Unified per-arm conclusion: conjunction of the ten family-
    specific `exec_eq_<family>` Props. Exactly one family fires
    non-trivially for any given arm; the others are `True`. -/
def OpEnvelope.exec_eq (env : OpEnvelope state m r_main) : Prop :=
  env.exec_eq_branch
    ∧ env.exec_eq_nomem
    ∧ env.exec_eq_rtype_binary
    ∧ env.exec_eq_itype_binary
    ∧ env.exec_eq_shift
    ∧ env.exec_eq_add_rtypew
    ∧ env.exec_eq_ldsd
    ∧ env.exec_eq_divu
    ∧ env.exec_eq_misc
    ∧ env.exec_eq_remaining

/-- **Known-defect-aware channel-balance global theorem.**

    For any `OpEnvelope` arm, the channel-balance form of the
    conclusion (`= state_effect_via_channels …`) holds outside the
    defect regions recorded by `Defects.NoKnownDefect`. -/
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (h_mem_trace : env.AcceptedMemoryTraceConstruction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  obtain ⟨_h_row_burden, _h_table_provider_burden, _h_route_burden⟩ :=
    h_burden
  have h_mem_context : env.acceptedMemoryTraceContext :=
    env.acceptedMemoryTraceContext_of_construction h_mem_trace
  have h_accepted_memory_burden : env.acceptedMemoryTraceBurden :=
    env.acceptedMemoryTraceBurden_of_context h_mem_context
  have h_memory_burden : env.memoryBurden :=
    env.memoryBurden_of_acceptedMemoryTraceBurden h_accepted_memory_burden
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift env
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_remaining env h_memory_burden h_known_bugs

end ZiskFv.Compliance
