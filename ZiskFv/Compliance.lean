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

`zisk_riscv_compliant_program_bus_except_known_defects` is the public
defect-aware theorem shape while `docs/fv/defects.md` contains open
claim-weakening defects. Its extra `h_known_bugs` binder is orthogonal to
the validity witnesses already bundled in `OpEnvelope`: validity says the
current modeled constraints hold; `h_known_bugs` says this envelope is not
inside a ledgered defect region.
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

/-- Shared C7 static BinaryExtension lookup obligation for the opcode families
    that currently consume BinaryExtensionTable semantics: signed loads,
    64-bit shifts, and W-shifts. Other arms reduce to `True` in each family
    predicate. -/
def OpEnvelope.binary_extension_static_lookup_soundness
    (env : OpEnvelope state m r_main) : Prop :=
  env.misc_signed_load_static_lookup_soundness
    ∧ env.shift_static_lookup_soundness
    ∧ env.remaining_wshift_static_lookup_soundness

/-- Shared C7 static lookup obligations currently discharged through Clean
    static providers for the terminal-A Binary-family route. -/
def OpEnvelope.binary_family_static_lookup_soundness
    (env : OpEnvelope state m r_main) : Prop :=
  env.rtype_binary_logic_static_lookup_soundness
    ∧ env.itype_binary_logic_static_lookup_soundness
    ∧ env.binary_extension_static_lookup_soundness

/-- **Known-defect-aware channel-balance global theorem.**

    For any `OpEnvelope` arm, the channel-balance form of the
    conclusion (`= state_effect_via_channels …`) holds outside the
    defect regions recorded by `Defects.NoKnownDefect`. -/
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope state m r_main)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift env
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc env
  · exact zisk_riscv_compliant_program_bus_remaining env h_known_bugs

/-- Defect-aware public compliance theorem.

    `h_known_bugs` is a visible exclusion of every currently ledgered defect
    region. The proof currently reuses the existing dispatcher theorem; as
    each defect predicate becomes more precise, opcode-family dispatchers can
    consume the corresponding derived facts locally. -/
theorem zisk_riscv_compliant_program_bus_except_known_defects
    (env : OpEnvelope state m r_main)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus env h_known_bugs

/-- Noncanonical C7 BinaryExtensionTable static route for the global
    channel-balance theorem.

    This composes the static routes for signed loads, 64-bit shifts, and
    W-shifts. The canonical global theorem above remains unchanged until the
    terminal Binary-family ensemble provides this shared witness from the Clean
    channel construction rather than as an external theorem parameter. -/
theorem zisk_riscv_compliant_program_bus_binary_extension_of_static_lookup
    (env : OpEnvelope state m r_main)
    (h_known_bugs : Defects.NoKnownDefect env)
    (offset : ℕ) (cleanEnv : Environment FGL)
    (h_static : env.binary_extension_static_lookup_soundness) :
    env.exec_eq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift_of_static_lookup env offset cleanEnv h_static.2.1
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc_signed_load_of_static_lookup
      env offset cleanEnv h_static.1
  · exact zisk_riscv_compliant_program_bus_remaining_wshift_of_static_lookup
      env h_known_bugs offset cleanEnv h_static.2.2

/-- Noncanonical C7 Binary-family static route for the global channel-balance
    theorem.

    This extends `zisk_riscv_compliant_program_bus_binary_extension_of_static_lookup`
    with BinaryTable static routes for AND/ANDI/OR/ORI/XOR/XORI and the
    64-bit chain arms SUB/SLT/SLTU/SLTI/SLTIU. The chain arms derive
    `mode32 = 0` and the concrete `b_op` from the selected Binary row's
    op-bus emission plus Binary column ranges. Binary core facts are also
    projected from the same static-lookup path, so the shared BinaryTable
    premise is just `StaticLookupSoundness`. -/
theorem zisk_riscv_compliant_program_bus_binary_family_of_static_lookup
    (env : OpEnvelope state m r_main)
    (h_known_bugs : Defects.NoKnownDefect env)
    (offset : ℕ) (cleanEnv : Environment FGL)
    (h_static : env.binary_family_static_lookup_soundness) :
    env.exec_eq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary_logic_of_static_lookup
      env offset cleanEnv h_static.1
  · exact zisk_riscv_compliant_program_bus_itype_binary_logic_of_static_lookup
      env offset cleanEnv h_static.2.1
  · exact zisk_riscv_compliant_program_bus_shift_of_static_lookup
      env offset cleanEnv h_static.2.2.2.1
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc_signed_load_of_static_lookup
      env offset cleanEnv h_static.2.2.1
  · exact zisk_riscv_compliant_program_bus_remaining_wshift_of_static_lookup
      env h_known_bugs offset cleanEnv h_static.2.2.2.2

end ZiskFv.Compliance
