import Source415DomainComparison.WitnessSplice

/-! Intrinsic old-domain capacity. Main already carries the source's fixed
4194304-row domain; no accepted-trace premise is added here. The unresolved
counting direction is to bound the old Binary/Extension row counts by that
Main count using actual old OpBus balance and Arith's paired primary/remainder
emissions. These numerical endpoint facts alone do not prove that direction. -/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

variable {p : Nat} {program : Program p}

 theorem old_main_capacity (old : OldWitness p program) :
    (oldTable old 14).table.length ≤ Main.mainFixedCapacity := by
  rw [Table.table_length]
  have domain := (oldTable old 14).fixed_domain
  have component : (oldTable old 14).component =
      Main.componentWithRomMemAndOpBus p program := oldTable_component old 14
  rw [component] at domain
  exact domain Main.mainFixedColumns rfl

 theorem binary_source_main_capacity_no_overflow :
    BinaryTable.tableSize + 8 * Main.mainFixedCapacity < GL_prime := by decide

 theorem extension_source_main_capacity_no_overflow :
    BinaryExtensionTable.tableSize + 8 * Main.mainFixedCapacity < GL_prime := by decide

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
