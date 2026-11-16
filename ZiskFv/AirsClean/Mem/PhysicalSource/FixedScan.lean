import ZiskFv.AirsClean.Mem.Stage1.SourceColumns
import ZiskFv.Field.Goldilocks
import Mathlib.Tactic

/-! INTERNAL Mem-only scan of the SAME original native fixed buffer.
traces.rs295–298 and the checked PIL roster give width2, SEGMENT_L1 at0 and
__L1__ at1. Only column1 is checked here; the two named columns are not aliased.
The tail-recursive scan constructs no physical-row list/vector or fixed slice.
This is a computed internal constructor check, not a Root/caller premise. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.FixedScan

open Goldilocks

def pulse (row : Nat) : FGL := if row = 0 then 1 else 0

/-- Each successful branch tail-calls on the original array. The bounds proof
is erased; no per-row Option, copied row, or intermediate index list is built. -/
def checkFrom (fixed : Array FGL) (first : Nat) : Nat → Bool
  | 0 => true
  | count + 1 =>
    if bound : 2 * first + 1 < fixed.size then
      if fixed[2 * first + 1]'bound = pulse first then
        checkFrom fixed (first + 1) count
      else false
    else false

def check (fixed : Array FGL) : Bool :=
  checkFrom fixed 0 Stage1.SourceColumns.physicalRows

theorem checkFrom_sound (fixed : Array FGL) (first count : Nat)
    (checked : checkFrom fixed first count = true) (index : Nat) (within : index < count) :
    fixed[2 * (first + index) + 1]? = some (pulse (first + index)) := by
  induction count generalizing first index with
  | zero => omega
  | succ count ih =>
    unfold checkFrom at checked
    split_ifs at checked with bound value
    · cases index with
      | zero => simpa [bound, pulse] using value
      | succ index =>
        have tail := ih (first + 1) checked index (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
    · contradiction
    · contradiction

theorem checkFrom_complete (fixed : Array FGL) (first count : Nat)
    (values : ∀ index, index < count →
      fixed[2 * (first + index) + 1]? = some (pulse (first + index))) :
    checkFrom fixed first count = true := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    have firstValue := values 0 (by omega)
    have bound : 2 * first + 1 < fixed.size := by
      by_contra absent
      simp [Nat.add_zero, Nat.not_lt.mp absent] at firstValue
    have value : fixed[2 * first + 1]'bound = pulse first := by
      simpa [bound] using firstValue
    rw [checkFrom, dif_pos bound, if_pos value]
    apply ih
    intro index within
    have nextValue := values (index + 1) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using nextValue

theorem check_iff (fixed : Array FGL) :
    check fixed = true ↔ ∀ row : Fin Stage1.SourceColumns.physicalRows,
      fixed[2 * row.val + 1]? = some (pulse row.val) := by
  constructor
  · intro checked row
    simpa using checkFrom_sound fixed 0 _ checked row.val row.isLt
  · intro values
    apply checkFrom_complete
    intro index within
    simpa using values ⟨index, within⟩

end ZiskFv.AirsClean.Mem.PhysicalSource.FixedScan
