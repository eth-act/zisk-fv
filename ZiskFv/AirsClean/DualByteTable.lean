import ZiskFv.AirsClean.RangeTables
import ZiskFv.Channels.DualByte

/-! Source: `zisk/precompiles/dma/pil/dual_range.pil:8-16`, instantiated by
`zisk/pil/zisk.pil:76` with min1=min2=0,max1=max2=255,id=88.
A repeats each value 256 times, while B cycles 0..255. -/
namespace ZiskFv.AirsClean.DualByteTable
open Goldilocks
open ZiskFv.Channels.DualByte

/-- Exact physical fixed-column row order, not merely set-equivalent order. -/
def sourceRow (i : Fin 65536) : DualByteMessage FGL :=
  ⟨((i.val / 256 : ℕ) : FGL), ((i.val % 256 : ℕ) : FGL)⟩

def table : StaticTable FGL DualByteMessage where
  name := "DualByte88"
  length := 65536
  row := sourceRow
  index t := 256 * t.byte_a.val + t.byte_b.val
  Spec t := t.byte_a.val < 256 ∧ t.byte_b.val < 256
  contains_iff := by
    intro t
    constructor
    · rintro ⟨i, rfl⟩
      have hi := i.isLt
      dsimp [sourceRow]
      constructor <;> rw [Nat.mod_eq_of_lt (by omega)]
      · omega
      · exact Nat.mod_lt _ (by omega)
    · rintro ⟨ha, hb⟩
      let i : Fin 65536 := ⟨256 * t.byte_a.val + t.byte_b.val, by omega⟩
      refine ⟨i, ?_⟩
      have hi := i.isLt
      have haeq : t.byte_a = ((i.val / 256 : ℕ) : FGL) := by
        apply Fin.ext
        rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
        dsimp [i]
        omega
      have hbeq : t.byte_b = ((i.val % 256 : ℕ) : FGL) := by
        apply Fin.ext
        rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
        dsimp [i]
        omega
      exact congrArg₂ DualByteMessage.mk haeq hbeq

/-- The source row number is recovered from the fixed columns. This is stronger
than set membership and distinguishes the physical A/B order. -/
theorem sourceRow_index (i : Fin 65536) :
    table.index (sourceRow i) = i.val := by
  have hi := i.isLt
  have ha : (sourceRow i).byte_a.val = i.val / 256 := by
    change (((i.val / 256 : ℕ) : FGL)).val = i.val / 256
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hb : (sourceRow i).byte_b.val = i.val % 256 := by
    change (((i.val % 256 : ℕ) : FGL)).val = i.val % 256
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  change 256 * (sourceRow i).byte_a.val + (sourceRow i).byte_b.val = i.val
  rw [ha, hb]
  omega

theorem sourceRow_injective : Function.Injective sourceRow := by
  intro i j hij
  apply Fin.ext
  have h := congrArg table.index hij
  simpa only [sourceRow_index] using h

theorem sourceRow_coordinates (i : Fin 65536) :
    (sourceRow i).byte_a = ((i.val / 256 : ℕ) : FGL) ∧
    (sourceRow i).byte_b = ((i.val % 256 : ℕ) : FGL) := ⟨rfl, rfl⟩

/-- Existing static consumer model has the same membership, despite enumerating
its rows in the opposite order. This does not identify physical fixed columns. -/
theorem consumer_membership_iff (t : DualByteMessage FGL) :
    table.Spec t ↔ RangeTables.dualByteTable.Spec #v[t.byte_a, t.byte_b] := by
  rfl

end ZiskFv.AirsClean.DualByteTable
