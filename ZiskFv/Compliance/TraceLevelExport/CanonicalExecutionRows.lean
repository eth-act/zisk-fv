import ZiskFv.Compliance.TraceLevelExport.ProductionRowLowering
import ZiskFv.Compliance.TraceLevelExport.ExecutionSpanLegacy

/-!
# Canonical physical intervals

Every boundary is computed by summing widths, never supplied as an independent
placement promise. Source widths below come from successful production rows.
The legacy comparison proves only placement equivalence on the old supported
domain; it does not turn old decode evidence into a source parser certificate.
-/

namespace ZiskFv.Compliance.CanonicalExecutionRows

open scoped BigOperators

/-- Sum exactly the widths before a cut; no out-of-range word is read. -/
def rowPrefix {n : Nat} (width : Fin n → Nat) (cut : Nat) : Nat :=
  ∑ i : Fin n, if i.val < cut then width i else 0

@[simp] theorem prefix_zero {n : Nat} (width : Fin n → Nat) :
    rowPrefix width 0 = 0 := by simp [rowPrefix]

theorem prefix_succ {n : Nat} (width : Fin n → Nat) (i : Fin n) :
    rowPrefix width (i.val + 1) = rowPrefix width i.val + width i := by
  have hterm (j : Fin n) :
      (if j.val < i.val + 1 then width j else 0) =
        (if j.val < i.val then width j else 0) +
          (if j = i then width i else 0) := by
    by_cases hji : j = i
    · subst j
      simp
    · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hlt : j.val < i.val
      · simp [hlt, Nat.lt_succ_of_lt hlt, hji]
      · have hnext : ¬ j.val < i.val + 1 := by omega
        simp [hlt, hnext, hji]
  calc
    rowPrefix width (i.val + 1) =
        ∑ j : Fin n, ((if j.val < i.val then width j else 0) +
          (if j = i then width i else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hterm j
    _ = rowPrefix width i.val + width i := by
      rw [Finset.sum_add_distrib]
      simp [rowPrefix]

theorem prefix_mono {n : Nat} (width : Fin n → Nat) {a b : Nat}
    (hab : a ≤ b) : rowPrefix width a ≤ rowPrefix width b := by
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : i.val < a <;> by_cases hb : i.val < b <;>
    simp [ha, hb] <;> omega

theorem prefix_strict {n : Nat} (width : Fin n → Nat)
    (positive : ∀ i, 0 < width i) (i j : Fin n) (hij : i.val < j.val) :
    rowPrefix width i.val < rowPrefix width j.val := by
  have hs := prefix_succ width i
  have hm := prefix_mono width (show i.val + 1 ≤ j.val by omega)
  have hp := positive i
  omega

/-- Each physical row before the derived endpoint belongs to exactly one span. -/
theorem prefix_cover {n : Nat} (width : Fin n → Nat)
    (p : Nat) (hp : p < rowPrefix width n) :
    ∃! i : Fin n, rowPrefix width i.val ≤ p ∧ p < rowPrefix width (i.val + 1) := by
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    subst n
    simpa using hp
  have hex : ∃ k : Nat, k < n ∧ p < rowPrefix width (k + 1) := by
    refine ⟨n - 1, by omega, ?_⟩
    simpa only [Nat.sub_add_cancel hn] using hp
  let k := Nat.find hex
  have hk : k < n ∧ p < rowPrefix width (k + 1) := Nat.find_spec hex
  have hstart : rowPrefix width k ≤ p := by
    by_contra h
    have hkpos : 0 < k := by
      by_contra hzero
      have : k = 0 := by omega
      rw [this] at h
      simpa using h
    have hprev : k - 1 < n ∧ p < rowPrefix width ((k - 1) + 1) := by
      refine ⟨by omega, ?_⟩
      rw [Nat.sub_add_cancel hkpos]
      omega
    have hminimal : k ≤ k - 1 := Nat.find_min' hex hprev
    omega
  refine ⟨⟨k, hk.1⟩, ⟨hstart, hk.2⟩, ?_⟩
  intro j hj
  apply Fin.ext
  change j.val = k
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hm := prefix_mono width (show j.val + 1 ≤ k by omega)
    omega
  · have hm := prefix_mono width (show k + 1 ≤ j.val by omega)
    omega

/-- Actual source-selected widths, not an opcode guess or parser fallback. -/
def sourceWidth {n : Nat} {words : Fin n → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i)) (i : Fin n) : Nat :=
  (lowering i).width

def sourceStart {n : Nat} {words : Fin n → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i)) (i : Fin n) : Nat :=
  rowPrefix (sourceWidth lowering) i.val

def sourceEnd {n : Nat} {words : Fin n → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i)) : Nat :=
  rowPrefix (sourceWidth lowering) n

theorem source_successor {n : Nat} {words : Fin n → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i)) (i j : Fin n)
    (hnext : j.val = i.val + 1) :
    sourceStart lowering j = sourceStart lowering i + (lowering i).width := by
  dsimp [sourceStart]
  rw [hnext, prefix_succ]
  rfl

theorem source_prefix_exact {n : Nat} {words : Fin n → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i))
    (p : Nat) (hp : p < sourceEnd lowering) :
    ∃! i : Fin n, sourceStart lowering i ≤ p ∧
      p < sourceStart lowering i + (lowering i).width := by
  have h := prefix_cover (sourceWidth lowering) p hp
  simpa only [sourceStart, prefix_succ, sourceWidth] using h

/-- Widths read from OLD decode-selected producers. Source-width agreement is
not asserted by this definition; the following comparison concerns placement. -/
noncomputable def legacyWidth {n : Nat} {trace : AcceptedZiskTrace n}
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i)) (i : Fin n) : Nat :=
  stepProducerRow i (steps i) (decoded i) + 1 - i.val

theorem legacy_width_positive {n : Nat} {trace : AcceptedZiskTrace n}
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i)) (i : Fin n) :
    0 < legacyWidth steps decoded i := by
  have h := ExecutionSpanLegacy.producer_eq_index_or_succ i (steps i) (decoded i)
  dsimp [legacyWidth]
  omega

/-- Old supported placements imply their canonical prefix starts, with NO new
placement or parser-success premise. The final width may still be two. -/
theorem legacy_start_eq_index {n : Nat} {trace : AcceptedZiskTrace n}
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i))
    (aligned : StepRowsAligned trace steps decoded) (i : Fin n) :
    rowPrefix (legacyWidth steps decoded) i.val = i.val := by
  have hprefix : ∀ k, k < n → rowPrefix (legacyWidth steps decoded) k = k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hklt : k < n := by omega
      let j : Fin n := ⟨k, hklt⟩
      have hproducer : stepProducerRow j (steps j) (decoded j) = k := aligned k hk
      have hw : legacyWidth steps decoded j = 1 := by
        dsimp [legacyWidth]
        rw [hproducer]
        dsimp [j]
        omega
      have hsucc := prefix_succ (legacyWidth steps decoded) j
      change rowPrefix (legacyWidth steps decoded) (k + 1) =
        rowPrefix (legacyWidth steps decoded) k + legacyWidth steps decoded j at hsucc
      rw [hsucc, ih hklt, hw]
  exact hprefix i.val i.isLt

theorem legacy_stop_eq_producer {n : Nat} {trace : AcceptedZiskTrace n}
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i))
    (aligned : StepRowsAligned trace steps decoded) (i : Fin n) :
    rowPrefix (legacyWidth steps decoded) (i.val + 1) =
      stepProducerRow i (steps i) (decoded i) + 1 := by
  rw [prefix_succ, legacy_start_eq_index steps decoded aligned]
  have h := ExecutionSpanLegacy.producer_eq_index_or_succ i (steps i) (decoded i)
  dsimp [legacyWidth]
  omega

/-- Comparative OLD placement implication, including a final expanded JALR.
The endpoint is the last producer plus one, not `n` or the Main table height. -/
theorem legacy_canonical_prefix {n : Nat} {trace : AcceptedZiskTrace n}
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i))
    (aligned : StepRowsAligned trace steps decoded)
    (last : Fin n) (hfinal : last.val + 1 = n) :
    rowPrefix (legacyWidth steps decoded) n =
        stepProducerRow last (steps last) (decoded last) + 1 ∧
      ∀ p, p < rowPrefix (legacyWidth steps decoded) n →
        ∃! i : Fin n, i.val ≤ p ∧ p ≤ stepProducerRow i (steps i) (decoded i) := by
  constructor
  · simpa only [hfinal] using legacy_stop_eq_producer steps decoded aligned last
  · intro p hp
    have h := prefix_cover (legacyWidth steps decoded) p hp
    simpa only [legacy_start_eq_index steps decoded aligned,
      legacy_stop_eq_producer steps decoded aligned, Nat.lt_succ_iff] using h

/-- Source-derived widths make architectural starts strictly increasing. -/
theorem source_starts_strict {n : Nat} {words : Fin n → BitVec 32}
    (lowering : ∀ i, SuccessfulRowLowering (words i)) (i j : Fin n)
    (hij : i.val < j.val) : sourceStart lowering i < sourceStart lowering j :=
  prefix_strict (sourceWidth lowering) (fun i => (lowering i).width_pos) i j hij

/-- Two real source words: expanded JALR followed by an ordinary ADDI. -/
def nonfinalJalrWords : Fin 2 → BitVec 32 :=
  Fin.cases 0x00208067#32 (fun _ => 0x00000013#32)

noncomputable def nonfinalJalrLowering :
    ∀ i : Fin 2, SuccessfulRowLowering (nonfinalJalrWords i) :=
  Fin.cases sourceJalrTwo (fun _ => sourceAddiOne)

/-- The first real source lowering is nonfinal and occupies rows0,1; the next
instruction begins at row2. Every claimed physical row has a unique owner.
This is source-layout constructibility, not accepted-trace semantic continuity. -/
theorem nonfinal_jalr_source_layout :
    sourceStart nonfinalJalrLowering (0 : Fin 2) = 0 ∧
      sourceStart nonfinalJalrLowering (1 : Fin 2) = 2 ∧
      sourceEnd nonfinalJalrLowering = 3 ∧
      ∀ p, p < 3 → ∃! i : Fin 2,
        sourceStart nonfinalJalrLowering i ≤ p ∧
          p < sourceStart nonfinalJalrLowering i + (nonfinalJalrLowering i).width := by
  have hw0 : sourceWidth nonfinalJalrLowering (0 : Fin 2) = 2 :=
    sourceJalrTwo_width
  have hw1 : sourceWidth nonfinalJalrLowering (1 : Fin 2) = 1 :=
    sourceAddiOne_width
  have hfirst := prefix_succ (sourceWidth nonfinalJalrLowering) (0 : Fin 2)
  change rowPrefix (sourceWidth nonfinalJalrLowering) 1 =
    rowPrefix (sourceWidth nonfinalJalrLowering) 0 +
      sourceWidth nonfinalJalrLowering (0 : Fin 2) at hfirst
  have hnext : sourceStart nonfinalJalrLowering (1 : Fin 2) = 2 := by
    simpa only [sourceStart, prefix_zero, zero_add, hw0] using hfirst
  have hlast := prefix_succ (sourceWidth nonfinalJalrLowering) (1 : Fin 2)
  change sourceEnd nonfinalJalrLowering =
    sourceStart nonfinalJalrLowering (1 : Fin 2) +
      sourceWidth nonfinalJalrLowering (1 : Fin 2) at hlast
  have hend : sourceEnd nonfinalJalrLowering = 3 := by
    simpa only [hnext, hw1] using hlast
  refine ⟨by simp [sourceStart], hnext, hend, ?_⟩
  intro p hp
  exact source_prefix_exact nonfinalJalrLowering p (by rw [hend]; exact hp)

end ZiskFv.Compliance.CanonicalExecutionRows
