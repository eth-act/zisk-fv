import ZiskFv.AirsClean.MemAlignWriteByte.RawSource
import Init.Data.String.Lemmas.Splits

/-! Shared kernel proofs for the existing general String.toNat? source decoder.
No decoder input cases, native_decide, default values or new parser are added. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.SourceLiterals

private theorem fold_positions_of_splits {α : Type} (f : α → Char → α)
    (slice : String.Slice) (chars : List Char) (position : slice.Pos) (leftPart : String)
    (hsplits : position.Splits leftPart (String.ofList chars)) (initial : α) :
    Std.Iter.fold (fun state out => f state (out.val.get out.property)) initial
      ({ internalState := { currPos := position } } :
        Std.Iter (α := String.Slice.PosIterator slice) { p : slice.Pos // p ≠ slice.endPos }) =
      chars.foldl f initial := by
  induction chars generalizing position leftPart initial with
  | nil =>
    have hposition : position = slice.endPos := hsplits.eq_endPos_iff.mpr (by simp)
    subst position
    rw [Std.Iter.fold_eq_match_step]
    simp [Std.Iter.step, Std.Iter.toIterM, Std.IterM.step, Std.IterM.toIter,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure]
  | cons char chars ih =>
    have hsplit : position.Splits leftPart (String.singleton char ++ String.ofList chars) := by
      simpa only [String.singleton_eq_ofList, ← String.ofList_append,
        List.singleton_append] using hsplits
    have hposition : position ≠ slice.endPos := hsplit.ne_endPos_of_singleton
    have hget : position.get hposition = char := by
      have h := congrArg (fun text : String => text.toList.head?)
        (hsplit.eq_right (position.splits_next_right hposition))
      simpa using h.symm
    rw [Std.Iter.fold_eq_match_step]
    simpa [Std.Iter.step, Std.Iter.toIterM, Std.IterM.step, Std.IterM.toIter,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure, hposition, hget]
      using (ih (position := position.next hposition)
        (leftPart := leftPart ++ String.singleton char) hsplit.next (initial := f initial char))

/-- Generic normalization through the actual iterator implementation, including
its opaque loop implementation, not a source-text/numeral whitelist check. -/
theorem foldl_ofList {α : Type} (f : α → Char → α) (initial : α) (chars : List Char) :
    (String.ofList chars).toSlice.foldl f initial = chars.foldl f initial := by
  unfold String.Slice.foldl String.Slice.chars
  rw [Std.Iter.fold_map]
  exact fold_positions_of_splits f (String.ofList chars).toSlice chars
    (String.ofList chars).toSlice.startPos ""
    (by simpa using (String.ofList chars).toSlice.splits_startPos) initial

theorem foldl_singleton {α : Type} (char : Char) (f : α → Char → α) (initial : α) :
    (String.singleton char).toSlice.foldl f initial = f initial char := by
  simpa [String.singleton_eq_ofList] using foldl_ofList f initial [char]

theorem toNat_zero : "0".toNat? = some 0 := by
  change (String.ofList ['0']).toNat? = some 0
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList]
  simp [String.Slice.isEmpty]

theorem toNat_one : "1".toNat? = some 1 := by
  change (String.ofList ['1']).toNat? = some 1
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList]
  simp [String.Slice.isEmpty]

theorem toNat_two : "2".toNat? = some 2 := by
  change (String.ofList ['2']).toNat? = some 2
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList]
  simp [String.Slice.isEmpty]

theorem toNat_four : "4".toNat? = some 4 := by
  change (String.ofList ['4']).toNat? = some 4
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList]
  simp [String.Slice.isEmpty]

theorem toNat_eight : "8".toNat? = some 8 := by
  change (String.ofList ['8']).toNat? = some 8
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList]
  simp [String.Slice.isEmpty]

theorem toNat_ten : "10".toNat? = some 10 := by
  change (String.ofList ['1', '0']).toNat? = some 10
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList]
  simp [String.Slice.isEmpty]

end ZiskFv.AirsClean.MemAlignWriteByte.SourceLiterals
