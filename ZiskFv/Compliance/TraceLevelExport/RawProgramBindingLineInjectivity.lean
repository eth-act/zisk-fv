import ZiskFv.Compliance.TraceLevelExport.RawProgramBinding

namespace ZiskFv.Compliance.RawProgramBinding

/-- The unchanged six-clause binding implies globally unique committed lines.
The serializer's existing line lemmas also cover extraction failures; no new
lowering-success, source-image, or runtime-layout premise is introduced. This
is a comparative lemma, not a predicate or caller cutover. -/
theorem program_lines_injective_of_programRowsBinding {n rawLength : Nat}
    {trace : AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength}
    {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    (binding : ProgramRowsBinding trace start addr rawProgram) :
    Function.Injective (fun j : Fin trace.programLength => (trace.program j).line) := by
  intro j j' sameLine
  obtain ⟨k, primary | ⟨row, second, index, rowEq⟩⟩ :=
    physical_row_of_programRowsBinding binding j
  · obtain ⟨index, rowEq⟩ := primary
    have lineAt : (trace.program j).line = addr k := by
      rw [rowEq, romMessagesOfRaw_first_line]
    have other := primary_row_at_architectural_line binding j' k
      (sameLine.symm.trans lineAt)
    exact index.trans other.1.symm
  · obtain ⟨k', primary' | ⟨row', second', index', rowEq'⟩⟩ :=
      physical_row_of_programRowsBinding binding j'
    · obtain ⟨index', rowEq'⟩ := primary'
      have lineAt' : (trace.program j').line = addr k' := by
        rw [rowEq', romMessagesOfRaw_first_line]
      have first := primary_row_at_architectural_line binding j k'
        (sameLine.trans lineAt')
      exact first.1.trans index'.symm
    · have lineAt : (trace.program j).line = addr k + 1 := by
        rw [rowEq, romMessagesOfRaw_second_line second]
      have lineAt' : (trace.program j').line = addr k' + 1 := by
        rw [rowEq', romMessagesOfRaw_second_line second']
      have addressEq : addr k = addr k' :=
        add_right_cancel (lineAt.symm.trans (sameLine.trans lineAt'))
      have wordEq : k = k' := by
        by_contra different
        rcases lt_or_gt_of_ne different with before | after
        · have strict := (binding.1 k k' before).2
          rw [addressEq] at strict
          omega
        · have strict := (binding.1 k' k after).2
          rw [addressEq] at strict
          omega
      subst k'
      exact Fin.ext (index.trans index'.symm)

end ZiskFv.Compliance.RawProgramBinding
