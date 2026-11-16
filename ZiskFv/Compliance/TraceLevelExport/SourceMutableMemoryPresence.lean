import ZiskFv.Compliance.TraceLevelExport.CanonicalSyntaxBoundary
import ZiskFv.Compliance.AcceptedZiskTrace.MemAlignRom
import ZiskFv.Compliance.TraceLevelExport.SourceMutableMemoryPresenceSourceFlags

/-!
# Mutable-memory presence from real source rows

The checked-source endpoint keeps the ORIGINAL Accepted n and computed source
heads. Complete real provider classification, exact MemAlign ROM predecessors,
intrinsic boot/D1/D3 constraints and finite spatial descent close presence.
The finite-support bound is derived from the actual witness roster and fixed
MemAlign domain, not taken as a caller premise. Source ROM provenance also
eliminates the otherwise possible Main minus-two store-provider alternative.

Separate local counterexamples record why neither timestamp transport nor
always-negative word-eight arity may replace this argument. They are not full
accepted-ensemble counterexamples to presence. Presence itself does not prove
replay membership, chronological read evidence, initial-memory agreement, or
the three explicit SB/SH/SW preserved-byte primitives. Source endpoint P may
still be n+1; no Accepted retarget or extra auxiliary execution is introduced.
-/

namespace ZiskFv.Compliance.SourceMutableMemoryPresence

open Goldilocks Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

private theorem present_of_mutable_provider
    {n : Nat} {trace : AcceptedZiskTrace n}
    {requestTable : Table FGL}
    {mainRow : Array FGL} {mainInteraction : Interaction FGL}
    {mainMsg : MemBusMessage (Expression FGL)} {multiplicity addressSpace : FGL}
    (provider : ActiveMainMutableMemProviderRowMatchSpec trace.program trace.witness
      requestTable mainRow mainInteraction mainMsg multiplicity addressSpace) :
    MutableMemPresent trace.witness := by
  rcases provider with
    ⟨_, _, _, _, _, table, member, _, row, rowMember, _, component, _⟩
  exact ⟨table, member, component, List.length_pos_of_mem rowMember⟩

/-- Finite spatial descent does not need absolute address bounds or timestamp
order. A small nonempty field support cannot give EVERY member a predecessor
at a positive distance at most seven. This is a mathematical finite-support
lemma, NOT an assumed provider-closure certificate for an Accepted trace. -/
theorem no_small_closed_field_support
    (support : Finset FGL) (small : 7 * support.card < GL_prime)
    (nonempty : support.Nonempty) :
    ¬ (∀ x ∈ support, ∃ y ∈ support, ∃ distance : Nat,
      1 ≤ distance ∧ distance ≤ 7 ∧ y + (distance : FGL) = x) := by
  classical
  intro closed
  choose previous previousMem gap gapLow gapHigh edge using closed
  let Node := { x : FGL // x ∈ support }
  let advance : Node → Node := fun x =>
    ⟨previous x.val x.property, previousMem x.val x.property⟩
  let stride : Node → Nat := fun x => gap x.val x.property
  obtain ⟨first, firstMem⟩ := nonempty
  let start : Node := ⟨first, firstMem⟩
  let walk : Nat → Node := Nat.rec start (fun _ x => advance x)
  let travel : Nat → Nat := Nat.rec 0 (fun k accumulated => accumulated + stride (walk k))
  have strideLow (x : Node) : 1 ≤ stride x := gapLow x.val x.property
  have strideHigh (x : Node) : stride x ≤ 7 := gapHigh x.val x.property
  have advanceEdge (x : Node) : (advance x).val + (stride x : FGL) = x.val :=
    edge x.val x.property
  have travelBound (k : Nat) : travel k ≤ 7 * k := by
    induction k with
    | zero => change 0 ≤ 7 * 0; omega
    | succ k ih =>
        change travel k + stride (walk k) ≤ 7 * (k + 1)
        have bound := strideHigh (walk k)
        omega
  have travelStrict : StrictMono travel := by
    apply strictMono_nat_of_lt_succ
    intro k
    change travel k < travel k + stride (walk k)
    have positive := strideLow (walk k)
    omega
  have pathEq (k : Nat) : (walk k).val + (Nat.cast (travel k) : FGL) = start.val := by
    induction k with
    | zero => change start.val + (0 : FGL) = start.val; ring
    | succ k ih =>
        change (advance (walk k)).val +
          ((travel k + stride (walk k) : Nat) : FGL) = start.val
        rw [Nat.cast_add]
        have next := advanceEdge (walk k)
        linear_combination next + ih
  let path : Fin (support.card + 1) → Node := fun i => walk i.val
  obtain ⟨i, j, distinct, collision⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt path (by
      simp [Node, Fintype.card_coe])
  have nodeEq : (walk i.val).val = (walk j.val).val :=
    congrArg Subtype.val collision
  have fieldEq : (Nat.cast (travel i.val) : FGL) = (Nat.cast (travel j.val) : FGL) := by
    have left := pathEq i.val
    have right := pathEq j.val
    rw [nodeEq] at left
    exact add_left_cancel (left.trans right.symm)
  have iBound : travel i.val < GL_prime := by
    apply lt_of_le_of_lt (travelBound i.val)
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 7 (by omega)) small
  have jBound : travel j.val < GL_prime := by
    apply lt_of_le_of_lt (travelBound j.val)
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 7 (by omega)) small
  have naturalEq := congrArg Fin.val fieldEq
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt iBound,
    Nat.mod_eq_of_lt jBound] at naturalEq
  exact distinct (Fin.ext (travelStrict.injective naturalEq))

private theorem alignment_table_height_bound (table : Table FGL)
    (componentEq : table.component = ZiskFv.AirsClean.MemAlign.component) :
    table.table.length ≤ ZiskFv.AirsClean.MemAlign.memAlignFixedCapacity := by
  cases table with
  | mk tableComponent rawRows data uniform fixedDomain =>
      change tableComponent = ZiskFv.AirsClean.MemAlign.component at componentEq
      subst tableComponent
      have bound := fixedDomain ZiskFv.AirsClean.MemAlign.memAlignFixedColumns rfl
      simpa only [Table.table_length] using bound

private noncomputable def wordReadProviderFilter (table : Table FGL) (raw : Array FGL) : Bool := by
  classical
  let row := eval (table.environment raw) ZiskFv.AirsClean.MemAlign.component.rowInputVar
  exact decide (row.width = 8 ∧ row.wr = 0 ∧
    row.sel_prove - (row.sel_up_to_down + row.sel_down_to_up) ≠ 0 ∧
    row.sel_prove - (row.sel_up_to_down + row.sel_down_to_up) ≠ -1)

private noncomputable def alignmentPointers (tables : List (Table FGL)) : List FGL := by
  classical
  exact tables.flatMap fun table =>
    if table.component = ZiskFv.AirsClean.MemAlign.component then
      (table.table.filter (wordReadProviderFilter table)).map fun row =>
        (ZiskFv.AirsClean.MemAlign.memBusMessage
          (eval (table.environment row) ZiskFv.AirsClean.MemAlign.component.rowInputVar)).ptr
    else []

private theorem alignmentPointers_length_bound (tables : List (Table FGL)) :
    (alignmentPointers tables).length ≤
      tables.length * ZiskFv.AirsClean.MemAlign.memAlignFixedCapacity := by
  classical
  induction tables with
  | nil => simp [alignmentPointers]
  | cons table tables ih =>
      by_cases componentEq : table.component = ZiskFv.AirsClean.MemAlign.component
      · have height := alignment_table_height_bound table componentEq
        have selected := List.length_filter_le (wordReadProviderFilter table) table.table
        simp only [alignmentPointers, List.flatMap_cons, if_pos componentEq,
          List.length_append, List.length_map, List.length_cons] at ⊢
        change (table.table.filter (wordReadProviderFilter table)).length +
            (alignmentPointers tables).length ≤
          (tables.length + 1) * ZiskFv.AirsClean.MemAlign.memAlignFixedCapacity
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [alignmentPointers, List.flatMap_cons, if_neg componentEq,
          List.nil_append, List.length_cons] at ⊢
        change (alignmentPointers tables).length ≤
          (tables.length + 1) * ZiskFv.AirsClean.MemAlign.memAlignFixedCapacity
        rw [Nat.add_mul, Nat.one_mul]
        omega

/-- Actual active word-eight READ-PROVIDER pointers in the SAME original
accepted witness. Selection uses exact source opcode, width and raw FGL
multiplicity, not a chosen replay provider or an address-alignment assumption. -/
noncomputable def actualAlignmentSupport {n : Nat} (trace : AcceptedZiskTrace n) : Finset FGL := by
  classical
  exact (alignmentPointers trace.witness.allTables).toFinset

/-- The finite-support no-wrap bound is DERIVED from the actual full witness
roster and MemAlign's intrinsic fixed domain. It is not a new caller premise.
All MemAlign rows, including padding and both request polarities, are counted. -/
theorem actualAlignmentSupport_small {n : Nat} (trace : AcceptedZiskTrace n) :
    7 * (actualAlignmentSupport trace).card < GL_prime := by
  classical
  have roster : trace.witness.allTables.length = 16 := by
    have mapped := congrArg List.length trace.witness.allTables_map_component
    simp only [List.length_map] at mapped
    rw [mapped]
    simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
      Ensemble.allTables, SoundEnsemble.addTable_tables,
      SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.empty, Ensemble.empty]
  have pointerBound := alignmentPointers_length_bound trace.witness.allTables
  have cardBound : (actualAlignmentSupport trace).card ≤
      (alignmentPointers trace.witness.allTables).length := by
    exact List.toFinset_card_le _
  rw [roster] at pointerBound
  change (alignmentPointers trace.witness.allTables).length ≤ 16 * 2097152 at pointerBound
  omega

/-- Accepted/source integration must derive the predecessor closure from real
provider/ROM/index facts; this theorem does NOT assume that closure and return
presence. It proves that such closure is impossible on the actual witness
support, with its size bound discharged internally. -/
theorem actualAlignmentSupport_not_closed {n : Nat} (trace : AcceptedZiskTrace n)
    (nonempty : (actualAlignmentSupport trace).Nonempty) :
    ¬ (∀ x ∈ actualAlignmentSupport trace,
      ∃ y ∈ actualAlignmentSupport trace, ∃ distance : Nat,
        1 ≤ distance ∧ distance ≤ 7 ∧ y + (distance : FGL) = x) :=
  no_small_closed_field_support _ (actualAlignmentSupport_small trace) nonempty

/-- Classify a genuine pull using its raw message, without identifying the
`assumeGuarantees` bit of `pulled` with that of `emitted (-1)`. The reference
interaction in the result is only a typed message view; membership and balance
are consumed on the ORIGINAL real interaction. -/
private theorem pull_provider_coverage
    {n : Nat} (trace : AcceptedZiskTrace n)
    {requestTable : Table FGL} (tableMember : requestTable ∈ trace.witness.allTables)
    {requestRow : Array FGL} {request : Interaction FGL}
    (interactionMember : request ∈ requestTable.interactionsWith MemBusChannel.toRaw)
    {requestMult : Expression FGL} {requestMessage : MemBusMessage (Expression FGL)}
    (messageEq : request.msg = (((MemBusChannel.emitted requestMult requestMessage).toRaw).eval
      (requestTable.environment requestRow)).msg)
    (active : request.mult = -1) :
    ActiveMainMemProviderRowMatchSpec trace.program trace.witness requestTable requestRow
      (((MemBusChannel.emitted requestMult requestMessage).toRaw).eval
        (requestTable.environment requestRow)) requestMessage (-1) 2 := by
  have requestMember : request ∈ trace.witness.interactionsWith MemBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨requestTable, tableMember, interactionMember⟩
  obtain ⟨provider, providerMember, same, nonpull, nonzero,
      table, member, providerInTable, classification⟩ :=
    exists_matching_mem_component_of_active_main_interaction
      trace.witness trace.channels_balanced requestMember active
  have sameView := same.trans messageEq
  refine ⟨provider, providerMember, sameView, nonpull, nonzero,
    table, member, providerInTable, ?_⟩
  have specified := trace.spec_holds table member
  rcases classification with readByte | byte | general | mutable | main | boundary
  · obtain ⟨row, rowMember, evaluated⟩ :=
      exists_memAlignReadByte_row_eval_of_interaction_mem readByte providerInTable nonpull
    left
    refine ⟨row, rowMember, specified row rowMember, readByte, evaluated, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← evaluated]
    exact sameView
  · obtain ⟨row, rowMember, evaluated⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem byte providerInTable nonpull
    right; left
    refine ⟨row, rowMember, specified row rowMember, byte, evaluated, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← evaluated]
    exact sameView
  · obtain ⟨row, rowMember, evaluated⟩ :=
      exists_memAlign_row_eval_of_interaction_mem general providerInTable
    right; right; left
    refine ⟨row, rowMember, specified row rowMember, general, evaluated, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
    rw [← evaluated]
    exact sameView
  · rcases exists_mem_dual_row_eval_of_interaction_mem mutable providerInTable with
      ⟨row, rowMember, evaluated⟩ | ⟨row, rowMember, evaluated⟩
    · right; right; right; left
      refine ⟨row, rowMember, specified row rowMember, mutable, Or.inl ⟨evaluated, ?_⟩⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← evaluated]
      exact sameView
    · right; right; right; left
      refine ⟨row, rowMember, specified row rowMember, mutable, Or.inr ⟨evaluated, ?_⟩⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← evaluated]
      exact sameView
  · obtain ⟨row, rowMember, evaluated⟩ :=
      exists_main_mem_row_eval_of_interaction_mem main providerInTable
    right; right; right; right; left
    refine ⟨row, rowMember, specified row rowMember, main, ?_⟩
    rcases evaluated with aPre | aCurrent | bPre | bCurrent | cPre | cCurrent
    · left
      refine ⟨aPre, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← aPre]
      exact sameView
    · right; left
      refine ⟨aCurrent, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← aCurrent]
      exact sameView
    · right; right; left
      refine ⟨bPre, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← bPre]
      exact sameView
    · right; right; right; left
      refine ⟨bCurrent, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← bCurrent]
      exact sameView
    · right; right; right; right; left
      refine ⟨cPre, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← cPre]
      exact sameView
    · right; right; right; right; right
      refine ⟨cCurrent, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← cCurrent]
      exact sameView
  · right; right; right; right; right
    exact boundary

private theorem memAlign_eval_input (env : Environment FGL) :
    eval env ZiskFv.AirsClean.MemAlign.component.rowInputVar =
      ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment env := by
  simpa only [ZiskFv.AirsClean.MemAlign.component, Component.rowInputVar,
    ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment] using
    (eval_varFromOffset_valueFromOffset ZiskFv.AirsClean.MemAlign.MemAlignRow 0 env)

private theorem memAlign_eval_mult (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.MemAlign.MemAlignRow FGL) :
    Expression.eval env (row.sel_prove - ZiskFv.AirsClean.MemAlign.selAssumeExpr row) =
      (eval env row).sel_prove -
        ((eval env row).sel_up_to_down + (eval env row).sel_down_to_up) := by
  cases row
  simp only [ZiskFv.AirsClean.MemAlign.selAssumeExpr, Expression.eval,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field] <;> ring

private theorem memBus_eval_width (env : Environment FGL)
    (message : MemBusMessage (Expression FGL)) :
    (eval env message).width = Expression.eval env message.width := by
  cases message
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

/-- Balance for ANY real word-read pull, including a MemAlign assumption,
finds mutable Mem or an actual active general-MemAlign word-read provider.
The Main-self/RegisterBoundary and both byte-provider alternatives are
eliminated by their real opcodes/polarities/widths, not by caller exclusions.
Raw message equality is used: legacy entry matching alone drops width. -/
theorem wordRead_pull_provider
    {n : Nat} (trace : AcceptedZiskTrace n)
    {requestTable : Table FGL} (tableMember : requestTable ∈ trace.witness.allTables)
    {requestRow : Array FGL} (rowMember : requestRow ∈ requestTable.table)
    {request : Interaction FGL}
    (interactionMember : request ∈ requestTable.interactionsWith MemBusChannel.toRaw)
    {requestMult : Expression FGL} {requestMessage : MemBusMessage (Expression FGL)}
    (evaluated : request.msg = (((MemBusChannel.emitted requestMult requestMessage).toRaw).eval
      (requestTable.environment requestRow)).msg)
    (active : request.mult = -1)
    (readOp : (eval (requestTable.environment requestRow) requestMessage).mem_op = 1)
    (word : (eval (requestTable.environment requestRow) requestMessage).width = 8) :
    MutableMemPresent trace.witness ∨
      (eval (requestTable.environment requestRow) requestMessage).ptr ∈
        actualAlignmentSupport trace := by
  classical
  have coverage := pull_provider_coverage trace tableMember interactionMember evaluated active
  rcases activeMainMemProviderRowMatchSpec_mutable_or_nonmutable coverage with
    mutable | nonmutable
  · exact Or.inl (present_of_mutable_provider mutable)
  · rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases nonmutable with
      readByte | byte | general | main | boundary
    · rcases readByte with
        ⟨provider, _, sameMessage, _, _, table, _, _, row, _, _, _, providerEval, _⟩
      have rawEq := sameMessage
      rw [providerEval] at rawEq
      have typed := memBusMessage_eq_of_eval_emitted_provider_msg_eq
        (providerMult := 1) (h_msg := rawEq)
      have widths := congrArg MemBusMessage.width typed
      rw [ZiskFv.AirsClean.MemAlignReadByte.eval_memBusMessageExpr] at widths
      change (1 : FGL) = (eval (requestTable.environment requestRow) requestMessage).width
        at widths
      rw [word] at widths
      exact False.elim ((by decide : (1 : FGL) ≠ 8) widths)
    · rcases byte with
        ⟨provider, _, sameMessage, _, _, table, _, _, row, _, _, _, providerEval, _⟩
      have rawEq := sameMessage
      rw [providerEval] at rawEq
      have typed := memBusMessage_eq_of_eval_emitted_provider_msg_eq
        (providerMult := 1) (h_msg := rawEq)
      have widths := congrArg MemBusMessage.width typed
      rw [ZiskFv.AirsClean.MemAlignByte.eval_memBusMessageExpr] at widths
      change (1 : FGL) = (eval (requestTable.environment requestRow) requestMessage).width
        at widths
      rw [word] at widths
      exact False.elim ((by decide : (1 : FGL) ≠ 8) widths)
    · rcases general with
        ⟨provider, _, sameMessage, nonpull, nonzero,
          table, tableMember, _, row, rowMember, _, componentEq, providerEval, _⟩
      let value := eval (table.environment row) ZiskFv.AirsClean.MemAlign.component.rowInputVar
      have rawEq := sameMessage
      rw [providerEval] at rawEq
      have typed := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_msg := rawEq)
      rw [ZiskFv.AirsClean.MemAlign.eval_memBusMessageExpr] at typed
      have widths : value.width = 8 :=
        (congrArg MemBusMessage.width typed).trans word
      have opcode : value.wr + 1 = 1 :=
        (congrArg MemBusMessage.mem_op typed).trans readOp
      have read : value.wr = 0 := by linear_combination opcode
      have multEq : provider.mult =
          value.sel_prove - (value.sel_up_to_down + value.sel_down_to_up) := by
        rw [providerEval]
        exact memAlign_eval_mult (table.environment row)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar
      have pointerEq : (ZiskFv.AirsClean.MemAlign.memBusMessage value).ptr =
          (eval (requestTable.environment requestRow) requestMessage).ptr :=
        congrArg MemBusMessage.ptr typed
      right
      simp only [actualAlignmentSupport, List.mem_toFinset, alignmentPointers,
        List.mem_flatMap]
      refine ⟨table, tableMember, ?_⟩
      rw [if_pos componentEq, List.mem_map]
      refine ⟨row, ?_, pointerEq⟩
      rw [List.mem_filter]
      refine ⟨rowMember, ?_⟩
      simp only [wordReadProviderFilter, decide_eq_true_eq]
      change value.width = 8 ∧ value.wr = 0 ∧
        value.sel_prove - (value.sel_up_to_down + value.sel_down_to_up) ≠ 0 ∧
        value.sel_prove - (value.sel_up_to_down + value.sel_down_to_up) ≠ -1
      exact ⟨widths, read, by simpa only [← multEq] using nonzero,
        by simpa only [← multEq] using nonpull⟩
    · exact False.elim (not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one
        trace.constraints_hold rfl readOp main)
    · exact False.elim (not_activeMainRegisterBoundaryProviderRowMatchSpec_of_main_mem_op_one
        rfl readOp boundary)

namespace AlignmentChronology

open ZiskFv.AirsClean.MemAlign
open ZiskFv.AirsClean.MemAlignRomTable

/-- Exhaustive facts about the ACTUAL extracted ROM. Read-word prove rows
have positive offsets; this does not by itself imply their field pointers
are unaligned, since the source supplies no absolute `addr` range bound. -/
theorem extracted_readWord_prove_shape :
    ∀ i : Fin tableSize,
      (rowOfIndex i).width = 8 → (rowOfIndex i).flags.val < 256 →
        1 ≤ (rowOfIndex i).offset.val ∧ (rowOfIndex i).offset.val ≤ 7 ∧
          (rowOfIndex i).pc.val ∈ ({101, 104, 107, 110, 116, 122, 131} : Finset Nat) ∧
          (rowOfIndex i).deltaPc = 1 ∧ (rowOfIndex i).deltaAddr = 0 := by
  decide +kernel

/-- Every ROM edge ENTERING one of the seven word-read prove PCs is its
program's initial pc-zero, width-eight, up-to-down assumption. This is the
finite predecessor classification needed by spatial descent, independent of
the absent timestamp binding. No named ROM alternative is omitted. -/
theorem extracted_readWord_predecessor_shape :
    ∀ i : Fin tableSize,
      ((rowOfIndex i).pc + (rowOfIndex i).deltaPc).val ∈
        ({101, 104, 107, 110, 116, 122, 131} : Finset Nat) →
        (rowOfIndex i).pc = 0 ∧ (rowOfIndex i).offset = 0 ∧
          (rowOfIndex i).width = 8 ∧ (rowOfIndex i).deltaAddr = 0 ∧
          1536 ≤ (rowOfIndex i).flags.val ∧ (rowOfIndex i).flags.val < 1792 := by
  decide +kernel

/-- All extracted ROM flag words fit below the combined up/down bit. This
bound eliminates impossible simultaneous assumption bits without imposing an
additional validator constraint. -/
theorem extracted_flags_bound :
    ∀ i : Fin tableSize, (rowOfIndex i).flags.val < 2560 := by
  decide +kernel

private def lowFlagNat (row : MemAlignRow FGL) : Nat :=
  row.sel_0.val + row.sel_1.val * 2 + row.sel_2.val * 4 + row.sel_3.val * 8 +
    row.sel_4.val * 16 + row.sel_5.val * 32 + row.sel_6.val * 64 + row.sel_7.val * 128

private def flagNat (row : MemAlignRow FGL) : Nat :=
  lowFlagNat row + row.wr.val * 256 + row.reset.val * 512 +
    row.sel_up_to_down.val * 1024 + row.sel_down_to_up.val * 2048

private theorem bit_val_bound {x : FGL} (boolean : x * (1 - x) = 0) : x.val ≤ 1 := by
  rcases zero_or_one_of_bool boolean with zero | one
  · simp [zero]
  · simp [one]

private theorem flagNat_cast (row : MemAlignRow FGL) :
    (flagNat row : FGL) = (memAlignRomMessage row).flags := by
  simp only [flagNat, lowFlagNat, memAlignRomMessage, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Fin.cast_val_eq_self]
  ring

/-- Convert the actual Boolean source columns to a no-wrap natural flag
packing; no new row-validator or flag-range premise is used. -/
private theorem flagNat_facts (row : MemAlignRow FGL) (specification : Spec row) :
    (memAlignRomMessage row).flags.val = flagNat row ∧
      lowFlagNat row ≤ 255 ∧ row.wr.val ≤ 1 ∧ row.reset.val ≤ 1 ∧
      row.sel_up_to_down.val ≤ 1 ∧ row.sel_down_to_up.val ≤ 1 := by
  rcases specification with
    ⟨hwr, hreset, hup, hdown, h0, h1, h2, h3, h4, h5, h6, h7, _⟩
  have wr := bit_val_bound hwr
  have reset := bit_val_bound hreset
  have up := bit_val_bound hup
  have down := bit_val_bound hdown
  have b0 := bit_val_bound h0
  have b1 := bit_val_bound h1
  have b2 := bit_val_bound h2
  have b3 := bit_val_bound h3
  have b4 := bit_val_bound h4
  have b5 := bit_val_bound h5
  have b6 := bit_val_bound h6
  have b7 := bit_val_bound h7
  have low : lowFlagNat row ≤ 255 := by
    dsimp only [lowFlagNat]
    omega
  have noWrap : flagNat row < GL_prime := by
    dsimp only [flagNat]
    omega
  have value := congrArg Fin.val (flagNat_cast row)
  rw [Fin.val_natCast, Nat.mod_eq_of_lt noWrap] at value
  exact ⟨value.symm, low, wr, reset, up, down⟩

private theorem extracted_word_flags_without_assume :
    ∀ i : Fin tableSize, (rowOfIndex i).width = 8 →
      (rowOfIndex i).flags.val < 1024 → (rowOfIndex i).flags.val < 512 := by
  decide +kernel

/-- Complete polarity classification of a general MemAlign word-read
provider. In particular a nonzero, non-pull provider cannot secretly be two
simultaneous assumption bits with multiplicity minus two. The conclusion is
derived from live row Spec and the entire extracted ROM, not from a selected
prove-side defect exclusion. -/
theorem wordRead_provider_shape
    (row : MemAlignRow FGL) (specification : Spec row)
    (rom : memAlignRomTable.Spec (memAlignRomMessage row))
    (word : row.width = 8) (read : row.wr = 0)
    (nonpull : row.sel_prove - (row.sel_up_to_down + row.sel_down_to_up) ≠ -1) :
    row.sel_up_to_down = 0 ∧ row.sel_down_to_up = 0 ∧
      1 ≤ row.offset.val ∧ row.offset.val ≤ 7 ∧
      row.pc.val ∈ ({101, 104, 107, 110, 116, 122, 131} : Finset Nat) ∧
      row.delta_pc = 1 ∧ row.delta_addr = 0 ∧ row.reset = 0 := by
  obtain ⟨index, romEq⟩ := rom
  obtain ⟨packed, low, wrBound, resetBound, upBound, downBound⟩ :=
    flagNat_facts row specification
  have romBound : (memAlignRomMessage row).flags.val < 2560 := by
    rw [romEq]
    exact extracted_flags_bound index
  have notBoth : ¬ (row.sel_up_to_down = 1 ∧ row.sel_down_to_up = 1) := by
    rintro ⟨up, down⟩
    rw [packed] at romBound
    simp only [flagNat, up, down] at romBound
    omega
  have hup := specification.2.2.1
  have hdown := specification.2.2.2.1
  have disjoint := specification.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have noAssume : row.sel_up_to_down = 0 ∧ row.sel_down_to_up = 0 := by
    rcases zero_or_one_of_bool hup with up | up <;>
      rcases zero_or_one_of_bool hdown with down | down
    · exact ⟨up, down⟩
    · have proveZero : row.sel_prove = 0 := by
        simpa [up, down] using disjoint
      exact False.elim (nonpull (by simp [proveZero, up, down]))
    · have proveZero : row.sel_prove = 0 := by
        simpa [up, down] using disjoint
      exact False.elim (nonpull (by simp [proveZero, up, down]))
    · exact False.elim (notBoth ⟨up, down⟩)
  have flagExpression : flagNat row = lowFlagNat row + row.reset.val * 512 := by
    simp [flagNat, read, noAssume.1, noAssume.2]
  have below1024 : (memAlignRomMessage row).flags.val < 1024 := by
    rw [packed, flagExpression]
    omega
  have romWord : (rowOfIndex index).width = 8 := by
    rw [← romEq]
    exact word
  have below512 : (memAlignRomMessage row).flags.val < 512 := by
    rw [romEq] at below1024 ⊢
    exact extracted_word_flags_without_assume index romWord below1024
  have below256 : (memAlignRomMessage row).flags.val < 256 := by
    rw [packed, flagExpression] at below512 ⊢
    omega
  rw [romEq] at below256
  have shape := extracted_readWord_prove_shape index romWord below256
  have offsetEq : (rowOfIndex index).offset = row.offset :=
    (congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.offset romEq).symm
  have pcEq : (rowOfIndex index).pc = row.pc :=
    (congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.pc romEq).symm
  have deltaEq : (rowOfIndex index).deltaPc = row.delta_pc :=
    (congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.deltaPc romEq).symm
  have addressDeltaEq : (rowOfIndex index).deltaAddr = row.delta_addr :=
    (congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.deltaAddr romEq).symm
  have resetZero : row.reset = 0 := by
    apply Fin.ext
    change row.reset.val = 0
    rw [packed, flagExpression] at below512
    omega
  rw [offsetEq, pcEq, deltaEq, addressDeltaEq] at shape
  exact ⟨noAssume.1, noAssume.2, shape.1, shape.2.1, shape.2.2.1,
    shape.2.2.2.1, shape.2.2.2.2, resetZero⟩



private def rowAt (table : Table FGL) (index : Fin table.length) : MemAlignRow FGL :=
  rowInputOfEnvironment (table.environmentAt index)

private theorem rowAt_input (table : Table FGL) (index : Fin table.length) :
    rowAt table index = rowInputOfEnvironment (table.environmentAt index) := rfl

private theorem rowAt_spec {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = component) (index : Fin table.length) :
    Spec (rowAt table index) := by
  have actual := trace.spec_holds table member
    (table.table.get ⟨index.val, by simpa only [Table.table_length] using index.isLt⟩)
    (List.get_mem _ _)
  rw [componentEq] at actual
  change Spec (rowAt table index) at actual
  exact actual

private theorem rowAt_rom {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = component) (index : Fin table.length) :
    memAlignRomTable.Spec (memAlignRomMessage (rowAt table index)) := by
  have actual := memAlignRomTable_spec_of_memAlign_row trace.witness
    trace.constraints_hold trace.channels_balanced member componentEq
    (show table.table.get
      ⟨index.val, by simpa only [Table.table_length] using index.isLt⟩ ∈ table.table from
      List.get_mem _ _)
  simpa only [memAlign_eval_input, rowAt, Table.environmentAt] using actual

private theorem table_first_of_fixed (table : Table FGL)
    (columns : IndexedFixedColumns FGL table.component.rawWidth)
    (fixed : table.component.fixedColumns = some columns) (positive : 0 < table.length) :
    table.table.get ⟨0, by simpa only [Table.table_length] using positive⟩ =
      columns.materialize 0 (table.rawRows.get ⟨0, positive⟩) := by
  have materialized :
      table.table = table.rawRows.mapIdx (fun index raw => columns.materialize index raw) := by
    unfold Table.table
    rw [fixed]
  simp only [materialized, List.get_eq_getElem, List.getElem_mapIdx]

private theorem memAlign_message_width (row : MemAlignRow FGL) :
    (memBusMessage row).width = row.width := rfl

private theorem memAlign_message_read (row : MemAlignRow FGL) (read : row.wr = 0) :
    (memBusMessage row).mem_op = 1 := by
  change row.wr + 1 = 1
  rw [read, zero_add]

private theorem rowAt_boot (table : Table FGL)
    (componentEq : table.component = component) (positive : 0 < table.length) :
    (rowAt table ⟨0, positive⟩).preL1 = 1 := by
  have materialized :
      table.table.get ⟨0, by simpa only [Table.table_length] using positive⟩ =
        memAlignFixedColumns.materialize 0 (table.rawRows.get ⟨0, positive⟩) := by
    cases table with
    | mk tableComponent rawRows data uniform fixedDomain =>
        change tableComponent = component at componentEq
        subst tableComponent
        exact table_first_of_fixed
          ⟨component, rawRows, data, uniform, fixedDomain⟩ memAlignFixedColumns rfl positive
  have environmentEq : table.environmentAt ⟨0, positive⟩ =
      Environment.fromArray
        (memAlignFixedColumns.materialize 0 (table.rawRows.get ⟨0, positive⟩)) table.data :=
    congrArg table.environment materialized
  have transported := congrArg rowInputOfEnvironment environmentEq
  have inputEq := (rowAt_input table ⟨0, positive⟩).trans transported
  have evaluation :
      eval (Environment.fromArray
          (memAlignFixedColumns.materialize 0 (table.rawRows.get ⟨0, positive⟩)) table.data)
        (varFromOffset (F := FGL) MemAlignRow 0) =
        rowInputOfEnvironment (Environment.fromArray
          (memAlignFixedColumns.materialize 0 (table.rawRows.get ⟨0, positive⟩)) table.data) :=
    eval_varFromOffset_valueFromOffset MemAlignRow 0 _
  have projection := congrArg MemAlignRow.preL1 inputEq
  have evaluatedProjection := congrArg MemAlignRow.preL1 evaluation
  exact projection.trans (evaluatedProjection.symm.trans
    (eval_memAlignFixedColumns_L1_boot table.data (table.rawRows.get ⟨0, positive⟩)))

/-- A real general-MemAlign word-read provider owns a real PRECEDING
word-read pull, at pointer minus its positive offset. This uses the original
accepted table's boot fixed column, exact ROM predecessor classification,
D1 address continuity and D3 cyclic successor. No replay/order premise is
introduced; timestamps are deliberately not equated. -/
theorem wordRead_provider_preceding_pull
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = component) (index : Fin table.length)
    (word : (rowAt table index).width = 8)
    (read : (rowAt table index).wr = 0)
    (nonpull : (rowAt table index).sel_prove -
      ((rowAt table index).sel_up_to_down + (rowAt table index).sel_down_to_up) ≠ -1) :
    ∃ previous : Fin table.length,
      (rowAt table previous).width = 8 ∧ (rowAt table previous).wr = 0 ∧
        (rowAt table previous).sel_prove -
          ((rowAt table previous).sel_up_to_down + (rowAt table previous).sel_down_to_up) = -1 ∧
        1 ≤ (rowAt table index).offset.val ∧ (rowAt table index).offset.val ≤ 7 ∧
        (memBusMessage (rowAt table previous)).ptr + (rowAt table index).offset =
          (memBusMessage (rowAt table index)).ptr := by
  have specification := rowAt_spec trace member componentEq index
  have rom := rowAt_rom trace member componentEq index
  generalize currentEq : rowAt table index = current at specification rom word read nonpull ⊢
  obtain ⟨upZero, downZero, offsetLow, offsetHigh, pcMember, deltaPc, deltaAddr, resetZero⟩ :=
    wordRead_provider_shape current specification rom word read nonpull
  have pcNonzero : current.pc ≠ 0 := by
    intro zero
    simp [zero] at pcMember
  have positive : 0 < index.val := by
    by_contra notPositive
    have zero : index.val = 0 := by omega
    have atZero : index = ⟨0, Nat.zero_lt_of_lt index.isLt⟩ := Fin.ext zero
    have boot := rowAt_boot table componentEq (Nat.zero_lt_of_lt index.isLt)
    rw [← atZero, currentEq] at boot
    have bootPc := specification.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [boot, one_mul] at bootPc
    exact pcNonzero bootPc
  let previous : Fin table.length := ⟨index.val - 1, by omega⟩
  have successor : table.successorIndex previous = index := by
    apply Fin.ext
    simp only [Table.successorIndex, previous]
    have step : index.val - 1 + 1 = index.val := by omega
    rw [step, Nat.mod_eq_of_lt index.isLt]
  have previousRom := trace.memAlignRomMembership member componentEq previous
  rw [Table.successorEnvironment, successor] at previousRom
  change memAlignRomTable.Spec
    (memAlignRomSuccessorMessage (rowAt table previous) (rowAt table index)) at previousRom
  rw [currentEq] at previousRom
  have previousSpec := rowAt_spec trace member componentEq previous
  generalize previousEq : rowAt table previous = preceding at previousSpec previousRom
  obtain ⟨romIndex, romEq⟩ := previousRom
  have enters : ((rowOfIndex romIndex).pc + (rowOfIndex romIndex).deltaPc).val ∈
      ({101, 104, 107, 110, 116, 122, 131} : Finset Nat) := by
    rw [← romEq]
    have enterPc : preceding.pc + (current.pc - preceding.pc) = current.pc := by ring
    simpa only [memAlignRomSuccessorMessage, enterPc] using pcMember
  obtain ⟨_, previousOffset, previousWidth, _, flagsLow, flagsHigh⟩ :=
    extracted_readWord_predecessor_shape romIndex enters
  have offsetEq : preceding.offset = (rowOfIndex romIndex).offset :=
    congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.offset romEq
  have widthEq : preceding.width = (rowOfIndex romIndex).width :=
    congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.width romEq
  have flagsEq : (memAlignRomMessage preceding).flags = (rowOfIndex romIndex).flags :=
    by
      simpa only [memAlignRomMessage, memAlignRomSuccessorMessage] using
        (congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.flags romEq)
  obtain ⟨packed, low, wrBound, resetBound, upBound, downBound⟩ :=
    flagNat_facts preceding previousSpec
  have flagsValue : (rowOfIndex romIndex).flags.val = flagNat preceding := by
    rw [← flagsEq]
    exact packed
  rw [flagsValue] at flagsLow flagsHigh
  dsimp only [flagNat] at flagsLow flagsHigh
  have readZero : preceding.wr = 0 := by
    apply Fin.ext
    change preceding.wr.val = 0
    omega
  have previousUp : preceding.sel_up_to_down = 1 := by
    apply Fin.ext
    change preceding.sel_up_to_down.val = 1
    omega
  have previousDown : preceding.sel_down_to_up = 0 := by
    apply Fin.ext
    change preceding.sel_down_to_up.val = 0
    omega
  have proveZero : preceding.sel_prove = 0 := by
    have disjoint := previousSpec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simpa [previousUp, previousDown] using disjoint
  have addressTransition := trace.transitions_hold table member index
  rw [componentEq] at addressTransition
  change transitionRows (rowAt table previous) (rowAt table index) at addressTransition
  rw [previousEq, currentEq] at addressTransition
  have addresses : current.addr = preceding.addr := by
    have equation := addressTransition.1
    rw [deltaAddr, resetZero] at equation
    linear_combination -equation
  refine ⟨previous, ?_⟩
  rw [previousEq]
  refine ⟨widthEq.trans previousWidth, readZero, ?_, offsetLow, offsetHigh, ?_⟩
  · simp [proveZero, previousUp, previousDown]
  · simp only [memBusMessage, offsetEq.trans previousOffset, addresses]
    ring

private theorem support_closed_of_absent {n : Nat} (trace : AcceptedZiskTrace n)
    (absent : ¬ MutableMemPresent trace.witness) :
    ∀ x ∈ actualAlignmentSupport trace,
      ∃ y ∈ actualAlignmentSupport trace, ∃ distance : Nat,
        1 ≤ distance ∧ distance ≤ 7 ∧ y + (distance : FGL) = x := by
  classical
  intro x member
  simp only [actualAlignmentSupport, List.mem_toFinset, alignmentPointers,
    List.mem_flatMap] at member
  obtain ⟨table, tableMember, member⟩ := member
  by_cases componentEq : table.component = component
  · rw [if_pos componentEq, List.mem_map] at member
    obtain ⟨raw, rawSelected, pointerEq⟩ := member
    rw [List.mem_filter] at rawSelected
    obtain ⟨rawMember, selected⟩ := rawSelected
    obtain ⟨rawIndex, rawEq⟩ := List.mem_iff_get.mp rawMember
    let index : Fin table.length :=
      ⟨rawIndex.val, by simpa only [Table.table_length] using rawIndex.isLt⟩
    have environmentEq : table.environmentAt index = table.environment raw := by
      simpa only [Table.environmentAt, index, rawEq]
    have valueEq : rowAt table index =
        eval (table.environment raw) component.rowInputVar := by
      rw [memAlign_eval_input]
      exact congrArg rowInputOfEnvironment environmentEq
    have selectedFacts :
        (rowAt table index).width = 8 ∧ (rowAt table index).wr = 0 ∧
          (rowAt table index).sel_prove -
            ((rowAt table index).sel_up_to_down + (rowAt table index).sel_down_to_up) ≠ 0 ∧
          (rowAt table index).sel_prove -
            ((rowAt table index).sel_up_to_down + (rowAt table index).sel_down_to_up) ≠ -1 := by
      rw [valueEq]
      simpa only [wordReadProviderFilter, decide_eq_true_eq] using selected
    obtain ⟨previous, word, read, active, gapLow, gapHigh, edge⟩ :=
      wordRead_provider_preceding_pull trace tableMember componentEq index
        selectedFacts.1 selectedFacts.2.1 selectedFacts.2.2.2
    let previousRaw : Array FGL := table.table.get
      ⟨previous.val, by simpa only [Table.table_length] using previous.isLt⟩
    have previousMember : previousRaw ∈ table.table := List.get_mem _ _
    let v := component.rowInputVar
    let message := memBusMessageExpr v
    let mult := v.sel_prove - selAssumeExpr v
    let interaction := ((MemBusChannel.emitted mult message).toRaw).eval
      (table.environment previousRaw)
    have roster : table.component.operations.interactionsWith MemBusChannel.toRaw =
        [((MemBusChannel.emitted mult message).toRaw)] := by
      rw [componentEq]
      exact component_interactionsWith_memBus
    have interactionMember : interaction ∈ table.interactionsWith MemBusChannel.toRaw := by
      simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
        roster, List.map_cons, List.map_nil, List.mem_flatMap, List.mem_singleton]
      exact ⟨previousRaw, previousMember, rfl⟩
    have previousValue :
        eval (table.environment previousRaw) component.rowInputVar = rowAt table previous := by
      rw [memAlign_eval_input]
      rfl
    have activeInteraction : interaction.mult = -1 := by
      change Expression.eval (table.environment previousRaw) mult = -1
      have eqMult : Expression.eval (table.environment previousRaw) mult =
          (rowAt table previous).sel_prove -
            ((rowAt table previous).sel_up_to_down + (rowAt table previous).sel_down_to_up) := by
        have evaluated := memAlign_eval_mult (table.environment previousRaw) v
        change Expression.eval (table.environment previousRaw) mult = _ at evaluated
        rw [previousValue] at evaluated
        exact evaluated
      exact eqMult.trans active
    have typedMessage : eval (table.environment previousRaw) message =
        memBusMessage (rowAt table previous) := by
      simp only [message, v, eval_memBusMessageExpr, previousValue]
    have readOp : (eval (table.environment previousRaw) message).mem_op = 1 := by
      exact (congrArg MemBusMessage.mem_op typedMessage).trans
        (memAlign_message_read _ read)
    have wordOp : (eval (table.environment previousRaw) message).width = 8 := by
      exact (congrArg MemBusMessage.width typedMessage).trans
        ((memAlign_message_width _).trans word)
    rcases wordRead_pull_provider trace tableMember previousMember interactionMember
      (requestMult := mult) (requestMessage := message) rfl
      activeInteraction readOp wordOp with present | provider
    · exact False.elim (absent present)
    · rw [typedMessage] at provider
      refine ⟨(memBusMessage (rowAt table previous)).ptr, provider,
        (rowAt table index).offset.val, gapLow, gapHigh, ?_⟩
      rw [Fin.cast_val_eq_self]
      rw [← pointerEq, ← valueEq]
      exact edge
  · simp [if_neg componentEq] at member

/-- Actual accepted balance and complete provider/ROM/index analysis force
mutable Mem from any real active word-eight read pull. No chronology or
read-value assumption and no support-size premise enter this theorem. -/
theorem wordRead_pull_present
    {n : Nat} (trace : AcceptedZiskTrace n)
    {requestTable : Table FGL} (tableMember : requestTable ∈ trace.witness.allTables)
    {requestRow : Array FGL} (rowMember : requestRow ∈ requestTable.table)
    {request : Interaction FGL}
    (interactionMember : request ∈ requestTable.interactionsWith MemBusChannel.toRaw)
    {requestMult : Expression FGL} {requestMessage : MemBusMessage (Expression FGL)}
    (evaluated : request.msg = (((MemBusChannel.emitted requestMult requestMessage).toRaw).eval
      (requestTable.environment requestRow)).msg)
    (active : request.mult = -1)
    (readOp : (eval (requestTable.environment requestRow) requestMessage).mem_op = 1)
    (word : (eval (requestTable.environment requestRow) requestMessage).width = 8) :
    MutableMemPresent trace.witness := by
  by_contra absent
  rcases wordRead_pull_provider trace tableMember rowMember interactionMember
    (requestMult := requestMult) (requestMessage := requestMessage)
    evaluated active readOp word with present | provider
  · exact absent present
  · exact actualAlignmentSupport_not_closed trace ⟨_, provider⟩
      (support_closed_of_absent trace absent)


private theorem present_of_wordRead_row {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = component) (index : Fin table.length)
    (word : (rowAt table index).width = 8) (read : (rowAt table index).wr = 0)
    (active : (rowAt table index).sel_prove -
      ((rowAt table index).sel_up_to_down + (rowAt table index).sel_down_to_up) = -1) :
    MutableMemPresent trace.witness := by
  let raw := table.table.get
    ⟨index.val, by simpa only [Table.table_length] using index.isLt⟩
  have rawMember : raw ∈ table.table := List.get_mem _ _
  let v := component.rowInputVar
  let message := memBusMessageExpr v
  let mult := v.sel_prove - selAssumeExpr v
  let interaction := ((MemBusChannel.emitted mult message).toRaw).eval (table.environment raw)
  have roster : table.component.operations.interactionsWith MemBusChannel.toRaw =
      [((MemBusChannel.emitted mult message).toRaw)] := by
    rw [componentEq]
    exact component_interactionsWith_memBus
  have interactionMember : interaction ∈ table.interactionsWith MemBusChannel.toRaw := by
    simp only [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
      roster, List.map_cons, List.map_nil, List.mem_flatMap, List.mem_singleton]
    exact ⟨raw, rawMember, rfl⟩
  have value : eval (table.environment raw) component.rowInputVar = rowAt table index := by
    rw [memAlign_eval_input]
    rfl
  have activeInteraction : interaction.mult = -1 := by
    change Expression.eval (table.environment raw) mult = -1
    have evaluated := memAlign_eval_mult (table.environment raw) v
    change Expression.eval (table.environment raw) mult = _ at evaluated
    rw [value] at evaluated
    exact evaluated.trans active
  have typed : eval (table.environment raw) message = memBusMessage (rowAt table index) := by
    simp only [message, v, eval_memBusMessageExpr, value]
  apply wordRead_pull_present trace member rawMember interactionMember
    (requestMult := mult) (requestMessage := message) rfl activeInteraction
  · exact (congrArg MemBusMessage.mem_op typed).trans
      (memAlign_message_read _ read)
  · exact (congrArg MemBusMessage.width typed).trans
      ((memAlign_message_width _).trans word)

private theorem extracted_zero_width_padding :
    ∀ i : Fin tableSize, (rowOfIndex i).width = 0 →
      (rowOfIndex i).pc = 0 ∧ (rowOfIndex i).deltaPc = 0 ∧
        (rowOfIndex i).flags = 512 := by
  decide +kernel

private theorem extracted_initial_wordRead :
    ∀ i : Fin tableSize, (rowOfIndex i).pc = 0 → (rowOfIndex i).width ≠ 0 →
      (rowOfIndex i).width = 8 ∧ 1536 ≤ (rowOfIndex i).flags.val ∧
        (rowOfIndex i).flags.val < 1792 := by
  decide +kernel

/-- Every nonpadding row in a real accepted MemAlign table has some actual
word-eight read pull at or before it. Padding cannot jump into a program:
this is derived from the full ROM and the cyclic source PC relation. -/
private theorem wordRead_row_of_nonzero_width {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = component) (index : Fin table.length)
    (nonpadding : (rowAt table index).width ≠ 0) :
    ∃ previous : Fin table.length, (rowAt table previous).width = 8 ∧
      (rowAt table previous).wr = 0 ∧
      (rowAt table previous).sel_prove -
        ((rowAt table previous).sel_up_to_down + (rowAt table previous).sel_down_to_up) = -1 := by
  have find (k : Nat) : ∀ current : Fin table.length, current.val = k →
      (rowAt table current).width ≠ 0 →
      ∃ previous : Fin table.length, (rowAt table previous).width = 8 ∧
        (rowAt table previous).wr = 0 ∧
        (rowAt table previous).sel_prove -
          ((rowAt table previous).sel_up_to_down + (rowAt table previous).sel_down_to_up) = -1 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro current currentEq nonzeroWidth
        have specification := rowAt_spec trace member componentEq current
        have rom := rowAt_rom trace member componentEq current
        generalize valueEq : rowAt table current = currentRow at specification rom nonzeroWidth
        by_cases pcZero : currentRow.pc = 0
        · obtain ⟨romIndex, romEq⟩ := rom
          have romPc : (rowOfIndex romIndex).pc = 0 := by
            rw [← romEq]
            exact pcZero
          have romWidth : (rowOfIndex romIndex).width ≠ 0 := by
            rw [← romEq]
            exact nonzeroWidth
          obtain ⟨width, flagsLow, flagsHigh⟩ :=
            extracted_initial_wordRead romIndex romPc romWidth
          have widthEq : currentRow.width = (rowOfIndex romIndex).width :=
            congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.width romEq
          have flagsEq : (memAlignRomMessage currentRow).flags =
              (rowOfIndex romIndex).flags :=
            congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.flags romEq
          obtain ⟨packed, low, wrBound, resetBound, upBound, downBound⟩ :=
            flagNat_facts currentRow specification
          have flagsValue : (rowOfIndex romIndex).flags.val = flagNat currentRow := by
            rw [← flagsEq]
            exact packed
          rw [flagsValue] at flagsLow flagsHigh
          dsimp only [flagNat] at flagsLow flagsHigh
          have read : currentRow.wr = 0 := by
            apply Fin.ext
            change currentRow.wr.val = 0
            omega
          have up : currentRow.sel_up_to_down = 1 := by
            apply Fin.ext
            change currentRow.sel_up_to_down.val = 1
            omega
          have down : currentRow.sel_down_to_up = 0 := by
            apply Fin.ext
            change currentRow.sel_down_to_up.val = 0
            omega
          have prove : currentRow.sel_prove = 0 := by
            have disjoint := specification.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            simpa [up, down] using disjoint
          refine ⟨current, ?_⟩
          rw [valueEq]
          exact ⟨widthEq.trans width, read, by simp [prove, up, down]⟩
        · have positive : 0 < current.val := by
            by_contra notPositive
            have zero : current.val = 0 := by omega
            have atZero : current = ⟨0, Nat.zero_lt_of_lt current.isLt⟩ := Fin.ext zero
            have boot := rowAt_boot table componentEq (Nat.zero_lt_of_lt current.isLt)
            rw [← atZero, valueEq] at boot
            have bootPc := specification.2.2.2.2.2.2.2.2.2.2.2.2.1
            rw [boot, one_mul] at bootPc
            exact pcZero bootPc
          let previous : Fin table.length := ⟨current.val - 1, by omega⟩
          have successor : table.successorIndex previous = current := by
            apply Fin.ext
            simp only [Table.successorIndex, previous]
            have step : current.val - 1 + 1 = current.val := by omega
            rw [step, Nat.mod_eq_of_lt current.isLt]
          have predecessorRom := trace.memAlignRomMembership member componentEq previous
          rw [Table.successorEnvironment, successor] at predecessorRom
          change memAlignRomTable.Spec
            (memAlignRomSuccessorMessage (rowAt table previous) (rowAt table current))
            at predecessorRom
          rw [valueEq] at predecessorRom
          generalize previousEq : rowAt table previous = previousRow at predecessorRom
          obtain ⟨romIndex, romEq⟩ := predecessorRom
          have previousNonzero : previousRow.width ≠ 0 := by
            intro widthZero
            have romWidth : (rowOfIndex romIndex).width = 0 := by
              rw [← romEq]
              exact widthZero
            obtain ⟨oldPc, delta, _⟩ := extracted_zero_width_padding romIndex romWidth
            have oldPcEq : previousRow.pc = (rowOfIndex romIndex).pc :=
              congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.pc romEq
            have deltaEq : currentRow.pc - previousRow.pc = (rowOfIndex romIndex).deltaPc :=
              congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.deltaPc romEq
            rw [oldPcEq, oldPc, delta, sub_zero] at deltaEq
            exact pcZero deltaEq
          apply ih previous.val (by dsimp only [previous]; omega) previous rfl
          rw [previousEq]
          exact previousNonzero
  exact find index.val index rfl nonpadding

/-- A genuine nonpadding row of the accepted general MemAlign table forces
mutable Mem. This includes narrow and store programs; no such alternative is
excluded or mistaken for the mutable-Mem provider itself. -/
theorem present_of_memAlign_nonzero_width {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = component) (index : Fin table.length)
    (nonpadding : (rowAt table index).width ≠ 0) :
    MutableMemPresent trace.witness := by
  obtain ⟨previous, word, read, active⟩ :=
    wordRead_row_of_nonzero_width trace member componentEq index nonpadding
  exact present_of_wordRead_row trace member componentEq previous word read active

/-- Every actual read-byte provider row contains its real aligned word pull.
This is the live two-interaction roster, not an excluded provider alternative. -/
theorem present_of_memAlignReadByte_row {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = ZiskFv.AirsClean.MemAlignReadByte.component)
    {raw : Array FGL} (rawMember : raw ∈ table.table) :
    MutableMemPresent trace.witness := by
  let v := ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar
  let message := ZiskFv.AirsClean.MemAlignReadByte.memReadMessageExpr v
  let interaction := ((MemBusChannel.pulled message).toRaw).eval (table.environment raw)
  have interactionMember : interaction ∈ table.interactionsWith MemBusChannel.toRaw := by
    apply List.mem_flatMap.mpr
    refine ⟨raw, rawMember, ?_⟩
    rw [Operations.interactionValuesWith_eq_map, componentEq,
      ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl rfl
  apply wordRead_pull_present trace member rawMember interactionMember
    (requestMult := -1) (requestMessage := message) rfl (by rfl)
  · rw [memBusMessage_eval_mem_op]
    rfl
  · rw [memBus_eval_width]
    rfl

/-- The read/write byte provider also has an unconditional actual word-read
pull, regardless of its selected-byte result's read/write polarity. -/
theorem present_of_memAlignByte_row {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (member : table ∈ trace.witness.allTables)
    (componentEq : table.component = ZiskFv.AirsClean.MemAlignByte.component)
    {raw : Array FGL} (rawMember : raw ∈ table.table) :
    MutableMemPresent trace.witness := by
  let v := ZiskFv.AirsClean.MemAlignByte.component.rowInputVar
  let message := ZiskFv.AirsClean.MemAlignByte.memReadMessageExpr v
  let interaction := ((MemBusChannel.pulled message).toRaw).eval (table.environment raw)
  have interactionMember : interaction ∈ table.interactionsWith MemBusChannel.toRaw := by
    apply List.mem_flatMap.mpr
    refine ⟨raw, rawMember, ?_⟩
    rw [Operations.interactionValuesWith_eq_map, componentEq,
      ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl rfl
  apply wordRead_pull_present trace member rawMember interactionMember
    (requestMult := -1) (requestMessage := message) rfl (by rfl)
  · rw [memBusMessage_eval_mem_op]
    rfl
  · rw [memBus_eval_width]
    rfl


/-- Complete provider closure for a REAL nonzero-width data-memory pull in
the same accepted witness and fully source-bound committed ROM. Read and
store polarity are both covered; no MemAlign/native/Main provider alternative
is omitted, and no selected replay-row membership is assumed. -/
theorem data_pull_present
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : RawProgramBinding.ProgramRowsBinding trace start addr rawProgram)
    {requestTable : Table FGL} (tableMember : requestTable ∈ trace.witness.allTables)
    {requestRow : Array FGL} (rowMember : requestRow ∈ requestTable.table)
    {request : Interaction FGL}
    (interactionMember : request ∈ requestTable.interactionsWith MemBusChannel.toRaw)
    {requestMult : Expression FGL} {requestMessage : MemBusMessage (Expression FGL)}
    (evaluated : request = ((MemBusChannel.emitted requestMult requestMessage).toRaw).eval
      (requestTable.environment requestRow))
    (active : request.mult = -1)
    (dataOp : (eval (requestTable.environment requestRow) requestMessage).mem_op = 1 ∨
      (eval (requestTable.environment requestRow) requestMessage).mem_op = 2)
    (widthOrStore : (eval (requestTable.environment requestRow) requestMessage).width ≠ 0 ∨
      (eval (requestTable.environment requestRow) requestMessage).mem_op = 2) :
    MutableMemPresent trace.witness := by
  have coverage := (activeMainMemProviderRowMatchSpec_of_active_main_eval
    trace.witness trace.channels_balanced trace.spec_holds tableMember rowMember
    interactionMember evaluated active (multiplicity := (-1)) («as» := 2)).2
  rcases activeMainMemProviderRowMatchSpec_mutable_or_nonmutable coverage with
    mutable | nonmutable
  · exact present_of_mutable_provider mutable
  · rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases nonmutable with
      readByte | byte | general | main | boundary
    · rcases readByte with
        ⟨_, _, _, _, _, table, member, _, raw, rawMember, _, componentEq, _, _⟩
      exact present_of_memAlignReadByte_row trace member componentEq rawMember
    · rcases byte with
        ⟨_, _, _, _, _, table, member, _, raw, rawMember, _, componentEq, _, _⟩
      exact present_of_memAlignByte_row trace member componentEq rawMember
    · rcases general with
        ⟨provider, _, sameMessage, _, _, table, member, _, raw, rawMember,
          _, componentEq, providerEval, _⟩
      have rawEq : provider.msg =
          (((MemBusChannel.emitted requestMult requestMessage).toRaw).eval
            (requestTable.environment requestRow)).msg := by
        rw [← evaluated]
        exact sameMessage
      rw [providerEval] at rawEq
      have typed := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_msg := rawEq)
      rw [eval_memBusMessageExpr] at typed
      obtain ⟨rawIndex, rawEq⟩ := List.mem_iff_get.mp rawMember
      let index : Fin table.length :=
        ⟨rawIndex.val, by simpa only [Table.table_length] using rawIndex.isLt⟩
      have environmentEq : table.environmentAt index = table.environment raw := by
        simpa only [Table.environmentAt, index, rawEq]
      have valueEq : rowAt table index = eval (table.environment raw) component.rowInputVar := by
        rw [memAlign_eval_input]
        exact congrArg rowInputOfEnvironment environmentEq
      apply present_of_memAlign_nonzero_width trace member componentEq index
      have specification := rowAt_spec trace member componentEq index
      have rom := rowAt_rom trace member componentEq index
      generalize actualEq : rowAt table index = current at valueEq specification rom ⊢
      have sourceMessage := congrArg memBusMessage valueEq
      have concreteTyped := sourceMessage.trans typed
      have widths := congrArg MemBusMessage.width concreteTyped
      change current.width = (eval (requestTable.environment requestRow) requestMessage).width
        at widths
      intro zero
      rcases widthOrStore with nonzeroWidth | storeOp
      · exact nonzeroWidth (widths.symm.trans zero)
      · obtain ⟨romIndex, romEq⟩ := rom
        have romWidth : (rowOfIndex romIndex).width = 0 := by
          rw [← romEq]
          exact zero
        have padding := (extracted_zero_width_padding romIndex romWidth).2.2
        have flagsEq : (memAlignRomMessage current).flags = 512 :=
          (congrArg ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.flags romEq).trans padding
        obtain ⟨packed, low, wrBound, resetBound, upBound, downBound⟩ :=
          flagNat_facts current specification
        have natFlags : flagNat current = 512 := by
          rw [← packed, flagsEq]
          rfl
        dsimp only [flagNat] at natFlags
        have read : current.wr = 0 := by
          apply Fin.ext
          change current.wr.val = 0
          omega
        have opcodes := congrArg MemBusMessage.mem_op concreteTyped
        change current.wr + 1 =
          (eval (requestTable.environment requestRow) requestMessage).mem_op at opcodes
        rw [read, storeOp, zero_add] at opcodes
        exact (by decide : (1 : FGL) ≠ 2) opcodes
    · rcases dataOp with read | store
      · exact False.elim (not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one
          trace.constraints_hold evaluated read main)
      · exact False.elim (SourceFlags.not_main_store_provider trace start addr rawProgram binding
          evaluated store main)
    · exact False.elim (SourceFlags.not_boundary_data_provider trace evaluated dataOp boundary)

/-- These are definitional omissions, not a proposed weakened validator. -/
theorem row_spec_step_free (row : MemAlignRow FGL) (timestamp : FGL) :
    Spec { row with step := timestamp } ↔ Spec row := Iff.rfl

theorem predecessor_step_free (previous current : MemAlignRow FGL) (a b : FGL) :
    transitionRows { previous with step := a } { current with step := b } ↔
      transitionRows previous current := Iff.rfl

theorem cyclic_successor_step_free (current successor : MemAlignRow FGL) (a b : FGL) :
    cyclicSuccessorTransitionRows { current with step := a } { successor with step := b } ↔
      cyclicSuccessorTransitionRows current successor := Iff.rfl

theorem rom_message_step_free (row : MemAlignRow FGL) (timestamp : FGL) :
    memAlignRomMessage { row with step := timestamp } = memAlignRomMessage row := rfl

/-- Exact extracted ROM rows 1 and 2: pc 0 -> 1 -> 0, one aligned read
followed by one byte proof. All value/register columns are zero. -/
def readByteAssume (timestamp : FGL) : MemAlignRow FGL :=
  memAlignRowOf .upToDown true false true
    true false false false false false false false
    0 0 0 0 0 0 0 0
    0 0 8 timestamp 0 1 0

def readByteProve (timestamp : FGL) : MemAlignRow FGL :=
  memAlignRowOf .prove false false false
    true false false false false false false false
    0 0 0 0 0 0 0 0
    0 0 1 timestamp 0 (-1) 1

/-- Both actual local Specs, both predecessor edges, and both cyclic successor
edges hold for ARBITRARY, independently chosen timestamps. -/
theorem readByteProgram_source_relations (readStep proveStep : FGL) :
    Spec (readByteAssume readStep) ∧ Spec (readByteProve proveStep) ∧
      transitionRows (readByteAssume readStep) (readByteProve proveStep) ∧
      transitionRows (readByteProve proveStep) (readByteAssume readStep) ∧
      cyclicSuccessorTransitionRows (readByteAssume readStep) (readByteProve proveStep) ∧
      cyclicSuccessorTransitionRows (readByteProve proveStep) (readByteAssume readStep) := by
  norm_num [Spec, transitionRows, cyclicSuccessorTransitionRows,
    readByteAssume, readByteProve, memAlignRowOf, memAlignValue0Of,
    memAlignValue1Of, memAlignLane]

/-- This is membership in the actual extracted static table, not a handwritten
ROM validator, guessed phase exclusion, or assumed table lookup. -/
theorem readByteAssume_rom (timestamp : FGL) :
    memAlignRomTable.Spec (memAlignRomMessage (readByteAssume timestamp)) := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  norm_num [memAlignRomMessage, readByteAssume, memAlignRowOf, rowOfIndex] <;>
    decide +kernel

theorem readByteProve_rom (timestamp : FGL) :
    memAlignRomTable.Spec (memAlignRomMessage (readByteProve timestamp)) := by
  refine ⟨⟨2, by decide⟩, ?_⟩
  norm_num [memAlignRomMessage, readByteProve, memAlignRowOf, rowOfIndex] <;>
    decide +kernel

/-- The fixed boot bit and declared value/byte range conditions do not repair
the timestamp omission. All bytes and both 32-bit value columns are zero. -/
theorem readByteProgram_fixed_and_ranges (readStep proveStep : FGL) :
    (readByteAssume readStep).preL1 = 1 ∧ (readByteProve proveStep).preL1 = 0 ∧
      (readByteAssume readStep).value_0.val < 2 ^ 32 ∧
      (readByteAssume readStep).value_1.val < 2 ^ 32 ∧
      (readByteProve proveStep).value_0.val < 2 ^ 32 ∧
      (readByteProve proveStep).value_1.val < 2 ^ 32 ∧
      (readByteAssume readStep).reg_0 = 0 ∧
      (readByteAssume readStep).reg_1 = 0 ∧
      (readByteAssume readStep).reg_2 = 0 ∧
      (readByteAssume readStep).reg_3 = 0 ∧
      (readByteAssume readStep).reg_4 = 0 ∧
      (readByteAssume readStep).reg_5 = 0 ∧
      (readByteAssume readStep).reg_6 = 0 ∧
      (readByteAssume readStep).reg_7 = 0 ∧
      (readByteProve proveStep).reg_0 = 0 ∧
      (readByteProve proveStep).reg_1 = 0 ∧
      (readByteProve proveStep).reg_2 = 0 ∧
      (readByteProve proveStep).reg_3 = 0 ∧
      (readByteProve proveStep).reg_4 = 0 ∧
      (readByteProve proveStep).reg_5 = 0 ∧
      (readByteProve proveStep).reg_6 = 0 ∧
      (readByteProve proveStep).reg_7 = 0 := by
  norm_num [readByteAssume, readByteProve, memAlignRowOf,
    memAlignValue0Of, memAlignValue1Of, memAlignLane]

/-- Exact source polarity and timestamp, before replay interpretation. The
aligned request is a pull; the byte result is a push with a separately free
step. No sign reinterpretation manufactures a memory write. -/
theorem readByteProgram_messages (readStep proveStep : FGL) :
    (readByteAssume readStep).sel_prove -
        ((readByteAssume readStep).sel_up_to_down +
          (readByteAssume readStep).sel_down_to_up) = -1 ∧
      (readByteProve proveStep).sel_prove -
        ((readByteProve proveStep).sel_up_to_down +
          (readByteProve proveStep).sel_down_to_up) = 1 ∧
      (memBusMessage (readByteAssume readStep)).mem_op = 1 ∧
      (memBusMessage (readByteAssume readStep)).width = 8 ∧
      (memBusMessage (readByteAssume readStep)).timestamp = readStep ∧
      (memBusMessage (readByteProve proveStep)).mem_op = 1 ∧
      (memBusMessage (readByteProve proveStep)).width = 1 ∧
      (memBusMessage (readByteProve proveStep)).timestamp = proveStep := by
  norm_num [memBusMessage, readByteAssume, readByteProve, memAlignRowOf]

/-- Small exact failed entailment: all preceding local source/ROM/transition
facts admit an aligned read timestamp strictly AFTER its byte proof. This is
not a full ensemble accepted construction and does not refute presence. -/
theorem readByteProgram_reversed_timestamps :
    (memBusMessage (readByteProve 2)).timestamp.val <
      (memBusMessage (readByteAssume 9)).timestamp.val := by
  decide

end AlignmentChronology

open RawProgramBinding RomDecodeBinding CanonicalSyntaxBoundary

private theorem present_of_source_load
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram) (i : Fin n)
    (selected : (mainRowWithRomLd trace i).rom.b_src_ind = 1)
    (width : (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 0) :
    MutableMemPresent trace.witness := by
  have rowMember : loadBMemMainRow trace i ∈ trace.mainTable.table :=
    List.mem_iff_get.mpr ⟨⟨i.val, trace.mainTable_index i⟩, rfl⟩
  have rowEval : eval (trace.mainTable.environment (loadBMemMainRow trace i))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar =
      mainRowWithRomLd trace i := by
    simpa [loadBMemMainRow, mainRowWithRomLd] using
      (mainTableRowAtOrZero_get trace.program trace.mainTable
        ⟨i.val, trace.mainTable_index i⟩).symm
  have sourceSum := SourceFlags.main_b_ind_sum trace start addr rawProgram binding
    trace.mainTable_mem trace.mainTable_component rowMember (by rw [rowEval]; exact selected)
  have fieldActive :
      -((mainRowWithRomLd trace i).rom.b_src_mem +
        (mainRowWithRomLd trace i).rom.b_src_ind +
        (mainRowWithRomLd trace i).rom.b_src_reg) = (-1 : FGL) := by
    rw [rowEval] at sourceSum
    rw [sourceSum]
  have active : (loadBMemMainInteraction trace i).mult = -1 := by
    change Expression.eval (trace.mainTable.environment (loadBMemMainRow trace i))
      (loadBMemMainMultiplicity trace) = -1
    rw [loadBMemMainMultiplicity]
    change (-1 : FGL) * Expression.eval
      (trace.mainTable.environment (loadBMemMainRow trace i)) _ = -1
    have scalarSum :
        Expression.eval (trace.mainTable.environment (loadBMemMainRow trace i))
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.b_src_mem +
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.b_src_ind +
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.b_src_reg) =
          (mainRowWithRomLd trace i).rom.b_src_mem + (mainRowWithRomLd trace i).rom.b_src_ind +
            (mainRowWithRomLd trace i).rom.b_src_reg := by
      simpa only [rowEval] using ZiskFv.AirsClean.Main.eval_bSourceSumExpr
        (trace.mainTable.environment (loadBMemMainRow trace i))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    rw [scalarSum]
    simpa only [neg_mul, one_mul] using fieldActive
  have interactionMember : loadBMemMainInteraction trace i ∈
      trace.mainTable.interactionsWith MemBusChannel.toRaw := by
    simpa [loadBMemMainInteraction, loadBMemMainRow, loadBMemMainMessage] using
      mainRowWithRomLd_bMemInteraction_mem trace i
  have messageEval :
      eval (trace.mainTable.environment (loadBMemMainRow trace i)) (loadBMemMainMessage trace) =
        ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i) := by
    rw [loadBMemMainMessage, ZiskFv.AirsClean.Main.eval_bMemMessageExpr, rowEval]
  apply AlignmentChronology.data_pull_present trace start addr rawProgram binding
    trace.mainTable_mem rowMember interactionMember rfl active
  · left
    rw [messageEval]
    exact mainRowWithRomLd_bMemMessage_mem_op_eq_one_of_active trace i selected fieldActive
  · left
    rw [messageEval]
    simpa only [ZiskFv.AirsClean.Main.bMemMessage, selected, one_mul, sub_add_cancel,
      mainOfTable_ind_width, mainRowWithRomLd] using width

private theorem present_of_source_store
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram) (i : Fin n)
    (selected : (mainRowWithRomSt trace i).rom.store_ind = 1) :
    MutableMemPresent trace.witness := by
  have rowMember : storeCMemMainRow trace i ∈ trace.mainTable.table :=
    List.mem_iff_get.mpr ⟨⟨i.val, trace.mainTable_index i⟩, rfl⟩
  have rowEval : eval (trace.mainTable.environment (storeCMemMainRow trace i))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar =
      mainRowWithRomSt trace i := by
    simpa [storeCMemMainRow, mainRowWithRomSt] using
      (mainTableRowAtOrZero_get trace.program trace.mainTable
        ⟨i.val, trace.mainTable_index i⟩).symm
  have sourceSum := SourceFlags.main_store_ind_sum trace start addr rawProgram binding
    trace.mainTable_mem trace.mainTable_component rowMember (by rw [rowEval]; exact selected)
  have fieldActive :
      -((mainRowWithRomSt trace i).rom.store_mem +
        (mainRowWithRomSt trace i).rom.store_ind +
        (mainRowWithRomSt trace i).rom.store_reg) = (-1 : FGL) := by
    rw [rowEval] at sourceSum
    rw [sourceSum]
  have active : (storeCMemMainInteraction trace i).mult = -1 := by
    change Expression.eval (trace.mainTable.environment (storeCMemMainRow trace i))
      (storeCMemMainMultiplicity trace) = -1
    rw [storeCMemMainMultiplicity]
    change (-1 : FGL) * Expression.eval
      (trace.mainTable.environment (storeCMemMainRow trace i)) _ = -1
    have scalarSum :
        Expression.eval (trace.mainTable.environment (storeCMemMainRow trace i))
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.store_mem +
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.store_ind +
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.store_reg) =
          (mainRowWithRomSt trace i).rom.store_mem + (mainRowWithRomSt trace i).rom.store_ind +
            (mainRowWithRomSt trace i).rom.store_reg := by
      simpa only [rowEval] using ZiskFv.AirsClean.Main.eval_cSourceSumExpr
        (trace.mainTable.environment (storeCMemMainRow trace i))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
    rw [scalarSum]
    simpa only [neg_mul, one_mul] using fieldActive
  have interactionMember : storeCMemMainInteraction trace i ∈
      trace.mainTable.interactionsWith MemBusChannel.toRaw := by
    simpa [storeCMemMainInteraction, storeCMemMainRow, storeCMemMainMessage] using
      mainRowWithRomSt_cMemInteraction_mem trace i
  have messageEval :
      eval (trace.mainTable.environment (storeCMemMainRow trace i)) (storeCMemMainMessage trace) =
        ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace i) := by
    rw [storeCMemMainMessage, ZiskFv.AirsClean.Main.eval_cMemMessageExpr, rowEval]
  have storeOp : (eval (trace.mainTable.environment (storeCMemMainRow trace i))
      (storeCMemMainMessage trace)).mem_op = 2 := by
    rw [messageEval]
    exact mainRowWithRomSt_cMemMessage_mem_op_eq_two_of_active trace i selected fieldActive
  exact AlignmentChronology.data_pull_present trace start addr rawProgram binding
    trace.mainTable_mem rowMember interactionMember rfl active (Or.inr storeOp) (Or.inr storeOp)

/-- A real decoded memory-emitting source head forces mutable Mem. This
uses source-bound selectors, not an old seed's presence callback or arbitrary
Core.mem membership. All seven loads and all four stores are included. -/
theorem present_of_memoryRowsOfStep_nonempty
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram) (i : Fin n)
    (step : ZiskStep trace i) (decoded : RowDecode trace i step)
    (nonempty : memoryRowsOfStep trace i step ≠ []) :
    MutableMemPresent trace.witness := by
  cases step <;> simp [memoryRowsOfStep] at nonempty
  all_goals first
    | exact present_of_source_load trace start addr rawProgram binding i
        decoded.h_b_src_ind (by rw [decoded.h_width]; decide)
    | exact present_of_source_store trace start addr rawProgram binding i decoded.h_store_ind

/-- SAME CheckedSyntax and ORIGINAL Accepted n: nonempty architectural SOURCE
memory rows force actual mutable-Mem presence. The heads are computed, not a
caller map; no total auxiliary step family or P=n retarget is used. Thus final
width-two ownership and old P=n+1 endpoints do not invent a memory operation.
This is presence ONLY, not chronological read evidence or RMW discharge. -/
theorem present_of_checked_source_nonempty
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (checked : CheckedSyntax trace start addr rawProgram)
    (nonempty : (List.finRange checked.count).flatMap
      (fun i => memoryRowsOfStep trace (checked.index i) (checked.steps i)) ≠ []) :
    MutableMemPresent trace.witness := by
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨i, _, entryMember⟩ := List.mem_flatMap.mp member
  apply present_of_memoryRowsOfStep_nonempty trace start addr rawProgram binding
    (checked.index i) (checked.steps i) (checked.decoded binding i)
  intro empty
  rw [empty] at entryMember
  simp at entryMember


namespace AlignmentArity

open ZiskFv.AirsClean.MemAlign
open ZiskFv.AirsClean.MemAlignRomTable

/-- The genuine three-row word-read ROM path 0 -> 101 -> 102 -> 0.
Only the prove multiplicity is variable; the eight bytes remain zero. -/
def wordReadFirst : MemAlignRow FGL :=
  memAlignRowOf .upToDown true false true
    false true true true true true true true
    0 0 0 0 0 0 0 0
    0 0 8 2 0 101 0

def wordReadProve (multiplicity : FGL) : MemAlignRow FGL :=
  { memAlignRowOf .prove false false false
      false true false false false false false false
      0 0 0 0 0 0 0 0
      0 1 8 2 0 1 101 with sel_prove := multiplicity }

def wordReadLast : MemAlignRow FGL :=
  memAlignRowOf .downToUp false false false
    true false false false false false false false
    0 0 0 0 0 0 0 0
    1 0 8 2 1 (-102) 102

/-- Neither the full local Spec nor either source transition family makes
`sel_prove` a Boolean or forces the word-count arity to be negative. -/
theorem wordReadProgram_source_relations (multiplicity : FGL) :
    Spec wordReadFirst ∧ Spec (wordReadProve multiplicity) ∧ Spec wordReadLast ∧
      transitionRows wordReadFirst (wordReadProve multiplicity) ∧
      transitionRows (wordReadProve multiplicity) wordReadLast ∧
      transitionRows wordReadLast wordReadFirst ∧
      cyclicSuccessorTransitionRows wordReadFirst (wordReadProve multiplicity) ∧
      cyclicSuccessorTransitionRows (wordReadProve multiplicity) wordReadLast ∧
      cyclicSuccessorTransitionRows wordReadLast wordReadFirst := by
  norm_num [Spec, transitionRows, cyclicSuccessorTransitionRows,
    wordReadFirst, wordReadProve, wordReadLast, memAlignRowOf,
    memAlignValue0Of, memAlignValue1Of, memAlignLane]

theorem wordReadFirst_rom :
    memAlignRomTable.Spec (memAlignRomMessage wordReadFirst) := by
  refine ⟨⟨101, by decide⟩, ?_⟩
  change ({ pc := 0, deltaPc := 101, deltaAddr := 0, offset := 0, width := 8, flags := 1790 } :
    ZiskFv.Channels.MemAlignRom.MemAlignRomMessage FGL) = rowOfIndex ⟨101, by decide⟩
  simp only [rowOfIndex, ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.mk.injEq] <;>
    decide +kernel

theorem wordReadProve_rom (multiplicity : FGL) :
    memAlignRomTable.Spec (memAlignRomMessage (wordReadProve multiplicity)) := by
  refine ⟨⟨102, by decide⟩, ?_⟩
  norm_num [memAlignRomMessage, wordReadProve, memAlignRowOf, rowOfIndex] <;>
    decide +kernel

theorem wordReadLast_rom :
    memAlignRomTable.Spec (memAlignRomMessage wordReadLast) := by
  refine ⟨⟨103, by decide⟩, ?_⟩
  change ({ pc := 102, deltaPc := -102, deltaAddr := 1, offset := 0, width := 8, flags := 2049 } :
    ZiskFv.Channels.MemAlignRom.MemAlignRomMessage FGL) = rowOfIndex ⟨103, by decide⟩
  simp only [rowOfIndex, ZiskFv.Channels.MemAlignRom.MemAlignRomMessage.mk.injEq] <;>
    decide +kernel

private def emissionMultiplicity (row : MemAlignRow FGL) : FGL :=
  row.sel_prove - (row.sel_up_to_down + row.sel_down_to_up)

/-- All THREE interactions have read opcode and width eight. Their literal
FGL multiplicity sum is `multiplicity - 2`, not automatically `-1`.
These are raw source requests, not signed legacy replay writes. -/
theorem wordReadProgram_polarity_and_sum (multiplicity : FGL) :
    (memBusMessage wordReadFirst).mem_op = 1 ∧
      (memBusMessage (wordReadProve multiplicity)).mem_op = 1 ∧
      (memBusMessage wordReadLast).mem_op = 1 ∧
      (memBusMessage wordReadFirst).width = 8 ∧
      (memBusMessage (wordReadProve multiplicity)).width = 8 ∧
      (memBusMessage wordReadLast).width = 8 ∧
      emissionMultiplicity wordReadFirst +
        emissionMultiplicity (wordReadProve multiplicity) +
        emissionMultiplicity wordReadLast = multiplicity - 2 := by
  simp [memBusMessage, emissionMultiplicity, wordReadFirst, wordReadProve,
    wordReadLast, memAlignRowOf]
  ring

/-- Exact failure of the proposed always-negative word-eight arity invariant.
The program's local source and exact ROM facts above hold also at multiplicity
three, where the word-eight count is PLUS ONE. This does not assert channel
balance or absence of mutable Mem in a complete accepted ensemble. -/
theorem wordReadProgram_positive_word_count :
    emissionMultiplicity wordReadFirst +
      emissionMultiplicity (wordReadProve 3) +
      emissionMultiplicity wordReadLast = 1 := by
  decide

end AlignmentArity

end ZiskFv.Compliance.SourceMutableMemoryPresence
