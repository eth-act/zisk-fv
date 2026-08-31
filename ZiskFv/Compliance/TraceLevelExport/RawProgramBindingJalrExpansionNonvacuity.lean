import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingControl
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.JalrRows
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification

/-!
# Raw JALR-expansion program binding non-vacuity

Every `ProgramRowsBinding` witness built so far (`singleAddProgramRowsBinding`,
`memoryProgramRowsBinding`, `addFaithfulProgramRowsBinding`) uses raw words whose
production lowering is a single physical ROM row, so the `some row` EXPANSION
branch of `ProgramRowsBinding` (`RawProgramBinding.lean:169-195`) has never been
exercised by a concrete witness. This module builds one: an all-empty execution
trace (`numInstructions = 0`, following the `RawProgramBindingMemoryNonvacuity`
pattern) that still commits a real, faithful two-row JALR-expansion ROM image —
the intermediate ADD row and terminal AND row the production extractor emits for
an unaligned JALR (`rawIType imm rs1 0 rd 0x67` with `imm % 4 ≠ 0`, the same
encoding family `RawProgramBindingJalr.lean`'s `jalr_raw_rows` handles).

This deliberately does NOT reuse `ZiskFv.Compliance.JalrSpinWitness.jalrAcceptedTrace`:
that witness's committed rows are hand-authored placeholders that do not match the
real production lowering (issue #334). Here the committed rows are *defined* as
`romRowOf` applied to the real extracted rows, so faithfulness holds by
construction, not by a separate equality proof.

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure.
-/

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks
open Air.Flat
open ZiskFv.Compliance.Extraction
  (defCtx decode_i_bounds decode_extract_ok from_inst_full_fields jalr_ok
   jalr_production_expanded_row_pins)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-! ## The raw JALR word and its two-row production lowering. -/

/-- `rd = 1`, `rs1 = 2` (both nonzero), `imm = 1` (not a multiple of 4, so the
    production extractor cannot statically prove the target is 4-aligned and
    always emits the unaligned two-row expansion — the intermediate ADD row
    followed by the terminal AND row). -/
def jalrExpansionRaw : BitVec 32 :=
  ZiskFv.Completeness.Rv64imShapes.rawIType 1 2 0 1 0x67

/-- The production extractor lowers `jalrExpansionRaw` to exactly two physical
    ROM rows. This mirrors the "unaligned" branch of `RawProgramBindingJalr`'s
    private `jalr_raw_rows`, specialized to a concrete word and stated only for
    the row-count fact this module needs (not the full ADD/AND field pins). -/
theorem jalrExpansionRaw_row_count :
    ∃ rows : aeneas_extract.Rv64imTranspileRowsExtract,
      aeneas_extract.extract_transpile_rv64im_rows_raw
          (ZiskFv.Compliance.Decode.toU32 jalrExpansionRaw) = ok rows ∧
      rows.row_count = 2#u32 := by
  unfold jalrExpansionRaw
  set raw := ZiskFv.Completeness.Rv64imShapes.rawIType 1 2 0 1 0x67 with hrawdef
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (ZiskFv.Compliance.Decode.toU32 raw) =
      aeneas_extract.rv64im_decode.decode_i
        (ZiskFv.Compliance.Decode.toU32 raw)
          aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false := by
    simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift,
      Bind.bind, bind_ok, ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode 1 2 0 1 0x67 (by norm_num)]
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ :=
    decode_i_bounds (ZiskFv.Compliance.Decode.toU32 raw)
      aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok decoded := hdec.trans hdecoded
  let input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm }
  obtain ⟨ctx, hctx⟩ := jalr_ok { defCtx with extract_marker := () } input
    (by simpa only [input] using hrs1b) (by simpa only [input] using hrdb) rfl
  have hpins := jalr_production_expanded_row_pins input ctx
    (by simpa only [input] using hrdb) (by simpa only [input] using hrs1b) hctx
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  have hdext' := hdext
  unfold aeneas_extract.decode_extract_from_decoded at hdext'
  obtain ⟨_, _, hdext'⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdext'
  obtain ⟨_, _, hdext'⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdext'
  obtain ⟨_, _, hdext'⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hdext'
  rw [Result.ok.injEq] at hdext'
  have hdextimm : dext.imm = decoded.imm := by rw [← hdext']
  have hdextrd : dext.rd = decoded.rd := by rw [← hdext']
  have hdextrs1 : dext.rs1 = decoded.rs1 := by rw [← hdext']
  have hdextrs2 : dext.rs2 = decoded.rs2 := by rw [← hdext']
  have himm : input.imm.bv = BitVec.signExtend 32 (BitVec.ofNat 12 1) :=
    decode_i_rawIType_imm 1 2 0 1 0x67 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) aeneas_extract.rv64im_decode.RiscvOpcode.Jalr decoded
        (by simpa only [raw] using hdecoded)
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false =
        .ok { ctx with extract_marker := () } := by
    change (do
      let s ← riscv2zisk_context.Riscv2ZiskContext.jalr
        { defCtx with extract_marker := () } input 4#u64
      .ok { s with extract_marker := () }) = _
    rw [hctx]
    rfl
  rcases hpins with haligned | hunaligned
  · exfalso
    obtain ⟨hrem0, _, _⟩ := haligned
    have himmEq : input.imm = (1#i32 : Std.I32) := by
      apply IScalar.eq_of_val_eq
      show input.imm.bv.toInt = (1#i32 : Std.I32).val
      rw [himm]
      decide
    rw [himmEq] at hrem0
    have hrem1 : (1#i32 : Std.I32) % 4#i32 = ok 1#i32 := rfl
    rw [hrem1] at hrem0
    simp at hrem0
  · obtain ⟨rem, hrem, hrem0, first, last, hfirst, hlast, hfirstPins, hlastPins⟩ := hunaligned
    obtain ⟨lastRow, hfrom, haSrc, haHi, haLo, hbSrc, hbHi, hbLo, hwidth,
      hop, hstore, hstoreOffset, hj1, hj2, hsetpc, hstorepc, hieo, hm32⟩ :=
      from_inst_full_fields last.i
    let terminal : aeneas_extract.Rv64imTranspileExtract :=
      { accepted := true, decode := dext, row := lastRow }
    have hterminal :
        aeneas_extract.extract_transpile_rv64im_raw
            (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal := by
      rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
      simp only [bind_ok, Bind.bind, hdext, hopd]
      change (do
        let input' ← riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
          decoded.rd decoded.rs1 decoded.rs2 decoded.imm
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input' riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      simp only [riscv2zisk_single_row.Rv64imLoweringInput.new]
      change (do
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      rw [hlower]
      simp only [Bind.bind]
      simp only [hlast, core.option.Option.unwrap, Result.ofOption, bind_ok]
      rw [hfrom]
      rfl
    let rows : aeneas_extract.Rv64imTranspileRowsExtract :=
      { accepted := true, decode := dext, row_count := 2#u32,
        first_row := first, last_row := lastRow }
    refine ⟨rows, ?_, rfl⟩
    unfold aeneas_extract.extract_transpile_rv64im_rows_raw
    rw [hterminal]
    simp only [ZiskFv.Compliance.Decode.toU32_and127]
    have hremval : rem.val ≠ 0 := by
      intro hz
      apply hrem0
      apply IScalar.eq_of_val_eq
      simpa using hz
    have hinputNew :
        riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64 decoded.rd
            decoded.rs1 decoded.rs2 decoded.imm = .ok input := rfl
    have hremDecoded :
        (decoded.imm % 4#i32 : Result Std.I32) = Result.ok rem := by
      simpa only [input] using hrem
    norm_num [terminal, raw, hdextrd, hdextrs1, hdextrs2, hdextimm, hrem,
      hremDecoded, hremval, lift, Bind.bind, hinputNew, hlower, hfirst, rows,
      core.option.Option.unwrap, Result.ofOption]
    rw [if_pos (by decide)]
    simp only [defCtx] at hlower
    rw [hlower]
    simp [hfirst]

/-- The chosen production two-row extraction witness for `jalrExpansionRaw`. -/
noncomputable def jalrExpansionRows : aeneas_extract.Rv64imTranspileRowsExtract :=
  jalrExpansionRaw_row_count.choose

theorem jalrExpansionRows_spec :
    aeneas_extract.extract_transpile_rv64im_rows_raw
        (ZiskFv.Compliance.Decode.toU32 jalrExpansionRaw) = ok jalrExpansionRows ∧
    jalrExpansionRows.row_count = 2#u32 :=
  jalrExpansionRaw_row_count.choose_spec

/-! ## The committed two-row ROM image: the JALR expansion at consecutive lines. -/

/-- Line `0`: 4-aligned, and `0 + 1 < GL_prime`, as required by
    `ProgramRowsBinding`. -/
def jalrExpansionLine : FGL := 0

/-- Row 0 is *defined* as `romRowOf` applied to the production extractor's real
    first (ADD) row — faithful by construction, not by a separate equality
    lemma. -/
noncomputable def jalrExpansionRow0 : ZiskRomMessage FGL :=
  romRowOf jalrExpansionLine jalrExpansionRows.first_row

/-- Row 1 (line `L + 1`, immediately after row 0) is *defined* as `romRowOf`
    applied to the production extractor's real terminal (AND) row. -/
noncomputable def jalrExpansionRow1 : ZiskRomMessage FGL :=
  romRowOf (jalrExpansionLine + 1) jalrExpansionRows.last_row

noncomputable def jalrExpansionProgram : Program 2
  | ⟨0, _⟩ => jalrExpansionRow0
  | ⟨1, _⟩ => jalrExpansionRow1

/-- `romMessagesOfRaw` at `jalrExpansionLine` on `jalrExpansionRaw` returns
    exactly the two committed rows, since the production extractor's row count
    is `2#u32` (`jalrExpansionRows_spec`). -/
theorem jalrExpansionRows_messages :
    romMessagesOfRaw jalrExpansionLine jalrExpansionRaw =
      (jalrExpansionRow0, some jalrExpansionRow1) := by
  obtain ⟨hextract, hcount⟩ := jalrExpansionRows_spec
  simp [romMessagesOfRaw, hextract, hcount, jalrExpansionRow0, jalrExpansionRow1]

private def jalrExpansionEmptyData : ProverData FGL := fun _ _ => #[]

private noncomputable def jalrExpansionWitness :
    EnsembleWitness (fullRv64imEnsemble 2 jalrExpansionProgram).ensemble :=
  EnsembleWitness.ofRows (fullRv64imEnsemble 2 jalrExpansionProgram).ensemble
    jalrExpansionEmptyData () (fun _ => [])
    (by intro i row hrow; simp at hrow)
    (by intro i columns hcolumns; simp)

private theorem jalrExpansionWitness_verifier :
    (fullRv64imEnsemble 2 jalrExpansionProgram).ensemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 2 jalrExpansionProgram).verifier_empty

private theorem jalrExpansionWitness_mutable_tables_empty (table : Table FGL)
    (hmem : table ∈ jalrExpansionWitness.allTables)
    (hcomp : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · exfalso
    rw [hv, EnsembleWitness.verifierTable_component] at hcomp
    have hvnil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 2
        jalrExpansionProgram
    rw [hcomp,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at hvnil
    exact absurd hvnil (by simp)
  · simp only [jalrExpansionWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [EnsembleWitness.tableAt, Table.table]
    split <;> rfl

private theorem jalrExpansionWitness_not_mutableMemPresent :
    ¬ MutableMemPresent jalrExpansionWitness := by
  intro hpresent
  obtain ⟨table, hmem, hcomp, hlen⟩ := hpresent
  have htable := jalrExpansionWitness_mutable_tables_empty table hmem hcomp
  exact absurd hlen (by simp [htable])

private theorem jalrExpansionWitness_constraints : jalrExpansionWitness.Constraints := by
  refine jalrExpansionWitness.constraints_of_tables jalrExpansionWitness_verifier ?_
  intro t ht
  simp only [jalrExpansionWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
  obtain ⟨i, rfl⟩ := ht
  simp [Air.Flat.Table.Constraints, EnsembleWitness.tableAt, Table.table]
  split <;> simp

private theorem jalrExpansionWitness_balanced : jalrExpansionWitness.BalancedChannels := by
  refine jalrExpansionWitness.balancedChannels_of_tables jalrExpansionWitness_verifier ?_
  intro channel _
  have hnil : jalrExpansionWitness.tables.flatMap (·.interactionsWith channel) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro t ht
    simp only [jalrExpansionWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [Air.Flat.Table.interactionsWith, EnsembleWitness.tableAt, Table.table]
    split <;> simp
  rw [hnil]
  exact balancedInteractions_of_present (Or.symm (Nat.eq_zero_or_pos _)) []
    (by simp) (by simp)

private theorem jalrExpansionWitness_transitions : jalrExpansionWitness.TransitionConstraints := by
  intro table hmem
  rw [Table.TransitionConstraints]
  intro index
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hverifier | htable
  · subst table
    simp [EnsembleWitness.verifierTable]
  · simp only [jalrExpansionWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at htable
    obtain ⟨i, rfl⟩ := htable
    change Fin 0 at index
    exact Fin.elim0 index

private theorem jalrExpansionWitness_cyclic :
    jalrExpansionWitness.CyclicSuccessorTransitionConstraints := by
  intro table hmem
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hverifier | htable
  · subst table
    simp [EnsembleWitness.verifierTable]
  · simp only [jalrExpansionWitness, EnsembleWitness.ofRows_tables, List.mem_ofFn] at htable
    obtain ⟨i, rfl⟩ := htable
    change Fin 0 at index
    exact Fin.elim0 index

noncomputable def jalrExpansionAcceptedTrace : AcceptedZiskTrace 0 where
  programLength := 2
  program := jalrExpansionProgram
  witness := jalrExpansionWitness
  constraints_hold := jalrExpansionWitness_constraints
  channels_balanced := jalrExpansionWitness_balanced
  mem_replay_table := fun h => absurd h jalrExpansionWitness_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h jalrExpansionWitness_not_mutableMemPresent
  transitions_hold := jalrExpansionWitness_transitions
  cyclic_successor_transitions_hold := jalrExpansionWitness_cyclic
  main_height := by intro table _ _ i; exact i.elim0

/-! ## The `ProgramRowsBinding` witness, exercising the expansion branch. -/

def jalrExpansionAddr : Fin 1 → FGL := fun _ => jalrExpansionLine

def jalrExpansionRawProgram : Fin 1 → BitVec 32 := fun _ => jalrExpansionRaw

/-- The sole raw word's first physical row is the ROM image's row `0`. -/
def jalrExpansionStart : Fin 1 → Fin jalrExpansionAcceptedTrace.programLength :=
  fun _ => ⟨0, by decide⟩

theorem jalrExpansionProgramRowsBinding :
    ProgramRowsBinding jalrExpansionAcceptedTrace jalrExpansionStart jalrExpansionAddr
      jalrExpansionRawProgram := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' h
    fin_cases k ; fin_cases k' ; revert h ; decide
  · intro k
    fin_cases k ; decide
  · intro k
    fin_cases k ; decide
  · intro k k' h
    fin_cases k ; fin_cases k' ; exact absurd h (by decide)
  · intro k
    fin_cases k
    simp only [jalrExpansionStart, jalrExpansionAddr, jalrExpansionRawProgram]
    rw [jalrExpansionRows_messages]
    exact ⟨rfl, by decide, rfl⟩
  · intro j
    fin_cases j
    · exact ⟨⟨0, by decide⟩, Or.inl rfl⟩
    · refine ⟨⟨0, by decide⟩, Or.inr ⟨jalrExpansionRow1, ?_, rfl⟩⟩
      simp only [jalrExpansionAddr, jalrExpansionRawProgram]
      rw [jalrExpansionRows_messages]

#print axioms jalrExpansionProgramRowsBinding

end ZiskFv.Compliance.RawProgramBinding
