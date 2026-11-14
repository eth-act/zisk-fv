import ZiskFv.Compliance.TraceLevelExport.RawProgramBinding
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.JalrRows

/-!
# Successful production row lowering

The row domain here is the successful, accepted result of the production rows
extractor, not an opcode-based width estimate. Source: ZisK `9ca88b5`,
`core/src/aeneas_extract.rs:361-412`, extracted in
`trust/aeneas/ProductionM2.lean:3694-3786`.

These certificates do not assert that every accepted execution has a successful
raw-word lowering, nor that its physical Main rows match the extracted rows.
Those are separate program/execution obligations.
-/

namespace ZiskFv.Compliance

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction
open ZiskFv.Compliance.RawProgramBinding

/-- An actual successful, accepted production lowering. Extraction failures and
rejected words cannot inhabit this type. -/
structure SuccessfulRowLowering (raw : BitVec 32) where
  rows : aeneas_extract.Rv64imTranspileRowsExtract
  source : aeneas_extract.extract_transpile_rv64im_rows_raw
    (ZiskFv.Compliance.Decode.toU32 raw) = .ok rows
  accepted : rows.accepted = true

namespace SuccessfulRowLowering

/-- Invert the actual source computation, retaining its terminal result and, in
its expanded arm, the successful second lowering and first-row extraction.
The one-row arm retains the source's non-JALR/aligned disjunction; it is not a
one-row default for an unsuccessful extraction. -/
theorem source_cases {raw : BitVec 32} (lowering : SuccessfulRowLowering raw) :
    ∃ terminal : aeneas_extract.Rv64imTranspileExtract,
      aeneas_extract.extract_transpile_rv64im_raw
        (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal ∧
      terminal.accepted = true ∧
      lowering.rows.decode = terminal.decode ∧
      lowering.rows.last_row = terminal.row ∧
      ((lowering.rows.row_count = 1#u32 ∧
          lowering.rows.first_row = terminal.row ∧
          ((ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32 ∨
            (terminal.decode.imm % 4#i32) = (Result.ok (0#i32) : Result Std.I32))) ∨
        (lowering.rows.row_count = 2#u32 ∧
          (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) = 103#u32 ∧
          ∃ (remainder : Std.I32)
              (input : riscv2zisk_single_row.Rv64imLoweringInput)
              (ctx : riscv2zisk_context.Riscv2ZiskContext),
            (terminal.decode.imm % 4#i32) = (Result.ok remainder : Result Std.I32) ∧
            remainder ≠ 0#i32 ∧
            riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
              terminal.decode.rd terminal.decode.rs1 terminal.decode.rs2
              terminal.decode.imm = .ok input ∧
            riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
              defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false =
                .ok ctx ∧
            core.option.Option.unwrap ctx.extract_first_inst =
              .ok lowering.rows.first_row)) := by
  obtain ⟨rows, hsource, hrowsAccepted⟩ := lowering
  unfold aeneas_extract.extract_transpile_rv64im_rows_raw at hsource
  obtain ⟨terminal, hterminal, hsource⟩ := bind_eq_ok_imp hsource
  simp only [lift, Bind.bind, bind_ok] at hsource
  split at hsource
  · rename_i htag
    split at hsource
    · rename_i haccepted
      obtain ⟨remainder, hrem, hsource⟩ := bind_eq_ok_imp hsource
      split at hsource
      · rename_i hnonzero
        obtain ⟨input, hinput, hsource⟩ := bind_eq_ok_imp hsource
        obtain ⟨ctx, hctx, hsource⟩ := bind_eq_ok_imp hsource
        obtain ⟨first, hfirst, hsource⟩ := bind_eq_ok_imp hsource
        rw [Result.ok.injEq] at hsource
        subst rows
        refine ⟨terminal, hterminal, haccepted, rfl, rfl,
          Or.inr ⟨rfl, htag, remainder, input, ctx, hrem, ?_, hinput, hctx, hfirst⟩⟩
        simpa using hnonzero
      · rename_i hzero
        have hremzero : remainder = 0#i32 := by
          apply IScalar.val_eq_imp
          simpa using hzero
        rw [Result.ok.injEq] at hsource
        subst rows
        exact ⟨terminal, hterminal, haccepted, rfl, rfl,
          Or.inl ⟨rfl, rfl, Or.inr (hrem.trans (congrArg Result.ok hremzero))⟩⟩
    · rw [Result.ok.injEq] at hsource
      subst rows
      simp at hrowsAccepted
  · rename_i htag
    rw [Result.ok.injEq] at hsource
    subst rows
    exact ⟨terminal, hterminal, hrowsAccepted, rfl, rfl,
      Or.inl ⟨rfl, rfl, Or.inl htag⟩⟩

/-- The physical width is read only from the successful production result. -/
def width {raw : BitVec 32} (lowering : SuccessfulRowLowering raw) : Nat :=
  lowering.rows.row_count.val

/-- Source control flow returns exactly one or two rows. -/
theorem count {raw : BitVec 32} (lowering : SuccessfulRowLowering raw) :
    lowering.rows.row_count.val = 1 ∨ lowering.rows.row_count.val = 2 := by
  obtain ⟨_, _, _, _, _, hcases⟩ := lowering.source_cases
  rcases hcases with ⟨hcount, _⟩ | ⟨hcount, _⟩
  · exact Or.inl (congrArg UScalar.val hcount)
  · exact Or.inr (congrArg UScalar.val hcount)

theorem width_pos {raw : BitVec 32} (lowering : SuccessfulRowLowering raw) :
    0 < lowering.width := by
  rcases lowering.count with h | h <;> simp [width, h]

theorem first_eq_last_of_width_one {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (hwidth : lowering.width = 1) :
    lowering.rows.first_row = lowering.rows.last_row := by
  obtain ⟨_, _, _, _, hlast, hcases⟩ := lowering.source_cases
  rcases hcases with ⟨_, hfirst, _⟩ | ⟨hcount, _⟩
  · exact hfirst.trans hlast.symm
  · norm_num [width, hcount, UScalar.val] at hwidth

/-- A non-JALR tag implies width one only after source success and acceptance
have been supplied by `lowering`. -/
theorem width_one_of_non_jalr {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw)
    (hnon : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32) :
    lowering.width = 1 := by
  obtain ⟨_, _, _, _, _, hcases⟩ := lowering.source_cases
  rcases hcases with ⟨hcount, _⟩ | ⟨_, htag, _⟩
  · exact congrArg UScalar.val hcount
  · exact (hnon htag).elim

/-- For an actual successful JALR, alignment is the source's signed-immediate
remainder computation, not target-PC alignment or an opcode-based estimate. -/
theorem jalr_width_one_iff_aligned {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw)
    (hjalr : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) = 103#u32) :
    lowering.width = 1 ↔
      (lowering.rows.decode.imm % 4#i32) = (Result.ok (0#i32) : Result Std.I32) := by
  obtain ⟨terminal, _, _, hdecode, _, hcases⟩ := lowering.source_cases
  rw [hdecode]
  rcases hcases with ⟨hcount, _, hreason⟩ | ⟨hcount, _, rem, _, _, hrem, hne, _⟩
  · have haligned :
        (terminal.decode.imm % 4#i32) = (Result.ok (0#i32) : Result Std.I32) :=
      hreason.resolve_left (fun hnon => hnon hjalr)
    have hwidth : lowering.width = 1 := congrArg UScalar.val hcount
    exact ⟨fun _ => haligned, fun _ => hwidth⟩
  · have hwidth : lowering.width = 2 := congrArg UScalar.val hcount
    constructor
    · intro h
      omega
    · intro h
      exact (hne (Result.ok.inj (hrem.symm.trans h))).elim

/-- Both possible JALR widths follow from the actual successful remainder
computation. A failed remainder computation is not interpreted as a width. -/
theorem jalr_width_of_remainder {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw)
    (hjalr : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) = 103#u32)
    (remainder : Std.I32)
    (hrem : (lowering.rows.decode.imm % 4#i32) =
      (Result.ok remainder : Result Std.I32)) :
    lowering.width = if remainder = 0#i32 then 1 else 2 := by
  by_cases hz : remainder = 0#i32
  · rw [if_pos hz]
    exact (lowering.jalr_width_one_iff_aligned hjalr).mpr
      (hrem.trans (congrArg Result.ok hz))
  · rw [if_neg hz]
    have hnotone : lowering.width ≠ 1 := by
      intro hone
      have hzero := (lowering.jalr_width_one_iff_aligned hjalr).mp hone
      exact hz (Result.ok.inj (hrem.symm.trans hzero))
    rcases lowering.count with h | h
    · exact (hnotone h).elim
    · exact h

/-- Exact first/optional-second correspondence for the existing serializer.
There is no failure arm here: the source equality selects its successful arm. -/
theorem serialized_rows {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (line : FGL) :
    romMessagesOfRaw line raw =
      (romRowOf line lowering.rows.first_row,
        if lowering.width = 2 then
          some (romRowOf (line + 1) lowering.rows.last_row) else none) := by
  obtain ⟨_, _, _, _, _, hcases⟩ := lowering.source_cases
  rcases hcases with ⟨hcount, hfirst, _⟩ | ⟨hcount, _⟩
  · have hsame := lowering.first_eq_last_of_width_one (congrArg UScalar.val hcount)
    simp [romMessagesOfRaw, lowering.source, hcount, width, hsame]
  · simp [romMessagesOfRaw, lowering.source, hcount, width]

theorem serialized_first {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (line : FGL) :
    (romMessagesOfRaw line raw).1 = romRowOf line lowering.rows.first_row := by
  exact congrArg Prod.fst (lowering.serialized_rows line)

theorem serialized_second {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (line : FGL) :
    (romMessagesOfRaw line raw).2 =
      if lowering.width = 2 then
        some (romRowOf (line + 1) lowering.rows.last_row) else none := by
  exact congrArg Prod.snd (lowering.serialized_rows line)

/-- The old serializer is exactly the terminal-row projection, including in the
expanded case, where it is not the first physical row. -/
theorem serialized_terminal {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (line : FGL) :
    romMessageOfRaw line raw = romRowOf line lowering.rows.last_row := by
  obtain ⟨_, hterminal, _, _, hlast, _⟩ := lowering.source_cases
  simp only [romMessageOfRaw, hterminal, hlast]

/-- The existing production JALR pin theorem applies to the first row selected
by source success. Register bounds are explicit here; no execution invariant
or raw-decode bound is smuggled into the lowering certificate. -/
theorem jalr_first_pins_of_width_two {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (hwidth : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32) :
    ∃ input : riscv2zisk_single_row.Rv64imLoweringInput,
      input.rd = lowering.rows.decode.rd ∧
      input.rs1 = lowering.rows.decode.rs1 ∧
      input.imm = lowering.rows.decode.imm ∧
      JalrUnalignedFirstRowPins input lowering.rows.first_row := by
  obtain ⟨terminal, _, _, hdecode, _, hcases⟩ := lowering.source_cases
  rcases hcases with ⟨hcount, _⟩ |
    ⟨_, _, rem, input, ctx, hrem, hne, hinput, hctx, hfirst⟩
  · norm_num [width, hcount, UScalar.val] at hwidth
  · have hinputEq :
        ({ rom_address := 0#u64, rd := terminal.decode.rd,
           rs1 := terminal.decode.rs1, rs2 := terminal.decode.rs2,
           imm := terminal.decode.imm } :
          riscv2zisk_single_row.Rv64imLoweringInput) = input :=
        Result.ok.inj hinput
    subst input
    change (do
      let ctx' ← riscv2zisk_context.Riscv2ZiskContext.jalr
        { defCtx with extract_marker := () }
        { rom_address := 0#u64, rd := terminal.decode.rd,
          rs1 := terminal.decode.rs1, rs2 := terminal.decode.rs2,
          imm := terminal.decode.imm } 4#u64
      .ok { ctx' with extract_marker := () }) = .ok ctx at hctx
    obtain ⟨actual, hactual, hctx⟩ := bind_eq_ok_imp hctx
    rw [Result.ok.injEq] at hctx
    subst ctx
    have hpins := jalr_production_expanded_row_pins _ actual
      (by simpa only [hdecode] using hrd)
      (by simpa only [hdecode] using hrs1) hactual
    rcases hpins with ⟨_, hnone, _⟩ |
      ⟨_, _, _, first, _, hsome, _, hpins, _⟩
    · simp [hnone, core.option.Option.unwrap, Result.ofOption] at hfirst
    · simp only [hsome, core.option.Option.unwrap, Result.ofOption] at hfirst
      have heq : first = lowering.rows.first_row := Result.ok.inj hfirst
      refine ⟨{
        rom_address := 0#u64
        rd := terminal.decode.rd
        rs1 := terminal.decode.rs1
        rs2 := terminal.decode.rs2
        imm := terminal.decode.imm }, ?_, ?_, ?_, ?_⟩
      · exact congrArg (fun d => d.rd) hdecode.symm
      · exact congrArg (fun d => d.rs1) hdecode.symm
      · exact congrArg (fun d => d.imm) hdecode.symm
      · exact heq ▸ hpins

/-- Source-grounded first-row store selectors. `store = 0` excludes both
architectural-register storage and either mutable-memory storage selector.
This is a row-shape fact, not yet an invariant of the physical execution's
register file or memory; that needs row/Main agreement and the corresponding
state-transition constraints. Source: `riscv2zisk_context.rs:1374-1419`;
selector meanings: `zisk_inst.rs:57-64`. -/
theorem jalr_first_no_write_selectors {raw : BitVec 32}
    (lowering : SuccessfulRowLowering raw) (hwidth : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32) :
    lowering.rows.first_row.store = 0#u64 ∧
      lowering.rows.first_row.store_pc = false ∧
      lowering.rows.first_row.set_pc = false ∧
      lowering.rows.first_row.store ≠ zisk_inst.STORE_REG ∧
      lowering.rows.first_row.store ≠ zisk_inst.STORE_MEM ∧
      lowering.rows.first_row.store ≠ zisk_inst.STORE_IND := by
  obtain ⟨_, _, _, _, hpins⟩ := lowering.jalr_first_pins_of_width_two hwidth hrd hrs1
  rcases hpins with ⟨_, _, _, _, _, _, _, _, _, hsetpc, hstorepc, hstore⟩
  refine ⟨hstore, hstorepc, hsetpc, ?_, ?_, ?_⟩ <;>
    simp [hstore, zisk_inst.STORE_REG, zisk_inst.STORE_MEM, zisk_inst.STORE_IND]

/-- Fail closed on rejected words and failed extraction. Width is subsequently
proved from source control flow, never inserted as a fallback. -/
noncomputable def check (raw : BitVec 32) : Option (SuccessfulRowLowering raw) :=
  match hsource : aeneas_extract.extract_transpile_rv64im_rows_raw
      (ZiskFv.Compliance.Decode.toU32 raw) with
  | .ok rows =>
      if haccepted : rows.accepted = true then
        some ⟨rows, hsource, haccepted⟩
      else none
  | _ => none

theorem check_complete {raw : BitVec 32} (lowering : SuccessfulRowLowering raw) :
    check raw = some lowering := by
  cases lowering with
  | mk rows hsource haccepted =>
      unfold check
      split
      · rename_i selected hselected
        have heq : selected = rows := Result.ok.inj (hselected.symm.trans hsource)
        subst selected
        simp [haccepted]
      · rename_i hselected
        exact False.elim (hselected rows hsource)

end SuccessfulRowLowering

/-! ## Closed successful source examples

These are bounded examples of the real production pipeline. They provide no
accepted-trace or physical-row agreement premise: composing them with an
execution still requires that separate evidence.
-/

set_option maxHeartbeats 8000000 in
private theorem sourceJalrTwo_exists :
    ∃ lowering : SuccessfulRowLowering (0x00208067#32), lowering.width = 2 := by
  let decoded : aeneas_extract.rv64im_decode.DecodedRv64im :=
    { opcode := .Jalr, format := .I, funct3 := 0#u32, funct7 := 0#u32,
      rd := 0#u32, rs1 := 1#u32, rs2 := 0#u32, imm := 2#i32,
      pred := 0#u32, succ := 0#u32 }
  -- Kernel reduction of the actual literal decoder, not a supplied decode.
  have hdecoded : aeneas_extract.rv64im_decode.decode_32_core
      (ZiskFv.Compliance.Decode.toU32 (0x00208067#32)) = .ok decoded := by
    rfl
  let input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm }
  obtain ⟨ctx, hctx⟩ := jalr_ok { defCtx with extract_marker := () } input
    (by decide) (by decide) rfl
  have hpins := jalr_production_expanded_row_pins input ctx
    (by decide) (by decide) hctx
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  have hdextFields := hdext
  unfold aeneas_extract.decode_extract_from_decoded at hdextFields
  obtain ⟨_, _, hdextFields⟩ := bind_eq_ok_imp hdextFields
  obtain ⟨_, _, hdextFields⟩ := bind_eq_ok_imp hdextFields
  obtain ⟨_, _, hdextFields⟩ := bind_eq_ok_imp hdextFields
  rw [Result.ok.injEq] at hdextFields
  have hdextrd : dext.rd = decoded.rd := by rw [← hdextFields]
  have hdextrs1 : dext.rs1 = decoded.rs1 := by rw [← hdextFields]
  have hdextrs2 : dext.rs2 = decoded.rs2 := by rw [← hdextFields]
  have hdextimm : dext.imm = decoded.imm := by rw [← hdextFields]
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
        defCtx input .Jalr false = .ok { ctx with extract_marker := () } := by
    change (do
      let s ← riscv2zisk_context.Riscv2ZiskContext.jalr
        { defCtx with extract_marker := () } input 4#u64
      .ok { s with extract_marker := () }) = _
    rw [hctx]
    rfl
  rcases hpins with ⟨hrem, _⟩ | ⟨rem, hrem, hne, first, last, hfirst, hlast, _⟩
  · have htwo : (input.imm % 4#i32) = (Result.ok (2#i32) : Result Std.I32) := by
      change IScalar.rem (2#i32) (4#i32) = _
      norm_num [IScalar.rem]
      decide
    rw [htwo] at hrem
    have hbad : (2#i32 : Std.I32) = 0#i32 := Result.ok.inj hrem
    exact False.elim ((by decide : (2#i32 : Std.I32) ≠ 0#i32) hbad)
  · obtain ⟨lastRow, hfrom, _⟩ := from_inst_full_fields last.i
    let terminal : aeneas_extract.Rv64imTranspileExtract :=
      { accepted := true, decode := dext, row := lastRow }
    have hterminal : aeneas_extract.extract_transpile_rv64im_raw
        (ZiskFv.Compliance.Decode.toU32 (0x00208067#32)) = .ok terminal := by
      rw [aeneas_extract.extract_transpile_rv64im_raw, hdecoded]
      simp only [bind_ok, Bind.bind, hdext]
      change (do
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input .Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row } :
          aeneas_extract.Rv64imTranspileExtract)) = .ok terminal
      rw [hlower]
      simp only [Bind.bind, hlast, core.option.Option.unwrap, Result.ofOption,
        bind_ok, hfrom]
      rfl
    let rows : aeneas_extract.Rv64imTranspileRowsExtract :=
      { accepted := true, decode := dext, row_count := 2#u32,
        first_row := first, last_row := lastRow }
    have hrows : aeneas_extract.extract_transpile_rv64im_rows_raw
        (ZiskFv.Compliance.Decode.toU32 (0x00208067#32)) = .ok rows := by
      unfold aeneas_extract.extract_transpile_rv64im_rows_raw
      rw [hterminal]
      simp only [terminal, hdextrd, hdextrs1, hdextrs2, hdextimm,
        lift, Bind.bind, bind_ok]
      have htag :
          (ZiskFv.Compliance.Decode.toU32 (0x00208067#32) &&& 127#u32) =
            103#u32 := by decide
      have hremDecoded :
          (decoded.imm % 4#i32) = (Result.ok rem : Result Std.I32) := by
        simpa only [input] using hrem
      have hremval : rem.val ≠ 0 := by
        intro hz
        apply hne
        apply IScalar.val_eq_imp
        simpa using hz
      have hnonzero : (rem != 0#i32) = true := by
        simpa using hremval
      have hinputNew :
          riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
            decoded.rd decoded.rs1 decoded.rs2 decoded.imm = .ok input := rfl
      simp only [htag, if_true, hremDecoded, bind_ok, Bind.bind,
        hnonzero, hinputNew]
      change (do
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input .Jalr false
        let first' ← core.option.Option.unwrap ctx'.extract_first_inst
        .ok ({
          accepted := true
          decode := dext
          row_count := 2#u32
          first_row := first'
          last_row := lastRow } :
          aeneas_extract.Rv64imTranspileRowsExtract)) = .ok rows
      rw [hlower]
      simp only [Bind.bind, hfirst, core.option.Option.unwrap, Result.ofOption, bind_ok]
      rfl
    exact ⟨⟨rows, hrows, rfl⟩, rfl⟩

/-- Actual successful two-row lowering of `jalr x0, x1, 2`. -/
noncomputable def sourceJalrTwo : SuccessfulRowLowering (0x00208067#32) :=
  sourceJalrTwo_exists.choose

theorem sourceJalrTwo_width : sourceJalrTwo.width = 2 :=
  sourceJalrTwo_exists.choose_spec

set_option maxHeartbeats 8000000 in
private theorem sourceAddiOne_exists :
    ∃ lowering : SuccessfulRowLowering (0x00000013#32), lowering.width = 1 := by
  let decoded : aeneas_extract.rv64im_decode.DecodedRv64im :=
    { opcode := .Addi, format := .I, funct3 := 0#u32, funct7 := 0#u32,
      rd := 0#u32, rs1 := 0#u32, rs2 := 0#u32, imm := 0#i32,
      pred := 0#u32, succ := 0#u32 }
  have hdecoded : aeneas_extract.rv64im_decode.decode_32_core
      (ZiskFv.Compliance.Decode.toU32 (0x00000013#32)) = .ok decoded := by
    rfl
  let input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm }
  obtain ⟨ctx, hctx⟩ := nop_ok { defCtx with extract_marker := () } input 4#u64
  obtain ⟨last, hlast, _⟩ := nop_static_pins
    { defCtx with extract_marker := () } input 4#u64 ctx hctx
  obtain ⟨lastRow, hfrom, _⟩ := from_inst_full_fields last.i
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
        defCtx input .Addi false = .ok { ctx with extract_marker := () } := by
    change (do
      let s ← riscv2zisk_context.Riscv2ZiskContext.nop
        { defCtx with extract_marker := () } input 4#u64
      .ok { s with extract_marker := () }) = _
    rw [hctx]
    rfl
  let terminal : aeneas_extract.Rv64imTranspileExtract :=
    { accepted := true, decode := dext, row := lastRow }
  have hterminal : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 (0x00000013#32)) = .ok terminal := by
    rw [aeneas_extract.extract_transpile_rv64im_raw, hdecoded]
    simp only [bind_ok, Bind.bind, hdext]
    change (do
      let ctx' ←
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input .Addi false
      let zib ← core.option.Option.unwrap ctx'.extract_inst
      let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
      .ok ({ accepted := true, decode := dext, row } :
        aeneas_extract.Rv64imTranspileExtract)) = .ok terminal
    rw [hlower]
    simp only [Bind.bind, hlast, core.option.Option.unwrap, Result.ofOption,
      bind_ok, hfrom]
    rfl
  let rows : aeneas_extract.Rv64imTranspileRowsExtract :=
    { accepted := true, decode := dext, row_count := 1#u32,
      first_row := lastRow, last_row := lastRow }
  have hrows : aeneas_extract.extract_transpile_rv64im_rows_raw
      (ZiskFv.Compliance.Decode.toU32 (0x00000013#32)) = .ok rows := by
    unfold aeneas_extract.extract_transpile_rv64im_rows_raw
    rw [hterminal]
    change (Result.ok rows : Result aeneas_extract.Rv64imTranspileRowsExtract) =
      (Result.ok rows : Result aeneas_extract.Rv64imTranspileRowsExtract)
    rfl
  exact ⟨⟨rows, hrows, rfl⟩, rfl⟩

/-- Actual successful one-row lowering of `addi x0, x0, 0` (NOP). -/
noncomputable def sourceAddiOne : SuccessfulRowLowering (0x00000013#32) :=
  sourceAddiOne_exists.choose

theorem sourceAddiOne_width : sourceAddiOne.width = 1 :=
  sourceAddiOne_exists.choose_spec

end ZiskFv.Compliance
