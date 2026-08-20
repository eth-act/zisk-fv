import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataControl

/-!
# ROM-driven decode binding — full RV64IM sweep (issue #159, BLOCK 1)

Replicates the ADD pilot (`RomDecodeBinding.Decode_add_of_program`) across the
remaining 62 RV64IM opcodes.  For each op, `Decode_<op>_of_program` DERIVES the
ROM-message-backed decode columns (`op`, `jmp_offset1/2`, `ind_width`, and the
packed flag columns `is_external_op`/`m32`/`set_pc`/`store_pc`) of the witness
row from the committed program `trace.program`, via the in-circuit ROM lookup
(`mainRomMessage_at_eq_program`) plus `packFlags` injectivity — given
*program-level* decode facts about the committed instruction bound to the row's
`pc`.  Non-ROM-message decode pins (Main-core columns like JALR's `flag`/`a`/`c`
lanes, the shift-immediate `b_0` shamt witness, the load sign-extension lookup
witnesses, the M-ext arith-memory/bound/pin witnesses, FENCE's claim-level
`fm`/`rs`/`rd` facts, and any value/PC-provenance bridges) are LEFT as
passthrough hypotheses — they belong to block 2 / pre-existing trust classes.

The program-level decode premise is quantified over ALL program entries at the
row's committed line, so the binding existential discharges it without a
program-line-distinctness premise (see the R1 note in `RomDecodeBinding.lean`).

No axioms: every column is derived from `trace.constraints_hold`.
-/

namespace ZiskFv.Compliance.RomDecodeBinding

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Trusted
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.Main (romMessage RomFlagBits packFlags romFlags)

set_option maxHeartbeats 1000000

/-- **Comprehensive ROM-column binding.**  Extends the pilot's
    `mainDecodeColumns_at_eq_program` with the `ind_width` slot (needed by the
    load/store families), for the SAME bound program entry `j`. -/
theorem mainRomColumns_at_eq_program
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    ∃ j : Fin trace.programLength,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc idx.val
    ∧ (trace.program j).op = (mainOfTable trace.program trace.mainTable).op idx.val
    ∧ (trace.program j).ind_width
        = (mainOfTable trace.program trace.mainTable).ind_width idx.val
    ∧ (trace.program j).jmp_offset1
        = (mainOfTable trace.program trace.mainTable).jmp_offset1 idx.val
    ∧ (trace.program j).jmp_offset2
        = (mainOfTable trace.program trace.mainTable).jmp_offset2 idx.val
    ∧ (trace.program j).flags
        = romFlags (mainTableRowAtOrZero trace.program trace.mainTable idx.val) := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace idx
  refine ⟨j, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [← hj, romMessage,
      mainOfTable_pc, mainOfTable_op, mainOfTable_ind_width,
      mainOfTable_jmp_offset1, mainOfTable_jmp_offset2]

/-- **Store-offset ROM-column binding.**  Projects the destination/address
    offset slot from the same Main↔ROM lookup used by
    `mainRomColumns_at_eq_program`, without changing that theorem's widely-used
    tuple shape. -/
theorem mainStoreOffset_at_eq_program
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    ∃ j : Fin trace.programLength,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc idx.val
    ∧ (trace.program j).store_offset
        = (mainTableRowAtOrZero trace.program trace.mainTable idx.val).rom.store_offset := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace idx
  refine ⟨j, ?_, ?_⟩ <;>
    simp only [← hj, romMessage, mainOfTable_pc]

/-- **B-offset ROM-column binding.** Projects the load-address immediate slot
    from the same Main↔ROM lookup used by `mainRomColumns_at_eq_program`. -/
theorem mainBOffsetImm0_at_eq_program
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    ∃ j : Fin trace.programLength,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc idx.val
    ∧ (trace.program j).b_offset_imm0
        = (mainTableRowAtOrZero trace.program trace.mainTable idx.val).rom.b_offset_imm0 := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace idx
  refine ⟨j, ?_, ?_⟩ <;>
    simp only [← hj, romMessage, mainOfTable_pc]

/-! ### Physical-row unpacking

Every family except JALR decodes at the physical row `⟨i.val, _⟩` carrying the
architectural index `i`, so the wrappers below are stated at `i`. JALR's
unaligned lowering spans two adjacent physical rows, only the first of which is
the architectural index, so it needs the same unpacking at an arbitrary
`Fin trace.mainTable.table.length`. The underlying binding lemmas
(`mainRomMessage_at_eq_program`, `mainRow_flags_boolean`, `mainSourceSpec_at`)
are already physical; these `…_at` versions just drop the architectural
projection, and the architectural wrappers are their instances at
`⟨i.val, h_lt⟩`. -/

/-- **Flag-column unpacking at a physical Main row.** Given the row's packed
    `romFlags` equals `packFlags bits`, the four packed flag columns equal
    `boolF` of their bits. -/
theorem mainFlagColumns_of_packFlags_at
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (row : Fin trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val)
        = packFlags bits) :
    (mainOfTable trace.program trace.mainTable).is_external_op row.val
        = ZiskFv.AirsClean.boolF bits.is_external_op
  ∧ (mainOfTable trace.program trace.mainTable).m32 row.val
        = ZiskFv.AirsClean.boolF bits.m32
  ∧ (mainOfTable trace.program trace.mainTable).set_pc row.val
        = ZiskFv.AirsClean.boolF bits.set_pc
  ∧ (mainOfTable trace.program trace.mainTable).store_pc row.val
        = ZiskFv.AirsClean.boolF bits.store_pc := by
  obtain ⟨a, b, d, e⟩ := romFlagColumns_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable row.val) bits
    (mainRow_flags_boolean trace row) h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mainOfTable_is_external_op] using a
  · simpa only [mainOfTable_m32] using b
  · simpa only [mainOfTable_set_pc] using d
  · simpa only [mainOfTable_store_pc] using e

/-- **Memory/register selector unpacking at a physical Main row.** The full
    six-selector projection of `romMemorySelectorColumns_of_romFlags_eq_packFlags`
    (the three-selector `mainSelectorColumns_of_packFlags` is the architectural
    subset used by address placement). -/
theorem mainMemorySelectorColumns_of_packFlags_at
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (row : Fin trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val)
        = packFlags bits) :
    (mainRowWithRomAt trace row).rom.b_src_mem = ZiskFv.AirsClean.boolF bits.b_src_mem
  ∧ (mainRowWithRomAt trace row).rom.store_mem = ZiskFv.AirsClean.boolF bits.store_mem
  ∧ (mainRowWithRomAt trace row).rom.store_ind = ZiskFv.AirsClean.boolF bits.store_ind
  ∧ (mainRowWithRomAt trace row).rom.b_src_ind = ZiskFv.AirsClean.boolF bits.b_src_ind
  ∧ (mainRowWithRomAt trace row).rom.b_src_reg = ZiskFv.AirsClean.boolF bits.b_src_reg
  ∧ (mainRowWithRomAt trace row).rom.store_reg = ZiskFv.AirsClean.boolF bits.store_reg :=
  romMemorySelectorColumns_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable row.val) bits
    (mainRow_flags_boolean trace row) h

/-- **`b`-immediate-source selector unpacking at a physical Main row.** -/
theorem mainBSourceImmColumn_of_packFlags_at
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (row : Fin trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val)
        = packFlags bits) :
    (mainRowWithRomAt trace row).rom.b_src_imm
        = ZiskFv.AirsClean.boolF bits.b_src_imm :=
  romBSourceImmColumn_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable row.val) bits
    (mainRow_flags_boolean trace row) h

/-- **`a`-immediate-source selector unpacking at a physical Main row.** -/
theorem mainASourceImmColumn_of_packFlags_at
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (row : Fin trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val)
        = packFlags bits) :
    (mainRowWithRomAt trace row).rom.a_src_imm
        = ZiskFv.AirsClean.boolF bits.a_src_imm :=
  romASourceImmColumn_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable row.val) bits
    (mainRow_flags_boolean trace row) h

/-- **Flag-column unpacking at a row.**  Given the row's packed `romFlags` equals
    `packFlags bits`, the four packed flag columns equal `boolF` of their bits.
    Wraps `romFlagColumns_of_romFlags_eq_packFlags` + `mainRow_flags_boolean` and
    projects to the `mainOfTable` named columns. -/
theorem mainFlagColumns_of_packFlags
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val)
        = packFlags bits) :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val
        = ZiskFv.AirsClean.boolF bits.is_external_op
  ∧ (mainOfTable trace.program trace.mainTable).m32 i.val
        = ZiskFv.AirsClean.boolF bits.m32
  ∧ (mainOfTable trace.program trace.mainTable).set_pc i.val
        = ZiskFv.AirsClean.boolF bits.set_pc
  ∧ (mainOfTable trace.program trace.mainTable).store_pc i.val
        = ZiskFv.AirsClean.boolF bits.store_pc :=
  mainFlagColumns_of_packFlags_at trace ⟨i.val, h_lt⟩ bits h

/-- **Selector-column unpacking at a row.** Given the row's packed `romFlags`
    equals `packFlags bits`, the selector columns needed by address-placement
    proofs equal `boolF` of their bits. -/
theorem mainSelectorColumns_of_packFlags
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val)
        = packFlags bits) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind
        = ZiskFv.AirsClean.boolF bits.store_ind
  ∧ (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_src_ind
        = ZiskFv.AirsClean.boolF bits.b_src_ind
  ∧ (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg
        = ZiskFv.AirsClean.boolF bits.store_reg := by
  exact romSelectorColumns_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable i.val) bits
    (mainRow_flags_boolean trace ⟨i.val, h_lt⟩) h

theorem mainRegSourceColumns_of_packFlags
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val)
        = packFlags bits) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_src_reg
        = ZiskFv.AirsClean.boolF bits.a_src_reg
  ∧ (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_src_reg
        = ZiskFv.AirsClean.boolF bits.b_src_reg :=
  romRegSourceColumns_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable i.val) bits
    (mainRow_flags_boolean trace ⟨i.val, h_lt⟩) h

/-- **Immediate-source selector unpacking at a row.** Given the row's packed
    `romFlags` equals `packFlags bits`, the `b_src_imm` column equals `boolF` of
    the committed-program bit. -/
theorem mainBSourceImmColumn_of_packFlags
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val)
        = packFlags bits) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_src_imm
        = ZiskFv.AirsClean.boolF bits.b_src_imm :=
  mainBSourceImmColumn_of_packFlags_at trace ⟨i.val, h_lt⟩ bits h

/-- The committed program's `b` immediate limbs, transported through the
    Main↔ROM lookup to the concrete row, together with `b_src_imm = 1`. -/
theorem mainBImmediateSourceFacts_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (imm : BitVec 12)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          BitVec.signExtend 64 imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_src_imm = 1
  ∧ BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          (((mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_offset_imm0).val
            + ((mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_imm1).val
              * 4294967296) := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace ⟨i.val, h_lt⟩
  have hline :
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc i.val := by
    simp only [← hj, romMessage, mainOfTable_pc]
  obtain ⟨h_imm, hpf⟩ := h_prog j hline
  have hrom :
      romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val) = packFlags bits := by
    have hflags :
        (trace.program j).flags =
          romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val) := by
      simp only [← hj, romMessage]
    exact hflags.symm.trans hpf
  have h_b_src_imm :=
    mainBSourceImmColumn_of_packFlags trace i h_lt bits hrom
  have h_b_src_imm_one :
      (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_src_imm = 1 := by
    simpa only [h_bits_b_src_imm, ZiskFv.AirsClean.boolF_true] using h_b_src_imm
  have h_b_offset :
      (trace.program j).b_offset_imm0 =
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_offset_imm0 := by
    simp only [← hj, romMessage]
  have h_b_imm1 :
      (trace.program j).b_imm1 =
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.b_imm1 := by
    simp only [← hj, romMessage]
  exact ⟨h_b_src_imm_one, by simpa only [h_b_offset, h_b_imm1] using h_imm⟩

/-- `SourceSpec` turns decoded immediate-source ROM limbs into the Main `b`
    lanes used by the I-type archetype. -/
theorem itypeImmSubset_of_sourceSpec
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (imm : BitVec 12)
    (h_source : ZiskFv.AirsClean.Main.SourceSpec (mainRowWithRomSub trace i))
    (h_b_src_imm : (mainRowWithRomSub trace i).rom.b_src_imm = 1)
    (h_rom_imm :
      BitVec.signExtend 64 imm
        = BitVec.ofNat 64
            (((mainRowWithRomSub trace i).rom.b_offset_imm0).val
              + ((mainRowWithRomSub trace i).rom.b_imm1).val * 4294967296)) :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      (mainOfTable trace.program trace.mainTable) i.val imm := by
  obtain ⟨_, _, h_b0, h_b1⟩ := h_source
  have h_b0_zero :
      (mainRowWithRomSub trace i).core.b_0
        + -1 * (mainRowWithRomSub trace i).rom.b_offset_imm0 = 0 := by
    simpa only [h_b_src_imm, one_mul] using h_b0
  have h_b1_zero :
      (mainRowWithRomSub trace i).core.b_1
        + -1 * (mainRowWithRomSub trace i).rom.b_imm1 = 0 := by
    simpa only [h_b_src_imm, one_mul] using h_b1
  have h_b0_eq :
      (mainRowWithRomSub trace i).core.b_0 =
        (mainRowWithRomSub trace i).rom.b_offset_imm0 := by
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg] using h_b0_zero
  have h_b1_eq :
      (mainRowWithRomSub trace i).core.b_1 =
        (mainRowWithRomSub trace i).rom.b_imm1 := by
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg] using h_b1_zero
  simpa [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main,
    mainRowWithRomSub, mainOfTable_b_0, mainOfTable_b_1, h_b0_eq, h_b1_eq] using h_rom_imm

/-- Writeback destination selector/offset facts derived from the committed
    program and packed ROM flags for the op-agnostic `mainRowWithRomSub` row. -/
theorem mainWritebackDestinationFacts_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (rd : regidx)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).store_offset = Transpiler.ind (regidx_to_fin rd)
        ∧ (trace.program j).flags = packFlags bits) :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  ∧ (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin rd) := by
  obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
    mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
  obtain ⟨_hpso, hpf⟩ := h_prog j hline
  obtain ⟨p_store_ind, _, _⟩ :=
    mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
  have h_store_ind : (mainRowWithRomSub trace i).rom.store_ind = 0 := by
    simpa [mainRowWithRomSub, h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind
  have h_store_offset :
      (mainRowWithRomSub trace i).rom.store_offset =
        Transpiler.ind (regidx_to_fin rd) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomSub] using hstore.symm.trans hpso
  exact ⟨h_store_ind, h_store_offset⟩

/-- Writeback destination selector/offset facts derived from the committed
    program and packed ROM flags for the `mainRowWithRomLui` row used by
    LUI/AUIPC/JAL/JALR rd writes. -/
theorem mainLuiDestinationFacts_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (rd : regidx)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).store_offset = Transpiler.ind (regidx_to_fin rd)
        ∧ (trace.program j).flags = packFlags bits) :
    (mainRowWithRomLui trace i).rom.store_ind = 0
  ∧ (mainRowWithRomLui trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin rd) := by
  obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
    mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
  obtain ⟨_hpso, hpf⟩ := h_prog j hline
  obtain ⟨p_store_ind, _, _⟩ :=
    mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
  have h_store_ind : (mainRowWithRomLui trace i).rom.store_ind = 0 := by
    simpa [mainRowWithRomLui, h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind
  have h_store_offset :
      (mainRowWithRomLui trace i).rom.store_offset =
        Transpiler.ind (regidx_to_fin rd) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLui] using hstore.symm.trans hpso
  exact ⟨h_store_ind, h_store_offset⟩

/-- Physical-row twin of `mainLuiDestinationFacts_of_program`: writeback
    destination selector/offset facts derived from the committed program at an
    arbitrary Main row, for a lowering whose writeback row is not the
    architectural index (JALR's unaligned terminal `OP_AND` row). -/
theorem mainDestinationFacts_of_program_at
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (row : Fin trace.mainTable.table.length)
    (bits : RomFlagBits)
    (rd : regidx)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc row.val →
          (trace.program j).store_offset = Transpiler.ind (regidx_to_fin rd)
        ∧ (trace.program j).flags = packFlags bits) :
    (mainRowWithRomAt trace row).rom.store_ind = 0
  ∧ (mainRowWithRomAt trace row).rom.store_offset
      = Transpiler.ind (regidx_to_fin rd) := by
  obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
    mainRomColumns_at_eq_program trace row
  obtain ⟨_hpso, hpf⟩ := h_prog j hline
  obtain ⟨_, _, p_store_ind, _, _, _⟩ :=
    mainMemorySelectorColumns_of_packFlags_at trace row bits (hflags.symm.trans hpf)
  refine ⟨by simpa [h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind, ?_⟩
  obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace row
  obtain ⟨hpso, _hpf⟩ := h_prog j hline
  simpa [mainRowWithRomAt] using hstore.symm.trans hpso


/-! ## Family: R/I-type ALU -/

/-- `Decode_sub` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sub_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sub trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SUB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sub trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind = 0 ∧
      (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_offset =
        Transpiler.ind (regidx_to_fin c.rd) := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    obtain ⟨p_store_ind, _p_b_src_ind, _p_store_reg⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    obtain ⟨j_store, hline_store, hstore⟩ :=
      mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_, _, _, hp_store_offset, _⟩ := h_prog j_store hline_store
    refine ⟨hop.symm.trans hpo, ?_, ?_, ?_, ?_,
      hj1.symm.trans hpj0, hj2.symm.trans hpj1, ?_, hstore.symm.trans hp_store_offset⟩
    · rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true]
    · rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false]
    · rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false]
    · rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false]
    · rw [p_store_ind, h_bits_store_ind, ZiskFv.AirsClean.boolF_false]
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2.1
      h_store_ind := key.2.2.2.2.2.2.2.1
      h_store_offset := key.2.2.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_and` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_and_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_and trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_and trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_or` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_or_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_or trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_or trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_xor` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_xor_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_xor trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_xor trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_slt` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_slt_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slt trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_slt trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_sltu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sltu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sltu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sltu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_andi` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_andi_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_andi trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_andi trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry }

/-- `Decode_ori` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_ori_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_ori trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_ori trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry }

/-- `Decode_xori` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_xori_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_xori trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_xori trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry }

/-- `Decode_slti` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_slti_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slti trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_slti trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry }

/-- `Decode_sltiu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sltiu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sltiu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sltiu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry }

/-- `Decode_addi` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_addi_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_addi trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_addi trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind = 0 ∧
      (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_offset =
        Transpiler.ind (regidx_to_fin c.rd) := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    obtain ⟨p_store_ind, _p_b_src_ind, _p_store_reg⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    obtain ⟨j_store, hline_store, hstore⟩ :=
      mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_, _, _, hp_store_offset, _hp_imm, _⟩ := h_prog j_store hline_store
    refine ⟨hop.symm.trans hpo, ?_, ?_, ?_, ?_,
      hj1.symm.trans hpj0, hj2.symm.trans hpj1, ?_, hstore.symm.trans hp_store_offset⟩
    · rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true]
    · rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false]
    · rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false]
    · rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false]
    · rw [p_store_ind, h_bits_store_ind, ZiskFv.AirsClean.boolF_false]
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2.1
      h_store_ind := key.2.2.2.2.2.2.2.1
      h_store_offset := key.2.2.2.2.2.2.2.2
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx }


/-! ## Family: shifts -/

/-- `Decode_sll` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sll_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sll trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sll trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_srl` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srl_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srl trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_srl trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_sra` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sra_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sra trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sra trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_slli` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_slli_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slli trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_slli trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := sorry
      h_b_offset_imm0 := sorry }

/-- `Decode_srli` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srli_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srli trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_srli trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := sorry
      h_b_offset_imm0 := sorry }

/-- `Decode_srai` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srai_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srai trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_srai trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := sorry
      h_b_offset_imm0 := sorry }


/-! ## Family: W-ALU and W-shifts -/

/-- `Decode_subw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_subw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_subw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SUB_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_subw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_addw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_addw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_addw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_addw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_addiw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_addiw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_addiw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_b_src_imm : bits.b_src_imm = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_addiw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, _hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  have h_src :=
    mainBImmediateSourceFacts_of_program trace i h_lt bits c.imm h_bits_b_src_imm
      (fun j hline => by
        obtain ⟨_, _, _, _, hp_imm, hpf⟩ := h_prog j hline
        exact ⟨hp_imm, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := h_src.1
      h_b_imm := h_src.2
      h_store_reg := sorry
      h_idx := h_idx }

/-- `Decode_sllw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sllw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sllw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sllw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_srlw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srlw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srlw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_srlw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_sraw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sraw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sraw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sraw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_slliw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_slliw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slliw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_slliw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := sorry
      h_b_offset_imm0 := sorry }

/-- `Decode_srliw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srliw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srliw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_srliw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := sorry
      h_b_offset_imm0 := sorry }

/-- `Decode_sraiw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sraiw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sraiw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sraiw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_imm := sorry
      h_b_offset_imm0 := sorry }


/-! ## Family: M-ext -/

/-- `Decode_mulw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_mulw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MUL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_mulw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx }

/-- `Decode_mul` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_mul_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mul trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MUL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_mul trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_mulh` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_mulh_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulh trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_mulh trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_mulhsu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_mulhsu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulhsu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULSUH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_mulhsu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_div` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_div_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_div trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIV
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_div trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      pins := { main_active := key.2.1, main_op := key.1 }
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_rem` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_rem_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_rem trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REM
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_rem trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      pins := { main_active := key.2.1, main_op := key.1 }
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_divw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_divw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_divw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIV_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_divw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      pins := { main_active := key.2.1, main_op := key.1 }
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_remw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_remw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_remw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REM_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_remw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      pins := { main_active := key.2.1, main_op := key.1 }
      arith_mem := arith_mem
      bounds := bounds }

/-- `Decode_mulhu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_mulhu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulhu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULUH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_mulhu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      bounds := bounds }

/-- `Decode_divu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_divu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_divu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIVU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_divu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      bounds := bounds }

/-- `Decode_divuw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_divuw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_divuw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIVU_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_divuw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      bounds := bounds }

/-- `Decode_remu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_remu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_remu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REMU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_remu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      bounds := bounds }

/-- `Decode_remuw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_remuw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_remuw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REMU_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_remuw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hp_store_offset, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_dest :=
    mainWritebackDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
      (fun j hline => by
        obtain ⟨_, _, _, hp_store_offset, hpf⟩ := h_prog j hline
        exact ⟨hp_store_offset, hpf⟩)
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      bounds := bounds }


/-! ## Shared load destination placement -/

/-- Load destination selector/offset facts derived from the committed program
    and packed ROM flags.  This is the primitive decode fact needed to derive
    the old `Inputs_*` `addr2` register-index pins from `AddressSpec`. -/
theorem mainLoadDestinationFacts_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (rd : BitVec 5)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (rd.toNat ≠ 0))
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 rd)
        ∧ (trace.program j).flags = packFlags bits) :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  ∧ (mainRowWithRomLd trace i).rom.store_reg = (if rd.toNat = 0 then 0 else 1)
  ∧ (mainRowWithRomLd trace i).rom.store_offset =
      Transpiler.ind (Transpiler.regidxOfBitVec5 rd) := by
  obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
    mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
  obtain ⟨_hpso, hpf⟩ := h_prog j hline
  obtain ⟨p_store_ind, _, p_store_reg⟩ :=
    mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
  have h_store_ind : (mainRowWithRomLd trace i).rom.store_ind = 0 := by
    simpa [mainRowWithRomLd, h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind
  have h_store_reg :
      (mainRowWithRomLd trace i).rom.store_reg = (if rd.toNat = 0 then 0 else 1) := by
    rw [p_store_reg, h_bits_store_reg]
    by_cases hrd : rd.toNat = 0
    · simp [hrd, ZiskFv.AirsClean.boolF_false]
    · rw [show decide (rd.toNat ≠ 0) = true from decide_eq_true hrd]
      simp [hrd, ZiskFv.AirsClean.boolF_true]
  have h_store_offset :
      (mainRowWithRomLd trace i).rom.store_offset =
        Transpiler.ind (Transpiler.regidxOfBitVec5 rd) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hstore.symm.trans hpso
  exact ⟨h_store_ind, h_store_reg, h_store_offset⟩

/-- Load memory-address selector fact derived from the committed program and
    packed ROM flags. This is the primitive decode fact needed to derive the
    old `Inputs_*` `addr1` placement pins from `AddressSpec`. -/
theorem mainLoadBsrcInd_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_lt : i.val < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).flags = packFlags bits) :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1 := by
  obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
    mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
  have hpf := h_prog j hline
  obtain ⟨_, p_b_src_ind, _⟩ :=
    mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
  simpa [mainRowWithRomLd, h_bits_b_src_ind, ZiskFv.AirsClean.boolF_true] using p_b_src_ind


/-! ## Family: loads -/

/-- `Decode_ld` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_ld_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_ld trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.ld_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (8 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.ld_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.ld_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_ld trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (8 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_store_ind : (mainRowWithRomLd trace i).rom.store_ind = 0 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _p_store_reg⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomLd, h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind
  have h_store_reg : (mainRowWithRomLd trace i).rom.store_reg =
      (if c.ld_input.rd.toNat = 0 then 0 else 1) := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨_p_store_ind, _, p_store_reg⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    rw [show (mainRowWithRomLd trace i).rom.store_reg =
        ZiskFv.AirsClean.boolF bits.store_reg by simpa [mainRowWithRomLd] using p_store_reg,
      h_bits_store_reg]
    by_cases hrd : c.ld_input.rd.toNat = 0
    · simp [hrd, ZiskFv.AirsClean.boolF_false]
    · rw [show decide (c.ld_input.rd.toNat ≠ 0) = true from decide_eq_true hrd]
      simp [hrd, ZiskFv.AirsClean.boolF_true]
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_store_offset :
      (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.ld_input.rd) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hstore.symm.trans hpso
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.ld_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      h_store_ind := h_store_ind
      h_store_reg := h_store_reg
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_store_offset
      h_b_offset_imm0 := h_b_offset_imm0 }

/-- `Decode_lbu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lbu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lbu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.lbu_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lbu_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lbu_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lbu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (1 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lbu_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.lbu_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_reg := h_dest.2.1
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_dest.2.2
      h_b_offset_imm0 := h_b_offset_imm0 }

/-- `Decode_lhu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lhu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lhu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.lhu_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lhu_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lhu_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lhu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (2 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lhu_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.lhu_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_reg := h_dest.2.1
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_dest.2.2
      h_b_offset_imm0 := h_b_offset_imm0 }

/-- `Decode_lwu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lwu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lwu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.lwu_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lwu_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lwu_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lwu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (4 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lwu_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.lwu_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      h_store_ind := h_dest.1
      h_store_reg := h_dest.2.1
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_dest.2.2
      h_b_offset_imm0 := h_b_offset_imm0 }

/-- `Decode_lb` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lb_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lb trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (v :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary :
    ℕ)
    (offset :
    ℕ)
    (env :
    Environment FGL)
    (h_static :
    ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.lb_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_B
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lb_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lb_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lb trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SIGNEXTEND_B ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (1 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lb_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.lb_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      v := v
      r_binary := r_binary
      offset := offset
      env := env
      h_static := h_static
      h_match := h_match
      h_store_ind := h_dest.1
      h_store_reg := h_dest.2.1
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_dest.2.2
      h_b_offset_imm0 := h_b_offset_imm0 }

/-- `Decode_lh` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lh_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lh trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (v :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary :
    ℕ)
    (offset :
    ℕ)
    (env :
    Environment FGL)
    (h_static :
    ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.lh_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_H
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lh_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lh_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lh trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SIGNEXTEND_H ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (2 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lh_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.lh_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      v := v
      r_binary := r_binary
      offset := offset
      env := env
      h_static := h_static
      h_match := h_match
      h_store_ind := h_dest.1
      h_store_reg := h_dest.2.1
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_dest.2.2
      h_b_offset_imm0 := h_b_offset_imm0 }

/-- `Decode_lw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (v :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary :
    ℕ)
    (offset :
    ℕ)
    (env :
    Environment FGL)
    (h_static :
    ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_bits_store_reg : bits.store_reg = decide (c.lw_input.rd.toNat ≠ 0))
    (h_bits_b_src_ind : bits.b_src_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lw_input.imm).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lw_input.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SIGNEXTEND_W ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = (4 : FGL) := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lw_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1 :=
    mainLoadBsrcInd_of_program trace i h_lt bits h_bits_b_src_ind
      (fun j hline => by
        obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpbo, _hpso, hpf⟩ := h_prog j hline
        exact hpf)
  have h_b_offset_imm0 :
      (mainRowWithRomLd trace i).rom.b_offset_imm0 =
        ((BitVec.signExtend 64 c.lw_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hboff⟩ := mainBOffsetImm0_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpbo, _hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hboff.symm.trans hpbo
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx
      v := v
      r_binary := r_binary
      offset := offset
      env := env
      h_static := h_static
      h_match := h_match
      h_store_ind := h_dest.1
      h_store_reg := h_dest.2.1
      h_b_src_ind := h_b_src_ind
      h_store_offset := h_dest.2.2
      h_b_offset_imm0 := h_b_offset_imm0 }


/-! ## Family: stores -/

/-- `Decode_sb` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sb_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sb trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 1
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sb_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sb trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = 1 := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_store_ind : (mainRowWithRomSt trace i).rom.store_ind = 1 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomSt, h_bits_store_ind, ZiskFv.AirsClean.boolF_true] using p_store_ind
  have h_store_offset_imm :
      (mainRowWithRomSt trace i).rom.store_offset =
        ((BitVec.signExtend 64 c.sb_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomSt] using hstore.symm.trans hpso
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_main_ind_width := key.2.2.2.2.2.2
      h_store_ind := h_store_ind
      h_store_offset_imm := h_store_offset_imm
      h_store_reg := sorry
      h_idx := h_idx }

/-- `Decode_sh` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sh_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sh trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 2
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sh_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sh trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = 2 := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_store_ind : (mainRowWithRomSt trace i).rom.store_ind = 1 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomSt, h_bits_store_ind, ZiskFv.AirsClean.boolF_true] using p_store_ind
  have h_store_offset_imm :
      (mainRowWithRomSt trace i).rom.store_offset =
        ((BitVec.signExtend 64 c.sh_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomSt] using hstore.symm.trans hpso
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_main_ind_width := key.2.2.2.2.2.2
      h_store_ind := h_store_ind
      h_store_offset_imm := h_store_offset_imm
      h_store_reg := sorry
      h_idx := h_idx }

/-- `Decode_sw` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sw_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 4
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sw_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sw trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).ind_width i.val = 4 := by
    obtain ⟨j, hline, hop, hiw, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_store_ind : (mainRowWithRomSt trace i).rom.store_ind = 1 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomSt, h_bits_store_ind, ZiskFv.AirsClean.boolF_true] using p_store_ind
  have h_store_offset_imm :
      (mainRowWithRomSt trace i).rom.store_offset =
        ((BitVec.signExtend 64 c.sw_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomSt] using hstore.symm.trans hpso
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_main_ind_width := key.2.2.2.2.2.2
      h_store_ind := h_store_ind
      h_store_offset_imm := h_store_offset_imm
      h_store_reg := sorry
      h_idx := h_idx }

/-- `Decode_sd` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_sd_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sd trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = true)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sd_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_sd trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  have h_store_ind : (mainRowWithRomSt trace i).rom.store_ind = 1 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomSt, h_bits_store_ind, ZiskFv.AirsClean.boolF_true] using p_store_ind
  have h_store_offset_imm :
      (mainRowWithRomSt trace i).rom.store_offset =
        ((BitVec.signExtend 64 c.sd_input.imm).toInt : FGL) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomSt] using hstore.symm.trans hpso
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2
      h_store_ind := h_store_ind
      h_store_offset_imm := h_store_offset_imm
      h_store_reg := sorry
      h_idx := h_idx }


/-! ## Family: LUI/AUIPC -/

/-- `Decode_lui` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_lui_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lui trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (c.imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_lui trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_dest := mainLuiDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
    (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_imm_lo_nat := h_imm_lo_nat
      h_imm_hi_nat := h_imm_hi_nat }

/-- `Decode_auipc` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_auipc_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_auipc trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = true)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 =
          ((BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toInt : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_auipc trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_dest := mainLuiDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
    (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj2_imm, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_FLAG ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, _, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, _hpj2_imm, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_true], hj1.symm.trans hpj0⟩
  have h_jmp_offset2_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val =
        ((BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, _, hj2, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, hpj2_imm, _hpso, _hpf⟩ := h_prog j hline
    simpa only [← hj2] using hpj2_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_jmp_offset2_imm := h_jmp_offset2_imm
      h_jmp1 := key.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx }


/-! ## Family: branches -/

/-- `Decode_beq` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_beq_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_beq trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_EQ
        ∧ (trace.program j).jmp_offset1 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_beq trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_EQ ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, _, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, _hpj1_imm, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj2.symm.trans hpj0⟩
  have h_jmp_offset1_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, hj1, _, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, hpj1_imm, _hpj0, _hpf⟩ := h_prog j hline
    simpa only [← hj1] using hpj1_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2
      h_jmp_offset1_imm := h_jmp_offset1_imm
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_bne` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_bne_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bne trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_EQ
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_bne trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_EQ ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, _, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, _hpj2_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0⟩
  have h_jmp_offset2_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, _, hj2, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, hpj2_imm, _hpf⟩ := h_prog j hline
    simpa only [← hj2] using hpj2_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2
      h_jmp_offset2_imm := h_jmp_offset2_imm
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_blt` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_blt_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_blt trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_blt trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, _, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, _hpj1_imm, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj2.symm.trans hpj0⟩
  have h_jmp_offset1_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, hj1, _, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, hpj1_imm, _hpj0, _hpf⟩ := h_prog j hline
    simpa only [← hj1] using hpj1_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2
      h_jmp_offset1_imm := h_jmp_offset1_imm
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_bge` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_bge_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bge trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_bge trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, _, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, _hpj2_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0⟩
  have h_jmp_offset2_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, _, hj2, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, hpj2_imm, _hpf⟩ := h_prog j hline
    simpa only [← hj2] using hpj2_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2
      h_jmp_offset2_imm := h_jmp_offset2_imm
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_bltu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_bltu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bltu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_bltu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, _, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, _hpj1_imm, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj2.symm.trans hpj0⟩
  have h_jmp_offset1_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, hj1, _, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, hpj1_imm, _hpj0, _hpf⟩ := h_prog j hline
    simpa only [← hj1] using hpj1_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2
      h_jmp_offset1_imm := h_jmp_offset1_imm
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := sorry
      h_a_offset_imm0 := sorry
      h_a_src_imm := sorry
      h_a_imm1 := sorry
      h_b_src_reg := sorry
      h_b_offset_imm0 := sorry
      h_b_src_imm := sorry
      h_b_imm1 := sorry }

/-- `Decode_bgeu` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_bgeu_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bgeu trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_bgeu trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, _, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, _hpj2_imm, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0⟩
  have h_jmp_offset2_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, _, hj2, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, hpj2_imm, _hpf⟩ := h_prog j hline
    simpa only [← hj2] using hpj2_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2
      h_jmp_offset2_imm := h_jmp_offset2_imm
      h_store_reg := sorry
      h_idx := h_idx
      h_a_src_reg := by sorry
      h_a_offset_imm0 := by sorry
      h_a_src_imm := by sorry
      h_a_imm1 := by sorry
      h_b_src_reg := by sorry
      h_b_offset_imm0 := by sorry
      h_b_src_imm := by sorry
      h_b_imm1 := by sorry }


/-! ## Family: JAL/JALR -/

/-- `Decode_jal` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_jal_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_jal trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = true)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset1 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_jal trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_dest := mainLuiDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
    (fun j hline => by
      obtain ⟨_hpo, _hpj1_imm, _hpj0, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_FLAG ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, _, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, _hpj1_imm, hpj0, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_true], hj2.symm.trans hpj0⟩
  have h_jmp_offset1_imm :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) := by
    obtain ⟨j, hline, _hop, _, hj1, _, _hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, hpj1_imm, _hpj0, _hpso, _hpf⟩ := h_prog j hline
    simpa only [← hj1] using hpj1_imm
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_jmp_offset1_imm := h_jmp_offset1_imm
      h_jmp2 := key.2.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx }

/-- `Decode_jalr` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_jalr_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
    (h_offset_aligned : c.offset_bv = BitVec.signExtend 64 c.imm)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_flag :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).flag
      i.val = 0)
    (h_a_mask_lo :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0
      i.val = 4294967294)
    (h_a_mask_hi :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1
      i.val = 4294967295)
    (h_c1_zero :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_1
      i.val = 0)
    (h_offset_even :
    c.offset_bv &&& 1#64 = 0#64)
    (h_target_nonneg :
      0 ≤ (((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0
        i.val).val : Int) + c.offset_bv.toInt)
    (h_target_lt :
      (((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0
        i.val).val : Int) + c.offset_bv.toInt < GL_prime)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = true)
    (h_bits_store_pc :
      bits.store_pc = decide ((regidx_to_fin c.rd).val ≠ 0))
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = ((BitVec.signExtend 64 c.imm).toInt : FGL)
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset =
            (if (regidx_to_fin c.rd).val = 0 then 0
             else Transpiler.ind (regidx_to_fin c.rd))
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_jalr trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  let physical : Fin trace.mainTable.table.length := ⟨i.val, h_lt⟩
  let rows : JalrLoweringRows trace i c.imm c.rs1 c.offset_bv :=
    { start := physical
      finish := physical
      architectural_start := rfl
      finish_has_successor := h_idx
      lowering := Or.inl ⟨rfl, h_offset_aligned⟩ }
  have h_dest :
      (mainRowWithRomLui trace i).rom.store_ind = 0 ∧
      (mainRowWithRomLui trace i).rom.store_offset =
        (if (regidx_to_fin c.rd).val = 0 then 0
         else Transpiler.ind (regidx_to_fin c.rd)) := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj1, _hpj2, hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    refine ⟨by
      simpa [mainRowWithRomLui, h_bits_store_ind, ZiskFv.AirsClean.boolF_false]
        using p_store_ind, ?_⟩
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_, _, _, hpso, _⟩ := h_prog j hline
    simpa [mainRowWithRomLui] using hstore.symm.trans hpso
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val =
        ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0)) ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val =
        ((BitVec.signExtend 64 c.imm).toInt : FGL) ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hjmp2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj1, hpj2, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true],
      by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false],
      by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_true],
      by rw [p_store_pc, h_bits_store_pc], hj1.symm.trans hpj1, hjmp2.symm.trans hpj2⟩
  exact
    { rows := rows
      h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_store_reg := sorry
      h_idx := h_idx
      h_flag := h_flag
      h_a_mask_lo := h_a_mask_lo
      h_a_mask_hi := h_a_mask_hi
      h_c1_zero := h_c1_zero
      h_jmp2 := Or.inl ⟨rfl, key.2.2.2.2.2.2⟩
      h_offset_bridge := by rw [key.2.2.2.2.2.1, h_offset_aligned]
      h_offset_even := h_offset_even
      h_target_nonneg := h_target_nonneg
      h_target_lt := h_target_lt
      h_start_store_reg_zero := fun h => absurd rfl h }

/-- `Decode_jalr` for the UNALIGNED lowering, rebuilt from the committed program
    via the ROM lookup at BOTH physical rows the lowering occupies.

    `Decode_jalr_of_program` covers the aligned lowering, which folds into the
    single architectural row. The unaligned lowering emits `OP_ADD` at the
    architectural row `i.val` (computing `rs1 + imm` on the `a`/`b` lanes) and
    the terminal `OP_AND` at its physical successor `i.val + 1` (masking bit
    zero, storing the link PC, and taking the jump). Both rows' ROM-message
    columns — `op`, `jmp_offset2`, `store_offset`, the packed
    `is_external_op`/`m32`/`set_pc`/`store_pc` flags, the `b`-lane source
    selectors, and the ADD row's `a`-lane immediate — are DERIVED here from
    `trace.program` at each row's OWN committed `pc`, so the two-row placement
    costs no extra program-level premise beyond the second line's decode.

    Passthrough (identical class to the aligned constructor's): the Main-core
    columns `flag`, `a_0`/`a_1`, `c_1`, the `jmp_offset1` ↔ `offset_bv` bridge,
    its evenness and no-wrap bounds, and the row bound. These are not ROM-message
    slots. -/
def Decode_jalr_unaligned_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
    -- the terminal row is the physical successor of the ADD row, and it too has
    -- a successor (the row the set-PC handshake lands on)
    (h_idx2 : i.val + 2 < trace.mainTable.table.length)
    -- claim-level: the unaligned lowering carries a zero terminal offset
    -- (mirrors the aligned constructor's `h_offset_aligned`)
    (h_offset_zero : c.offset_bv = 0#64)
    (h_flag_add :
    (mainOfTable trace.program trace.mainTable).flag i.val = 0)
    (h_flag :
    (mainOfTable trace.program trace.mainTable).flag (i.val + 1) = 0)
    (h_a_mask_lo :
    (mainOfTable trace.program trace.mainTable).a_0 (i.val + 1) = 4294967294)
    (h_a_mask_hi :
    (mainOfTable trace.program trace.mainTable).a_1 (i.val + 1) = 4294967295)
    (h_c1_zero :
    (mainOfTable trace.program trace.mainTable).c_1 (i.val + 1) = 0)
    (h_offset_even : c.offset_bv &&& 1#64 = 0#64)
    (h_target_nonneg :
      0 ≤ (((mainOfTable trace.program trace.mainTable).c_0
        (i.val + 1)).val : Int) + c.offset_bv.toInt)
    (h_target_lt :
      (((mainOfTable trace.program trace.mainTable).c_0
        (i.val + 1)).val : Int) + c.offset_bv.toInt < GL_prime)
    (addBits : RomFlagBits)
    (h_add_ieo : addBits.is_external_op = true)
    (h_add_m32 : addBits.m32 = false)
    (h_add_set_pc : addBits.set_pc = false)
    (h_add_a_src_imm : addBits.a_src_imm = true)
    (h_add_b_src_imm :
      addBits.b_src_imm = decide ((regidx_to_fin c.rs1).val = 0))
    (h_add_b_src_reg :
      addBits.b_src_reg = decide ((regidx_to_fin c.rs1).val ≠ 0))
    (andBits : RomFlagBits)
    (h_and_ieo : andBits.is_external_op = true)
    (h_and_m32 : andBits.m32 = false)
    (h_and_set_pc : andBits.set_pc = true)
    (h_and_store_pc :
      andBits.store_pc = decide ((regidx_to_fin c.rd).val ≠ 0))
    (h_and_store_ind : andBits.store_ind = false)
    (h_and_b_src_imm : andBits.b_src_imm = false)
    (h_and_b_src_mem : andBits.b_src_mem = false)
    (h_and_b_src_ind : andBits.b_src_ind = false)
    (h_and_b_src_reg : andBits.b_src_reg = false)
    (h_prog_add : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset2 = 1
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).a_offset_imm0.val
                  + (trace.program j).a_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags addBits)
    (h_prog_and : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc (i.val + 1) →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 0
        ∧ (trace.program j).jmp_offset2 = 3
        ∧ (trace.program j).store_offset =
            (if (regidx_to_fin c.rd).val = 0 then 0
             else Transpiler.ind (regidx_to_fin c.rd))
        ∧ (trace.program j).flags = packFlags andBits) :
    Decode_jalr trace i c := by
  have h_lt_start : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_lt_finish : i.val + 1 < trace.mainTable.table.length := by omega
  -- `Decode_jalr` lives in `Type`, so every `Exists` elimination on the ROM
  -- binding must be bagged into a Prop-valued `have` before the structure is
  -- built (large elimination is not available in the goal itself). Same shape
  -- as the aligned constructor's `have key`, once per committed row.
  have keyAdd :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 1 ∧
      (mainRowWithRomAt trace ⟨i.val, h_lt_start⟩).rom.b_src_imm =
        ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rs1).val = 0)) ∧
      (mainRowWithRomAt trace ⟨i.val, h_lt_start⟩).rom.b_src_reg =
        ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rs1).val ≠ 0)) := by
    obtain ⟨ja, hlinea, hopa, _, _, hjmp2a, hflagsa⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt_start⟩
    obtain ⟨hpoa, hpj2a, _, hpfa⟩ := h_prog_add ja hlinea
    have hroma := hflagsa.symm.trans hpfa
    obtain ⟨pa_ieo, pa_m32, pa_set_pc, _⟩ :=
      mainFlagColumns_of_packFlags_at trace ⟨i.val, h_lt_start⟩ addBits hroma
    obtain ⟨_, _, _, _, pa_b_src_reg, _⟩ :=
      mainMemorySelectorColumns_of_packFlags_at trace ⟨i.val, h_lt_start⟩ addBits hroma
    have pa_b_src_imm :=
      mainBSourceImmColumn_of_packFlags_at trace ⟨i.val, h_lt_start⟩ addBits hroma
    exact ⟨hopa.symm.trans hpoa,
      by rw [pa_ieo, h_add_ieo, ZiskFv.AirsClean.boolF_true],
      by rw [pa_m32, h_add_m32, ZiskFv.AirsClean.boolF_false],
      by rw [pa_set_pc, h_add_set_pc, ZiskFv.AirsClean.boolF_false],
      hjmp2a.symm.trans hpj2a,
      by rw [pa_b_src_imm, h_add_b_src_imm],
      by rw [pa_b_src_reg, h_add_b_src_reg]⟩
  -- The ADD row's `a` lane carries the committed immediate: `a_src_imm = 1`
  -- turns `SourceSpec` into `a_0 = a_offset_imm0`, `a_1 = a_imm1`, and the ROM
  -- message ties both limbs to the committed program entry.
  have h_a_lane :
      BitVec.ofNat 64
          (((mainOfTable trace.program trace.mainTable).a_0 i.val).val
            + ((mainOfTable trace.program trace.mainTable).a_1 i.val).val * 4294967296)
        = BitVec.signExtend 64 c.imm := by
    obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace ⟨i.val, h_lt_start⟩
    have hline : (trace.program j).line
        = (mainOfTable trace.program trace.mainTable).pc i.val := by
      simp only [← hj, romMessage, mainOfTable_pc]
    obtain ⟨_, _, h_imm, hpf⟩ := h_prog_add j hline
    have hrom : romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val)
        = packFlags addBits := by
      have hflags : (trace.program j).flags
          = romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val) := by
        simp only [← hj, romMessage]
      exact hflags.symm.trans hpf
    have h_asi :
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_src_imm = 1 := by
      simpa only [h_add_a_src_imm, ZiskFv.AirsClean.boolF_true]
        using mainASourceImmColumn_of_packFlags_at trace ⟨i.val, h_lt_start⟩ addBits hrom
    obtain ⟨h_a0, h_a1, _, _⟩ := mainSourceSpec_at trace ⟨i.val, h_lt_start⟩
    rw [h_asi, one_mul] at h_a0 h_a1
    have e_a0 : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.a_0
        = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_offset_imm0 := by
      apply sub_eq_zero.mp; simpa [sub_eq_add_neg] using h_a0
    have e_a1 : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.a_1
        = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_imm1 := by
      apply sub_eq_zero.mp; simpa [sub_eq_add_neg] using h_a1
    have h_off : (trace.program j).a_offset_imm0
        = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_offset_imm0 := by
      simp only [← hj, romMessage]
    have h_hi : (trace.program j).a_imm1
        = (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_imm1 := by
      simp only [← hj, romMessage]
    rw [h_off, h_hi] at h_imm
    simpa only [mainOfTable_a_0, mainOfTable_a_1, e_a0, e_a1] using h_imm.symm
  have keyAnd :
      (mainOfTable trace.program trace.mainTable).op (i.val + 1) = ZiskFv.Trusted.OP_AND ∧
      (mainOfTable trace.program trace.mainTable).is_external_op (i.val + 1) = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 (i.val + 1) = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc (i.val + 1) = 1 ∧
      (mainOfTable trace.program trace.mainTable).store_pc (i.val + 1) =
        ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0)) ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 (i.val + 1) = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 (i.val + 1) = 3 ∧
      (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.b_src_imm = 0 ∧
      (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.b_src_mem = 0 ∧
      (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.b_src_ind = 0 ∧
      (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.b_src_reg = 0 ∧
      (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.store_ind = 0 ∧
      (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.store_offset
        = (if (regidx_to_fin c.rd).val = 0 then 0 else
            Transpiler.ind (regidx_to_fin c.rd)) := by
    obtain ⟨jb, hlineb, hopb, _, hjmp1b, hjmp2b, hflagsb⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val + 1, h_lt_finish⟩
    obtain ⟨hpob, hpj1b, hpj2b, _, hpfb⟩ := h_prog_and jb hlineb
    have hromb := hflagsb.symm.trans hpfb
    obtain ⟨pb_ieo, pb_m32, pb_set_pc, pb_store_pc⟩ :=
      mainFlagColumns_of_packFlags_at trace ⟨i.val + 1, h_lt_finish⟩ andBits hromb
    obtain ⟨pb_b_mem, _, _, pb_b_ind, pb_b_reg, _⟩ :=
      mainMemorySelectorColumns_of_packFlags_at trace ⟨i.val + 1, h_lt_finish⟩ andBits hromb
    have pb_b_imm :=
      mainBSourceImmColumn_of_packFlags_at trace ⟨i.val + 1, h_lt_finish⟩ andBits hromb
    have h_dest :
        (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.store_ind = 0 ∧
        (mainRowWithRomAt trace ⟨i.val + 1, h_lt_finish⟩).rom.store_offset =
          (if (regidx_to_fin c.rd).val = 0 then 0 else
            Transpiler.ind (regidx_to_fin c.rd)) := by
      obtain ⟨_, _, p_store_ind, _, _, _⟩ :=
        mainMemorySelectorColumns_of_packFlags_at trace ⟨i.val + 1, h_lt_finish⟩
          andBits hromb
      refine ⟨by
        simpa [h_and_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind, ?_⟩
      obtain ⟨j, hline, hstore⟩ :=
        mainStoreOffset_at_eq_program trace ⟨i.val + 1, h_lt_finish⟩
      obtain ⟨_, _, _, hpso, _⟩ := h_prog_and j hline
      simpa [mainRowWithRomAt] using hstore.symm.trans hpso
    exact ⟨hopb.symm.trans hpob,
      by rw [pb_ieo, h_and_ieo, ZiskFv.AirsClean.boolF_true],
      by rw [pb_m32, h_and_m32, ZiskFv.AirsClean.boolF_false],
      by rw [pb_set_pc, h_and_set_pc, ZiskFv.AirsClean.boolF_true],
      by rw [pb_store_pc, h_and_store_pc],
      hjmp1b.symm.trans hpj1b,
      hjmp2b.symm.trans hpj2b,
      by rw [pb_b_imm, h_and_b_src_imm, ZiskFv.AirsClean.boolF_false],
      by rw [pb_b_mem, h_and_b_src_mem, ZiskFv.AirsClean.boolF_false],
      by rw [pb_b_ind, h_and_b_src_ind, ZiskFv.AirsClean.boolF_false],
      by rw [pb_b_reg, h_and_b_src_reg, ZiskFv.AirsClean.boolF_false],
      h_dest.1, h_dest.2⟩
  exact
    { rows :=
        { start := ⟨i.val, h_lt_start⟩
          finish := ⟨i.val + 1, h_lt_finish⟩
          architectural_start := rfl
          finish_has_successor := by simpa using h_idx2
          lowering := Or.inr ⟨rfl, h_offset_zero, keyAdd.1, keyAdd.2.1, keyAdd.2.2.1,
            h_flag_add, keyAdd.2.2.2.1, keyAdd.2.2.2.2.1, h_a_lane,
            keyAdd.2.2.2.2.2.1, keyAdd.2.2.2.2.2.2,
            keyAnd.2.2.2.2.2.2.2.1, keyAnd.2.2.2.2.2.2.2.2.1,
            keyAnd.2.2.2.2.2.2.2.2.2.1, keyAnd.2.2.2.2.2.2.2.2.2.2.1⟩ }
      h_main_op := keyAnd.1
      h_main_active := keyAnd.2.1
      h_flag := h_flag
      h_m32 := keyAnd.2.2.1
      h_set_pc := keyAnd.2.2.2.1
      h_store_pc := keyAnd.2.2.2.2.1
      h_store_ind := keyAnd.2.2.2.2.2.2.2.2.2.2.2.1
      h_store_offset := keyAnd.2.2.2.2.2.2.2.2.2.2.2.2
      h_store_reg := sorry
      h_idx := by simpa using h_idx2
      h_a_mask_lo := h_a_mask_lo
      h_a_mask_hi := h_a_mask_hi
      h_c1_zero := h_c1_zero
      h_jmp2 := Or.inr ⟨rfl, keyAnd.2.2.2.2.2.2.1⟩
      h_offset_bridge := by
        rw [keyAnd.2.2.2.2.2.1, h_offset_zero]
        norm_num
      h_offset_even := h_offset_even
      h_target_nonneg := h_target_nonneg
      h_target_lt := h_target_lt
      h_start_store_reg_zero := sorry }


/-! ## Family: FENCE -/

/-- `Decode_fence` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_fence_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_fence trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_fm_zero :
    c.fm = 0#4)
    (h_rs_x0 :
    ZiskFv.Compliance.Defects.IsX0Reg c.rs)
    (h_rd_x0 :
    ZiskFv.Compliance.Defects.IsX0Reg c.rd)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_prog : ∀ j : Fin trace.programLength,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_fence trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_FLAG ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, _, hj1, hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, _⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_jmp1 := key.2.2.2.1
      h_jmp2 := key.2.2.2.2
      h_store_reg := sorry
      h_idx := h_idx
      h_fm_zero := h_fm_zero
      h_rs_x0 := h_rs_x0
      h_rd_x0 := h_rd_x0 }


end ZiskFv.Compliance.RomDecodeBinding
