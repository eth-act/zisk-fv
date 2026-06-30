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
    ∃ j : Fin trace.numInstructions,
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
    ∃ j : Fin trace.numInstructions,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc idx.val
    ∧ (trace.program j).store_offset
        = (mainTableRowAtOrZero trace.program trace.mainTable idx.val).rom.store_offset := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace idx
  refine ⟨j, ?_, ?_⟩ <;>
    simp only [← hj, romMessage, mainOfTable_pc]

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
        = ZiskFv.AirsClean.boolF bits.store_pc := by
  obtain ⟨a, b, d, e⟩ := romFlagColumns_of_romFlags_eq_packFlags
    (mainTableRowAtOrZero trace.program trace.mainTable i.val) bits
    (mainRow_flags_boolean trace ⟨i.val, h_lt⟩) h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mainOfTable_is_external_op] using a
  · simpa only [mainOfTable_m32] using b
  · simpa only [mainOfTable_set_pc] using d
  · simpa only [mainOfTable_store_pc] using e

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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

/-- `Decode_slli` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_slli_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slli trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx
      h_b_lo_t := h_b_lo_t }

/-- `Decode_srli` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srli_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srli trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx
      h_b_lo_t := h_b_lo_t }

/-- `Decode_srai` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_srai_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srai trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx
      h_b_lo_t := h_b_lo_t }


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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx }


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
    (h_prog : ∀ j : Fin numInstructions,
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MUL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULSUH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIV
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REM
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIV_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
    (bounds :
    ZiskFv.Compliance.ByteBounds c.bus.e2)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = true)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REM_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 rd)
        ∧ (trace.program j).flags = packFlags bits) :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  ∧ (mainRowWithRomLd trace i).rom.store_reg = 1
  ∧ (mainRowWithRomLd trace i).rom.store_offset =
      Transpiler.ind (Transpiler.regidxOfBitVec5 rd) := by
  obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
    mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
  obtain ⟨_hpso, hpf⟩ := h_prog j hline
  obtain ⟨p_store_ind, _, p_store_reg⟩ :=
    mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
  have h_store_ind : (mainRowWithRomLd trace i).rom.store_ind = 0 := by
    simpa [mainRowWithRomLd, h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind
  have h_store_reg : (mainRowWithRomLd trace i).rom.store_reg = 1 := by
    simpa [mainRowWithRomLd, h_bits_store_reg, ZiskFv.AirsClean.boolF_true] using p_store_reg
  have h_store_offset :
      (mainRowWithRomLd trace i).rom.store_offset =
        Transpiler.ind (Transpiler.regidxOfBitVec5 rd) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hstore.symm.trans hpso
  exact ⟨h_store_ind, h_store_reg, h_store_offset⟩


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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (8 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_store_ind : (mainRowWithRomLd trace i).rom.store_ind = 0 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_store_ind, _, _p_store_reg⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomLd, h_bits_store_ind, ZiskFv.AirsClean.boolF_false] using p_store_ind
  have h_store_reg : (mainRowWithRomLd trace i).rom.store_reg = 1 := by
    obtain ⟨j, hline, _hop, _hiw, _hj1, _hj2, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨_p_store_ind, _, p_store_reg⟩ :=
      mainSelectorColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    simpa [mainRowWithRomLd, h_bits_store_reg, ZiskFv.AirsClean.boolF_true] using p_store_reg
  have h_store_offset :
      (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.ld_input.rd) := by
    obtain ⟨j, hline, hstore⟩ := mainStoreOffset_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, _hpf⟩ := h_prog j hline
    simpa [mainRowWithRomLd] using hstore.symm.trans hpso
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
      h_store_offset := h_store_offset }

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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lbu_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
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
      h_store_offset := h_dest.2.2 }

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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lhu_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
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
      h_store_offset := h_dest.2.2 }

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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lwu_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
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
      h_store_offset := h_dest.2.2 }

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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_B
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lb_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
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
      h_store_offset := h_dest.2.2 }

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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_H
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lh_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
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
      h_store_offset := h_dest.2.2 }

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
    (h_bits_store_reg : bits.store_reg = true)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  have h_dest := mainLoadDestinationFacts_of_program trace i h_lt bits c.lw_input.rd
    h_bits_store_ind h_bits_store_reg (fun j hline => by
      obtain ⟨_hpo, _hpj0, _hpj1, _hpiw, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
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
      h_store_offset := h_dest.2.2 }


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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 1
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_main_ind_width := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 2
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_main_ind_width := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.1
      h_main_ind_width := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    obtain ⟨hpo, hpj0, hpj1, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_set_pc := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_jmp1 := key.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_auipc trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_dest := mainLuiDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
    (fun j hline => by
      obtain ⟨_hpo, _hpj0, hpso, hpf⟩ := h_prog j hline
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
    obtain ⟨hpo, hpj0, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_true], hj1.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_jmp1 := key.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_EQ
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
    obtain ⟨hpo, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj2.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_EQ
        ∧ (trace.program j).jmp_offset1 = 4
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
    obtain ⟨hpo, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
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
    obtain ⟨hpo, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj2.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
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
    obtain ⟨hpo, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
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
    obtain ⟨hpo, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj2.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset2 := key.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
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
    obtain ⟨hpo, hpj0, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_jmp_offset1 := key.2.2.2.2.2
      h_idx := h_idx }


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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_jal trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_dest := mainLuiDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
    (fun j hline => by
      obtain ⟨_hpo, _hpj0, hpso, hpf⟩ := h_prog j hline
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
    obtain ⟨hpo, hpj0, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_false], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_true], hj2.symm.trans hpj0⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2.1
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_jmp2 := key.2.2.2.2.2
      h_idx := h_idx }

/-- `Decode_jalr` rebuilt from the committed program via the ROM lookup
    (issue #159 block 1).  ROM-message-backed decode columns are DERIVED
    from `trace.program`; non-ROM pins (if any) are passthrough. -/
def Decode_jalr_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
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
    (h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val = c.offset_bv.toNat)
    (h_offset_even :
    c.offset_bv &&& 1#64 = 0#64)
    (h_no_fgl_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0 i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
          i.val).val < GL_prime)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = true)
    (h_bits_store_pc : bits.store_pc = true)
    (h_bits_store_ind : bits.store_ind = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_jalr trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  have h_dest := mainLuiDestinationFacts_of_program trace i h_lt bits c.rd h_bits_store_ind
    (fun j hline => by
      obtain ⟨_hpo, hpso, hpf⟩ := h_prog j hline
      exact ⟨hpso, hpf⟩)
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND ∧
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 1 ∧
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 1 := by
    obtain ⟨j, hline, hop, _, _, _, hflags⟩ :=
      mainRomColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, _hpso, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_true], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_true]⟩
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_set_pc := key.2.2.2.1
      h_store_pc := key.2.2.2.2
      h_store_ind := h_dest.1
      h_store_offset := h_dest.2
      h_idx := h_idx
      h_flag := h_flag
      h_a_mask_lo := h_a_mask_lo
      h_a_mask_hi := h_a_mask_hi
      h_c1_zero := h_c1_zero
      h_offset_bridge := h_offset_bridge
      h_offset_even := h_offset_even
      h_no_fgl_wrap := h_no_fgl_wrap }


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
    (h_prog : ∀ j : Fin numInstructions,
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
      h_idx := h_idx
      h_fm_zero := h_fm_zero
      h_rs_x0 := h_rs_x0
      h_rd_x0 := h_rd_x0 }


end ZiskFv.Compliance.RomDecodeBinding
