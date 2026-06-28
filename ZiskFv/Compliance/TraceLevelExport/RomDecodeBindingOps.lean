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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SUB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
      h_idx := h_idx }


end ZiskFv.Compliance.RomDecodeBinding

