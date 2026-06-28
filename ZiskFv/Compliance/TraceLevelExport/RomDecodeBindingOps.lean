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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SUB_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MUL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (pins :
    ZiskFv.Compliance.MainRowPins
      (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV)
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
      pins := pins
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
    (pins :
    ZiskFv.Compliance.MainRowPins
      (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM)
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
      pins := pins
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
    (pins :
    ZiskFv.Compliance.MainRowPins
      (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV_W)
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
      pins := pins
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
    (pins :
    ZiskFv.Compliance.MainRowPins
      (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM_W)
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
      pins := pins
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULUH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIVU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIVU_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REMU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REMU_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
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
      bounds := bounds }


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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (8 : FGL)
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
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
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
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
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
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
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
      h_width := key.2.2.2.2.2.2
      h_idx := h_idx }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_B
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
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
      h_match := h_match }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_H
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
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
      h_match := h_match }

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
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
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
    obtain ⟨hpo, hpj0, hpj1, hpiw, hpf⟩ := h_prog j hline
    obtain ⟨p_ieo, _, p_set_pc, p_store_pc⟩ :=
      mainFlagColumns_of_packFlags trace i h_lt bits (hflags.symm.trans hpf)
    exact ⟨hop.symm.trans hpo, by rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true], by rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false], by rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false], hj1.symm.trans hpj0, hj2.symm.trans hpj1, hiw.symm.trans hpiw⟩
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
      h_match := h_match }


end ZiskFv.Compliance.RomDecodeBinding

