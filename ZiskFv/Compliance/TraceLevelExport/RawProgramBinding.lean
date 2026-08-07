import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Dispatch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.DynamicFields
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves

/-!
# Raw-program binding through the production ZisK lowerer

This module makes the committed ROM message's ADD decode fields **derived** from
the raw RISC-V instruction word, via the REAL Aeneas transpile pipeline
(`extract_transpile_rv64im_raw`, `trust/aeneas/ProductionM2.lean`).

Block 1 (`RomDecodeBinding.Decode_add_of_program`) tied the witness row's decode
columns to the committed program `trace.program`.  This block ties the committed
program entry to its raw instruction word: the op-agnostic `ProgramBinding`
certificate states the committed ROM holds exactly the serialized lowering of the
raw program.  For the ADD case the chain closes — `Decode_add_from_rawProgram`
rebuilds `Decode_add` from `rawProgram` + `ProgramBinding` + the ADD-branch of the
(eventual exhaustive) per-entry raw-word split.

Op-AGNOSTIC: `serializeExtract` / `romMessageOfRaw` / `ProgramBinding` run ONE
pipeline for every word; ADD-ness enters only via the `rawRType … 0x33` raw-word
hypothesis (the ADD case of an exhaustive split), never as a trust premise.

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).  The lowering totality is proven
with the kernel-sound `System.Platform.numBits` casing (the same register-bound
lemmas as `…/Extraction/Helpers.lean`), NOT `native_decide` (the production
RV-completeness harness uses `native_decide`; this in-build pilot does not).
-/

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)

set_option maxHeartbeats 8000000

/-! ## Op-agnostic serialization of the lowered row into the committed ROM message. -/

/-- Op-agnostic flag-bit extraction from a lowered ZiskInstExtract: the five
    decode-relevant flags are faithful direct copies of the lowered booleans; the
    operand-source / store selector bits are the op-agnostic selector decode
    (operand-side, out of decode scope — not consumed by per-op decode). -/
def romFlagBitsOfExtract (e : zisk_core.aeneas_extract.ZiskInstExtract) : RomFlagBits where
  a_src_imm := decide (e.a_src = zisk_core.zisk_inst.SRC_IMM)
  a_src_mem := decide (e.a_src = zisk_core.zisk_inst.SRC_MEM)
  is_precompiled := e.is_precompiled
  b_src_imm := decide (e.b_src = zisk_core.zisk_inst.SRC_IMM)
  b_src_mem := decide (e.b_src = zisk_core.zisk_inst.SRC_MEM)
  is_external_op := e.is_external_op
  store_pc := e.store_pc
  store_mem := decide (e.store = zisk_core.zisk_inst.STORE_MEM)
  store_ind := decide (e.store = zisk_core.zisk_inst.STORE_IND)
  set_pc := e.set_pc
  m32 := e.m32
  b_src_ind := decide (e.b_src = zisk_core.zisk_inst.SRC_IND)
  a_src_reg := decide (e.a_src = zisk_core.zisk_inst.SRC_REG)
  b_src_reg := decide (e.b_src = zisk_core.zisk_inst.SRC_REG)
  store_reg := decide (e.store = zisk_core.zisk_inst.STORE_REG)

/-- Interpret a lowered unsigned 64-bit offset as the signed `i64` used by the
    production ROM emitter, then embed it in the proof field (`rom.rs:226-236`). -/
def signedOffset (x : Std.U64) : FGL := (x.bv.toInt : FGL)

/-- The production ROM emitter stores stack-immediate selectors only for an
    immediate source (`rom.rs:240-244`). -/
def sourceImmediate (src useSp : Std.U64) : FGL :=
  if src = zisk_core.zisk_inst.SRC_IMM then (useSp.val : FGL) else 0

/-- The three free-input opcodes share CopyB's ROM-table semantics
    (`rom.rs:252-260`). Production RV64IM lowering does not emit these codes,
    but the serializer mirrors the generic emitter. -/
def romOpcode (op : Std.U8) : FGL :=
  if op.val = 246 ∨ op.val = 247 ∨ op.val = 248 then 1 else (op.val : FGL)

/-- Op-agnostic serialization of a lowered row into the committed FGL ROM message.
    This is the proof-facing transcription of `rom.rs:204-260`. -/
def serializeExtract (line : FGL) (e : zisk_core.aeneas_extract.ZiskInstExtract) :
    ZiskRomMessage FGL where
  line := line                                                        -- rom.rs:246
  a_offset_imm0 := signedOffset e.a_offset_imm0                       -- rom.rs:226-230,247
  a_imm1 := sourceImmediate e.a_src e.a_use_sp_imm1                   -- rom.rs:240-241,248
  b_offset_imm0 := signedOffset e.b_offset_imm0                       -- rom.rs:232-236,249
  b_imm1 := sourceImmediate e.b_src e.b_use_sp_imm1                   -- rom.rs:242-244,250
  ind_width := (e.ind_width.val : FGL)                                -- rom.rs:251
  op := romOpcode e.op                                                -- rom.rs:252-260
  store_offset := (e.store_offset.val : FGL)                          -- rom.rs:215-219,261
  jmp_offset1 := (e.jmp_offset1.val : FGL)                            -- rom.rs:205-209,262
  jmp_offset2 := (e.jmp_offset2.val : FGL)                            -- rom.rs:210-214,263
  flags := packFlags (romFlagBitsOfExtract e)                         -- rom.rs:264

/-- Independently named ROM-row transcription used at the program-image boundary.
    It is a separate definition from `serializeExtract` to give that boundary its own
    stable handle; `romRowOf_eq_serializeExtract` proves the two agree definitionally
    (`rfl`). That catches editing one transcription without the other, but it is a
    consistency check between two hand-written transcriptions — not a check against the
    Rust source. -/
def romRowOf (line : FGL) (e : zisk_core.aeneas_extract.ZiskInstExtract) :
    ZiskRomMessage FGL where
  line := line
  a_offset_imm0 := signedOffset e.a_offset_imm0
  a_imm1 := if e.a_src = zisk_core.zisk_inst.SRC_IMM then (e.a_use_sp_imm1.val : FGL) else 0
  b_offset_imm0 := signedOffset e.b_offset_imm0
  b_imm1 := if e.b_src = zisk_core.zisk_inst.SRC_IMM then (e.b_use_sp_imm1.val : FGL) else 0
  ind_width := (e.ind_width.val : FGL)
  op := if e.op.val = 246 ∨ e.op.val = 247 ∨ e.op.val = 248 then 1 else (e.op.val : FGL)
  store_offset := (e.store_offset.val : FGL)
  jmp_offset1 := (e.jmp_offset1.val : FGL)
  jmp_offset2 := (e.jmp_offset2.val : FGL)
  flags := packFlags (romFlagBitsOfExtract e)

theorem romRowOf_eq_serializeExtract (line : FGL)
    (e : zisk_core.aeneas_extract.ZiskInstExtract) :
    romRowOf line e = serializeExtract line e := by
  rfl

/-- The committed ROM message a raw RISC-V word must serialize to: run the REAL
    Aeneas transpile pipeline on the word and FGL-serialize its lowered row. A
    raw word the pipeline rejects maps to the all-zero message (never matched by a
    supported decode). Op-AGNOSTIC: one pipeline for every word. -/
noncomputable def romMessageOfRaw (line : FGL) (raw : BitVec 32) : ZiskRomMessage FGL :=
  match zisk_core.aeneas_extract.extract_transpile_rv64im_raw (ZiskFv.Compliance.Decode.toU32 raw) with
  | .ok ext => romRowOf line ext.row
  | _ => { line := line, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0,
           b_imm1 := 0, ind_width := 0, op := 0, store_offset := 0,
           jmp_offset1 := 0, jmp_offset2 := 0, flags := 0 }

/-- The complete production lowering of one raw word. Most words have one row;
    an unaligned JALR has its intermediate ADD row followed by its terminal AND
    row. The existing `romMessageOfRaw` remains the terminal-row projection. -/
noncomputable def romMessagesOfRaw (line : FGL) (raw : BitVec 32) :
    ZiskRomMessage FGL × Option (ZiskRomMessage FGL) :=
  match zisk_core.aeneas_extract.extract_transpile_rv64im_rows_raw
      (ZiskFv.Compliance.Decode.toU32 raw) with
  | .ok ext =>
      if ext.row_count = 2#u32 then
        (romRowOf line ext.first_row, some (romRowOf (line + 1) ext.last_row))
      else
        (romRowOf line ext.last_row, none)
  | _ => (romMessageOfRaw line raw, none)

/-- A successfully lowered non-JALR word has exactly one physical row, namely
    the existing terminal-row projection. -/
theorem romMessagesOfRaw_fst_of_non_jalr (line : FGL) (raw : BitVec 32)
    (ext : aeneas_extract.Rv64imTranspileExtract)
    (hok : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok ext)
    (hnon : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32) :
    (romMessagesOfRaw line raw).1 = romMessageOfRaw line raw := by
  unfold romMessagesOfRaw romMessageOfRaw
  rw [aeneas_extract.extract_transpile_rv64im_rows_raw, hok]
  simp only [lift, Bind.bind, bind_ok, hnon, if_false]
  norm_num [UScalar.val]

/-- Op-agnostic ROM-image binding (a verifier-attached certificate, NOT an axiom):
    the committed ROM holds exactly the serialized lowering of the raw program. -/
def ProgramBinding {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (addr : Fin trace.programLength → FGL)
    (rawProgram : Fin trace.programLength → BitVec 32) : Prop :=
  (∀ k k' : Fin trace.programLength, k < k' → (addr k).val < (addr k').val) ∧
  ∀ k : Fin trace.programLength, trace.program k = romMessageOfRaw (addr k) (rawProgram k)

/-- Additive program-image binding for production lowerings with one or two rows.
    `start` embeds architectural raw-word indices into physical ROM indices.
    The separation condition prevents a two-row lowering from overlapping the
    next word. Existing one-word/one-row clients keep using `ProgramBinding`. -/
def ProgramRowsBinding {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) : Prop :=
  (∀ k k' : Fin rawLength, k < k' →
      (start k).val < (start k').val ∧ (addr k).val < (addr k').val) ∧
  (∀ k : Fin rawLength, (addr k).val % 4 = 0) ∧
  (∀ k : Fin rawLength, (addr k).val + 1 < GL_prime) ∧
  (∀ k k' : Fin rawLength, k < k' →
      match (romMessagesOfRaw (addr k) (rawProgram k)).2 with
      | none => (start k).val + 1 ≤ (start k').val
      | some _ => (start k).val + 2 ≤ (start k').val) ∧
  (∀ k : Fin rawLength,
      let rows := romMessagesOfRaw (addr k) (rawProgram k)
      trace.program (start k) = rows.1 ∧
        match rows.2 with
        | none => True
        | some row =>
            ∃ h : (start k).val + 1 < trace.programLength,
              trace.program ⟨(start k).val + 1, h⟩ = row) ∧
  ∀ j : Fin trace.programLength,
    ∃ k : Fin rawLength,
      j = start k ∨
        ∃ row : ZiskRomMessage FGL,
          (romMessagesOfRaw (addr k) (rawProgram k)).2 = some row ∧
            j.val = (start k).val + 1

/-- Faithful architectural lookup at the first physical row of a lowered word.
    Unlike a physical-indexed raw array, this never duplicates an instruction
    word to account for expansion rows. -/
def RawAtProgramStart {programLength rawLength : Nat}
    (start : Fin rawLength → Fin programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (j : Fin programLength) (line : FGL) (raw : BitVec 32) : Prop :=
  ∃ k : Fin rawLength, start k = j ∧ addr k = line ∧ rawProgram k = raw

theorem romMessagesOfRaw_first_line (line : FGL) (raw : BitVec 32) :
    (romMessagesOfRaw line raw).1.line = line := by
  unfold romMessagesOfRaw
  split
  · split <;> rfl
  · unfold romMessageOfRaw
    split <;> rfl

theorem romMessagesOfRaw_second_line {line : FGL} {raw : BitVec 32}
    {row : ZiskRomMessage FGL}
    (hsecond : (romMessagesOfRaw line raw).2 = some row) :
    row.line = line + 1 := by
  unfold romMessagesOfRaw at hsecond
  split at hsecond
  · split at hsecond
    · simp only [Option.some.injEq] at hsecond
      rw [← hsecond]
      rfl
    · simp at hsecond
  · simp at hsecond

/-- Reuse bridge for the existing one-row opcode proofs: architectural lookup
    plus `ProgramRowsBinding` gives the same primary-row equality those proofs
    previously obtained from a physical-indexed `ProgramBinding`. -/
theorem primary_row_of_programRowsBinding {n rawLength : Nat}
    {trace : ZiskFv.Compliance.AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength}
    {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    {j : Fin trace.programLength} {line : FGL} {raw : BitVec 32}
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (hlookup : RawAtProgramStart start addr rawProgram j line raw) :
    trace.program j = (romMessagesOfRaw line raw).1 := by
  obtain ⟨_, _, _, _, hrows, _⟩ := hbind
  obtain ⟨k, rfl, rfl, rfl⟩ := hlookup
  exact (hrows k).1

/-- Expansion bridge: when the lowering exposes a second row, the committed
    physical successor is exactly that row. This is the JALR ADD-to-AND join. -/
theorem successor_row_of_programRowsBinding {n rawLength : Nat}
    {trace : ZiskFv.Compliance.AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength}
    {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    {j : Fin trace.programLength} {line : FGL} {raw : BitVec 32}
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (hlookup : RawAtProgramStart start addr rawProgram j line raw)
    {row : ZiskRomMessage FGL}
    (hsecond : (romMessagesOfRaw line raw).2 = some row) :
    ∃ h : j.val + 1 < trace.programLength,
      trace.program ⟨j.val + 1, h⟩ = row := by
  obtain ⟨_, _, _, _, hrows, _⟩ := hbind
  obtain ⟨k, rfl, rfl, rfl⟩ := hlookup
  simpa [hsecond] using (hrows k).2

/-- Exact physical-row coverage: every committed row is either an
    architectural word's primary lowering row or that word's present expansion
    successor. In particular there are no unbound gap rows. -/
theorem physical_row_of_programRowsBinding {n rawLength : Nat}
    {trace : ZiskFv.Compliance.AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength}
    {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (j : Fin trace.programLength) :
    ∃ k : Fin rawLength,
      (j = start k ∧
        trace.program j = (romMessagesOfRaw (addr k) (rawProgram k)).1) ∨
      ∃ row : ZiskRomMessage FGL,
        (romMessagesOfRaw (addr k) (rawProgram k)).2 = some row ∧
          j.val = (start k).val + 1 ∧ trace.program j = row := by
  obtain ⟨_, _, _, _, hrows, hcover⟩ := hbind
  obtain ⟨k, hj | ⟨row, hsecond, hj⟩⟩ := hcover j
  · exact ⟨k, Or.inl ⟨hj, hj ▸ (hrows k).1⟩⟩
  · obtain ⟨hnext, hrow⟩ := by
      simpa [hsecond] using (hrows k).2
    have hfin : j = ⟨(start k).val + 1, hnext⟩ := Fin.ext hj
    exact ⟨k, Or.inr ⟨row, hsecond, hj, hfin ▸ hrow⟩⟩

/-- Legacy one-row adapter. Exact physical coverage, four-byte architectural
    alignment, and successor no-wrap imply that any row whose committed line
    is an architectural address is that word's primary row, never an expansion
    successor. -/
theorem primary_row_at_architectural_line {n rawLength : Nat}
    {trace : ZiskFv.Compliance.AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength}
    {addr : Fin rawLength → FGL}
    {rawProgram : Fin rawLength → BitVec 32}
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (j : Fin trace.programLength) (k₀ : Fin rawLength)
    (hline : (trace.program j).line = addr k₀) :
    j = start k₀ ∧
      trace.program j = (romMessagesOfRaw (addr k₀) (rawProgram k₀)).1 := by
  have hbind' := hbind
  obtain ⟨horder, halign, hnowrap, _, _, _⟩ := hbind
  obtain ⟨k, ⟨hj, hrow⟩ | ⟨row, hsecond, _, hrow⟩⟩ :=
    physical_row_of_programRowsBinding hbind' j
  · have ha : addr k = addr k₀ := by
      have := hline
      rw [hrow, romMessagesOfRaw_first_line] at this
      exact this
    have hk : k = k₀ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := (horder k k₀ hlt).2
        rw [ha] at this
        omega
      · have := (horder k₀ k hgt).2
        rw [ha] at this
        omega
    subst k
    exact ⟨hj, hrow⟩
  · have hrowline := romMessagesOfRaw_second_line hsecond
    have heq : addr k + 1 = addr k₀ := by
      rw [← hrowline, ← hline, hrow]
    have heqv := congrArg Fin.val heq
    simp [Fin.add_def, Nat.mod_eq_of_lt (hnowrap k)] at heqv
    have hkmod := halign k
    have hk₀mod := halign k₀
    omega

end ZiskFv.Compliance.RawProgramBinding
