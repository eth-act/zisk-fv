import Init.Data.UInt.Bitwise
import ZiskFv.AirsClean.NativeTraceRules
import ZiskFv.AirsClean.MemAlignWriteByte.SourceInstance

/-!
INTERNAL finite-cell decoder for exactly six actual trace_row! profiles.
The SINGLE shared renderer supplies declaration ordinals, bit offsets and
source fragments. Raw UInt64 words are read FIRST from the identical original
Params trace; only the extracted field is projected by NativeTraceWords.
No callback, alternate word store, full-trace map, crop, or None->0 exists.

Profile checks describe supported internal inputs, not Root exclusions or new
success premises. Actual metadata/TraceR, setup/PIL/compiled-operand identity,
native machine/ABI and source-image authentication remain unproved. This is
not a production-totality or Accepted-world theorem.
Packed fields model the captured bit-level getter equations. Unpacked fields
are canonical raw F-storage cells, NOT Rust's typed get_<field> return values:
unpacked F2 at a Bool column stays F2 here, whereas that typed getter is true.
No unpacked range/Bool validator or cast-equivalence premise is introduced.
-/
namespace ZiskFv.AirsClean.NativeTraceCells

open Goldilocks Extraction.RuntimeMainTraceLayout
open Extraction.RuntimeMemWriteByteTraceLayout
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource.Native

inductive Kind where
  | main | binary | byte | readByte | mem | writeByte
  deriving DecidableEq

def profile : Kind → Profile
  | .main => mainProfile | .binary => binaryProfile
  | .byte => byteProfile | .readByte => readByteProfile
  | .mem => memProfile | .writeByte => writeByteProfile

def nativeStride (kind : Kind) (packed : Bool) : Nat :=
  if packed then (profile kind).packedWords else (profile kind).unpackedWords

private def mainCells : Array Cell := mainProfile.cells.toArray
private def binaryCells : Array Cell := binaryProfile.cells.toArray
private def byteCells : Array Cell := byteProfile.cells.toArray
private def readByteCells : Array Cell := readByteProfile.cells.toArray
private def memCells : Array Cell := memProfile.cells.toArray
private def writeByteCells : Array Cell := writeByteProfile.cells.toArray

private def cells : Kind → Array Cell
  | .main => mainCells | .binary => binaryCells
  | .byte => byteCells | .readByte => readByteCells
  | .mem => memCells | .writeByte => writeByteCells

/-- No guessed schema or default field is substituted for absent metadata. -/
def selectedCell? (kind : Kind) (column : Nat) : Option Cell :=
  (cells kind)[column]?

/-- Source u128 shift/subtract followed by u64 cast, including width64.
A u64 left shift by64 would be a DIFFERENT algorithm and is not used. -/
def mask (width : Nat) : UInt64 := UInt64.ofNat (2 ^ width - 1)

/-- Source `type_for_bitwidth` classes restricted to the decoder's supported
scalar domain. Unsupported widths are not assigned a fallback cast. -/
def scalarWidth? (width : Nat) : Option Nat :=
  if 0 < width ∧ width ≤ 64 then
    some (if width = 1 then 1 else if width ≤ 8 then 8 else
      if width ≤ 16 then 16 else if width ≤ 32 then 32 else 64)
  else none

theorem scalarWidth_covers (width : Nat) (positive : 0 < width)
    (bounded : width ≤ 64) :
    ∃ bits, scalarWidth? width = some bits ∧ width ≤ bits ∧ bits ≤ 64 := by
  unfold scalarWidth?
  rw [if_pos ⟨positive, bounded⟩]
  split_ifs <;> (refine ⟨_, rfl, ?_, ?_⟩ <;> omega)

theorem mask64 : mask 64 = 18446744073709551615 := by decide +kernel

/-- A contained getter fits its declared width even at the width64 boundary. -/
theorem masked_value_bound (word : UInt64) (width : Nat) (bounded : width ≤ 64) :
    (word &&& mask width).toNat < 2 ^ width := by
  have power : 2 ^ width ≤ 2 ^ 64 :=
    Nat.pow_le_pow_of_le (by decide) bounded
  have positive := Nat.two_pow_pos width
  have limit : 2 ^ width - 1 < UInt64.size := by
    change 2 ^ width - 1 < 2 ^ 64
    omega
  have exactMask : (mask width).toNat = 2 ^ width - 1 :=
    UInt64.toNat_ofNat_of_lt' limit
  change word.toNat &&& (mask width).toNat < 2 ^ width
  exact Nat.and_lt_two_pow _ (by rw [exactMask]; omega)

/-- Rust's unsigned narrowing cast is value-preserving for the source's chosen
return width; the statement is arithmetic, not a Rust compiler/ABI theorem. -/
theorem masked_unsigned_cast (word : UInt64) (width bits : Nat)
    (bounded : width ≤ 64) (covers : width ≤ bits) :
    (word &&& mask width).toNat % 2 ^ bits = (word &&& mask width).toNat := by
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (masked_value_bound word width bounded)
    (Nat.pow_le_pow_of_le (by decide) covers)

/-- Source `raw_value != 0` for width1 has the identical integer value as the
extracted raw bit. This is not an arbitrary field-to-Bool coercion. -/
theorem masked_boolean_value (word : UInt64) :
    (word &&& mask 1).toNat = if word &&& mask 1 = 0 then 0 else 1 := by
  have bounded := masked_value_bound word 1 (by decide)
  by_cases zero : word &&& mask 1 = 0
  · simp [zero]
  · rw [if_neg zero]
    have nonzero : (word &&& mask 1).toNat ≠ 0 := by
      intro equality
      apply zero
      apply UInt64.toNat_inj.mp
      simpa using equality
    change (word &&& mask 1).toNat < 2 at bounded
    omega

theorem boolean_getter_contained (bitOffset : Nat) :
    bitOffset % 64 + 1 ≤ 64 := by
  have := Nat.mod_lt bitOffset (by decide : 0 < 64)
  omega

/-- Both source getter generators join the same two disjoint, masked parts.
The shift amount is strictly below64; no machine shift-by64 or wrap assumption
is substituted for the captured source's split branch. -/
theorem split_value_bound (lowWord highWord : UInt64) (start width : Nat)
    (startBound : start < 64) (widthBound : width ≤ 64)
    (crosses : 64 < start + width) :
    (((highWord &&& mask (width - (64 - start))) <<< UInt64.ofNat (64 - start)) |||
      ((lowWord >>> UInt64.ofNat start) &&& mask (64 - start))).toNat < 2 ^ width := by
  let lowBits := 64 - start
  let highBits := width - lowBits
  have lowPositive : 0 < lowBits := by dsimp [lowBits]; omega
  have lowStrict : lowBits < 64 := by dsimp [lowBits]; omega
  have lowLe : lowBits ≤ width := by dsimp [lowBits]; omega
  have highLe : highBits ≤ 64 := by dsimp [highBits]; omega
  have sum : highBits + lowBits = width := by dsimp [highBits]; omega
  have highBound := masked_value_bound highWord highBits highLe
  have lowBound := masked_value_bound (lowWord >>> UInt64.ofNat start) lowBits (by omega)
  have productBound :
      (highWord &&& mask highBits).toNat * 2 ^ lowBits < 2 ^ width := by
    calc
      _ < 2 ^ highBits * 2 ^ lowBits :=
        Nat.mul_lt_mul_of_pos_right highBound (Nat.two_pow_pos lowBits)
      _ = 2 ^ width := by rw [← Nat.pow_add, sum]
  have exactShift : (UInt64.ofNat lowBits).toNat = lowBits := by
    apply UInt64.toNat_ofNat_of_lt'
    change lowBits < 2 ^ 64
    omega
  have shiftedBound :
      ((highWord &&& mask highBits) <<< UInt64.ofNat lowBits).toNat < 2 ^ width := by
    rw [UInt64.toNat_shiftLeft, exactShift, Nat.mod_eq_of_lt lowStrict, Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) productBound
  change (((highWord &&& mask highBits) <<< UInt64.ofNat lowBits) |||
    ((lowWord >>> UInt64.ofNat start) &&& mask lowBits)).toNat < 2 ^ width
  rw [UInt64.toNat_or]
  exact Nat.or_lt_two_pow shiftedBound
    (Nat.lt_of_lt_of_le lowBound (Nat.pow_le_pow_of_le (by decide) lowLe))

theorem split_unsigned_cast (lowWord highWord : UInt64) (start width bits : Nat)
    (startBound : start < 64) (widthBound : width ≤ 64)
    (crosses : 64 < start + width) (covers : width ≤ bits) :
    (((highWord &&& mask (width - (64 - start))) <<< UInt64.ofNat (64 - start)) |||
      ((lowWord >>> UInt64.ofNat start) &&& mask (64 - start))).toNat % 2 ^ bits =
    (((highWord &&& mask (width - (64 - start))) <<< UInt64.ofNat (64 - start)) |||
      ((lowWord >>> UInt64.ofNat start) &&& mask (64 - start))).toNat := by
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (split_value_bound lowWord highWord start width startBound widthBound crosses)
    (Nat.pow_le_pow_of_le (by decide) covers)

/-- The exact raw-value equations of packed_row.rs contained/split getters.
Array dimensions were flattened by the same emitted source profile; every read
still addresses the original source buffer and may fail explicitly. -/
def packedRaw? (params : RawSource.Params FGL) (base : Nat) (cell : Cell) : Option UInt64 := do
  if 0 < cell.width ∧ cell.width ≤ 64 then
    let word := cell.bitOffset / 64
    let start := cell.bitOffset % 64
    let lowWord ← RawSource.traceWord? params (base + word)
    if start + cell.width ≤ 64 then
      return (lowWord >>> UInt64.ofNat start) &&& mask cell.width
    else
      let lowBits := 64 - start
      let highBits := cell.width - lowBits
      let highWord ← RawSource.traceWord? params (base + word + 1)
      let low := (lowWord >>> UInt64.ofNat start) &&& mask lowBits
      let high := highWord &&& mask highBits
      return (high <<< UInt64.ofNat lowBits) ||| low
  else none

/-- Native stride comes from the selected slot metadata; the source profile
stride and logical cm1 are checked SEPARATELY. Original suffix is retained. -/
def rowBase? {source : SourceObject FGL} (kind : Kind)
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat) : Option Nat := do
  let setup ← resolved.setup?
  let cm1 ← setup.mapSectionsN["cm1"]?
  if NativeTraceRules.ready = true ∧
      resolved.registryEntry.airgroupId = (profile kind).nativeGroup ∧
      resolved.registryEntry.airId = (profile kind).nativeAir ∧
      setup.profile.verify = false ∧ setup.profile.gpu = false ∧
      setup.rowCount = (profile kind).nativeRows ∧ row < setup.rowCount ∧
      cm1 = (profile kind).unpackedWords ∧
      resolved.slotData.metadata.nColsTrace = nativeStride kind resolved.slotData.metadata.isPacked ∧
      0 < resolved.slotData.metadata.nColsTrace ∧
      setup.rowCount * resolved.slotData.metadata.nColsTrace ≤ (resolved.params mode).trace.size then
    some (row * resolved.slotData.metadata.nColsTrace)
  else none

/-- Both modes begin with the SAME original UInt64 buffer. Unsupported source
cells/profiles fail, including a packed cell outside its actual declared bits. -/
def rawCell? {source : SourceObject FGL} (kind : Kind)
    (resolved : ResolvedOccurrence source) (mode : Bool) (row column : Nat) : Option UInt64 := do
  let cell ← selectedCell? kind column
  let base ← rowBase? kind resolved mode row
  if resolved.slotData.metadata.isPacked then
    if cell.bitOffset + cell.width ≤ (profile kind).packedBits then
      packedRaw? (resolved.params mode) base cell
    else none
  else RawSource.traceWord? (resolved.params mode) (base + column)

/-- The owner-supplied concrete native canonicalization is reused verbatim.
It is intentionally AFTER raw bit extraction, never before packed reads. -/
def cell? {source : SourceObject FGL} (kind : Kind)
    (resolved : ResolvedOccurrence source) (mode : Bool) (row column : Nat) : Option FGL :=
  (rawCell? kind resolved mode row column).map RawSource.NativeTraceWords.unpackedField

theorem field_after_raw {source : SourceObject FGL} (kind : Kind)
    (resolved : ResolvedOccurrence source) (mode : Bool) (row column : Nat) :
    cell? kind resolved mode row column =
      (rawCell? kind resolved mode row column).map RawSource.NativeTraceWords.unpackedField := rfl

theorem source_store {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) (index : Nat) :
    RawSource.traceWord? (resolved.params mode) index = resolved.slotData.trace[index]? := rfl

/-- One finite-row request checks its actual source layout once, not39 times.
There is still no decoded buffer or arbitrary reader callback. -/
structure Row {source : SourceObject FGL} (kind : Kind)
    (resolved : ResolvedOccurrence source) (mode : Bool) (index : Nat) where
  base : Nat
  selected : rowBase? kind resolved mode index = some base

def row? {source : SourceObject FGL} (kind : Kind)
    (resolved : ResolvedOccurrence source) (mode : Bool) (index : Nat) :
    Option (Row kind resolved mode index) :=
  match h : rowBase? kind resolved mode index with
  | none => none
  | some base => some ⟨base, h⟩

theorem Row.constructor_recovers {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) :
    row? kind resolved mode index = some view := by
  cases view with
  | mk base hbase =>
    unfold row?
    split
    · rename_i hnone
      simp [hbase] at hnone
    · rename_i selectedBase hselected
      have heq := Option.some.inj (hselected.symm.trans hbase)
      subst selectedBase
      rfl

def Row.rawCell? {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (column : Nat) : Option UInt64 := do
  let cell ← selectedCell? kind column
  if resolved.slotData.metadata.isPacked then
    if cell.bitOffset + cell.width ≤ (profile kind).packedBits then
      packedRaw? (resolved.params mode) view.base cell
    else none
  else RawSource.traceWord? (resolved.params mode) (view.base + column)

def Row.cell? {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (column : Nat) : Option FGL :=
  (view.rawCell? column).map RawSource.NativeTraceWords.unpackedField

/-- A checked finite row owns each addressed native word inside the original
store prefix; the possibly larger shared suffix is neither copied nor cropped. -/
theorem Row.word_bound {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (word : Nat)
    (hword : word < nativeStride kind resolved.slotData.metadata.isPacked) :
    view.base + word < (resolved.params mode).trace.size := by
  have hbase := view.selected
  unfold rowBase? at hbase
  cases hs : resolved.setup? with
  | none => simp [hs] at hbase
  | some setup =>
    cases hc : setup.mapSectionsN["cm1"]? with
    | none => simp [hs, hc] at hbase
    | some cm1 =>
      simp only [hs] at hbase
      dsimp only [Bind.bind, Option.bind] at hbase
      simp only [hc] at hbase
      split at hbase
      · rename_i hprofile
        rcases hprofile with ⟨_, _, _, _, _, _, hrow, _, hstride, _, hcoverage⟩
        have heq : index * resolved.slotData.metadata.nColsTrace = view.base := by
          simpa using hbase
        have hnext : index + 1 ≤ setup.rowCount := by omega
        have hprefix := Nat.mul_le_mul_right resolved.slotData.metadata.nColsTrace hnext
        rw [Nat.add_mul, Nat.one_mul] at hprefix
        rw [← heq]
        rw [← hstride] at hword
        omega
      · simp at hbase

theorem Row.cell_eq_global {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (column : Nat) :
    view.cell? column = ZiskFv.AirsClean.NativeTraceCells.cell? kind resolved mode index column := by
  cases h : selectedCell? kind column <;>
    simp [Row.cell?, ZiskFv.AirsClean.NativeTraceCells.cell?, Row.rawCell?,
      ZiskFv.AirsClean.NativeTraceCells.rawCell?, h, view.selected]

theorem contained_raw_equation (params : RawSource.Params FGL) (base : Nat) (cell : Cell)
    (hwidth : 0 < cell.width ∧ cell.width ≤ 64)
    (hfit : cell.bitOffset % 64 + cell.width ≤ 64) :
    packedRaw? params base cell =
      (RawSource.traceWord? params (base + cell.bitOffset / 64)).map
        (fun word => (word >>> UInt64.ofNat (cell.bitOffset % 64)) &&& mask cell.width) := by
  cases hr : RawSource.traceWord? params (base + cell.bitOffset / 64) <;>
    simp [packedRaw?, hwidth, hfit, hr]

theorem split_raw_equation (params : RawSource.Params FGL) (base : Nat) (cell : Cell)
    (hwidth : 0 < cell.width ∧ cell.width ≤ 64)
    (hsplit : ¬cell.bitOffset % 64 + cell.width ≤ 64) :
    packedRaw? params base cell = (do
      let lowWord ← RawSource.traceWord? params (base + cell.bitOffset / 64)
      let highWord ← RawSource.traceWord? params (base + cell.bitOffset / 64 + 1)
      let lowBits := 64 - cell.bitOffset % 64
      return ((highWord &&& mask (cell.width - lowBits)) <<< UInt64.ofNat lowBits) |||
        ((lowWord >>> UInt64.ofNat (cell.bitOffset % 64)) &&& mask lowBits)) := by
  simp [packedRaw?, hwidth, hsplit]

/-- Source scalar getter dispatch (`word_start = word_end`) and the runtime
array getter condition agree on these supported finite-width source cells. -/
theorem scalar_contained_iff (offset width : Nat) (hwidth : 0 < width) :
    offset / 64 = (offset + width - 1) / 64 ↔ offset % 64 + width ≤ 64 := by
  omega

/-- A supported crossing cell occupies exactly the NEXT word. This derives
the array getter's `word+1` from the scalar source's explicit `word_end`. -/
theorem scalar_split_next (offset width : Nat) (hwidth : 0 < width ∧ width ≤ 64)
    (hcross : ¬offset % 64 + width ≤ 64) :
    (offset + width - 1) / 64 = offset / 64 + 1 := by
  omega

theorem split_shift_bounds (offset width : Nat) (hwidth : 0 < width ∧ width ≤ 64)
    (hcross : ¬offset % 64 + width ≤ 64) :
    0 < 64 - offset % 64 ∧ 64 - offset % 64 < 64 ∧
    0 < width - (64 - offset % 64) ∧ width - (64 - offset % 64) < 64 := by
  omega

/-- Only the fixed finite source row (at most39 cells) is allocated. No native
physical-domain vector or intermediate index list is constructed. -/
private def gather? {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) : (count : Nat) → Option (Vector FGL count)
  | 0 => some #v[]
  | count + 1 => do
    let previous ← gather? view count
    let value ← view.cell? count
    return previous.push value

private theorem gather_coordinates {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (count : Nat) (values : Vector FGL count)
    (h : gather? view count = some values) (column : Fin count) :
    view.cell? column.val = some values[column.val] := by
  induction count with
  | zero => exact Fin.elim0 column
  | succ count ih =>
    simp only [gather?] at h
    cases hp : gather? view count with
    | none => simp [hp] at h
    | some previous =>
      cases hv : view.cell? count with
      | none => simp [hp, hv] at h
      | some value =>
        have heq : previous.push value = values := by simpa [hp, hv] using h
        subst values
        by_cases hlt : column.val < count
        · simpa only [Vector.getElem_push_lt hlt] using
            ih previous hp ⟨column.val, hlt⟩
        · have heq : column.val = count := by omega
          simpa only [heq, Vector.getElem_push_eq] using hv

def Row.values? {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) : Option (Vector FGL (profile kind).unpackedWords) :=
  gather? view (profile kind).unpackedWords

theorem Row.values_coordinates {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (values : Vector FGL (profile kind).unpackedWords)
    (h : view.values? = some values) (column : Fin (profile kind).unpackedWords) :
    ZiskFv.AirsClean.NativeTraceCells.cell? kind resolved mode index column.val = some values[column.val] := by
  rw [← view.cell_eq_global]
  exact gather_coordinates view _ values h column

theorem actual_finite_row_bound (kind : Kind) : (profile kind).unpackedWords ≤ 39 := by
  cases kind <;> decide +kernel


theorem actual_cell_bounds (kind : Kind) :
    (profile kind).cells.all (fun cell =>
      decide (0 < cell.width ∧ cell.width ≤ 64 ∧
        cell.bitOffset + cell.width ≤ (profile kind).packedBits)) = true := by
  cases kind <;> decide +kernel


/-- Each actual source ordinal has a finite-width accessor wholly inside its
native row, including the SECOND word of every supported crossing cell. -/
theorem actual_indexed_accessors (kind : Kind) :
    ∀ column : Fin (profile kind).unpackedWords,
      (selectedCell? kind column.val).map (fun cell => decide (
        0 < cell.width ∧ cell.width ≤ 64 ∧
        cell.bitOffset + cell.width ≤ (profile kind).packedBits ∧
        cell.bitOffset / 64 < (profile kind).packedWords ∧
        (¬cell.bitOffset % 64 + cell.width ≤ 64 →
          cell.bitOffset / 64 + 1 < (profile kind).packedWords))) = some true := by
  cases kind <;> decide +kernel

theorem Row.raw_defined {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (column : Fin (profile kind).unpackedWords) :
    ∃ word, view.rawCell? column.val = some word := by
  have hcell := actual_indexed_accessors kind column
  cases hc : selectedCell? kind column.val with
  | none => simp [hc] at hcell
  | some cell =>
    have hs := of_decide_eq_true (Option.some.inj (by simpa [hc] using hcell))
    rcases hs with ⟨hpositive, hwidth, hend, hword, hnext⟩
    cases hp : resolved.slotData.metadata.isPacked with
    | false =>
      have hb := view.word_bound column.val (by simpa [nativeStride, hp] using column.isLt)
      refine ⟨(resolved.params mode).trace[view.base + column.val]'hb, ?_⟩
      simp [Row.rawCell?, hc, hp, RawSource.traceWord?, hb]
    | true =>
      have hb := view.word_bound (cell.bitOffset / 64)
        (by simpa [nativeStride, hp] using hword)
      have hr : RawSource.traceWord? (resolved.params mode) (view.base + cell.bitOffset / 64) =
          some ((resolved.params mode).trace[view.base + cell.bitOffset / 64]'hb) := by
        simp [RawSource.traceWord?, hb]
      by_cases hfit : cell.bitOffset % 64 + cell.width ≤ 64
      · simp [Row.rawCell?, hc, hp, hend, packedRaw?, hpositive, hwidth, hfit, hr]
      · have hhigh := view.word_bound (cell.bitOffset / 64 + 1)
          (by simpa [nativeStride, hp] using hnext.resolve_left hfit)
        have hh : RawSource.traceWord? (resolved.params mode) (view.base + cell.bitOffset / 64 + 1) =
            some ((resolved.params mode).trace[view.base + cell.bitOffset / 64 + 1]'(by omega)) := by
          simp [RawSource.traceWord?, show view.base + cell.bitOffset / 64 + 1 <
            (resolved.params mode).trace.size by omega]
        simp [Row.rawCell?, hc, hp, hend, packedRaw?, hpositive, hwidth, hfit, hr, hh]

theorem Row.cell_defined {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (column : Fin (profile kind).unpackedWords) :
    ∃ value, view.cell? column.val = some value := by
  obtain ⟨word, hw⟩ := view.raw_defined column
  exact ⟨RawSource.NativeTraceWords.unpackedField word, by simp [Row.cell?, hw]⟩

private theorem gather_defined {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) (count : Nat)
    (hcount : count ≤ (profile kind).unpackedWords) :
    ∃ values, gather? view count = some values := by
  induction count with
  | zero => exact ⟨#v[], rfl⟩
  | succ count ih =>
    obtain ⟨previous, hp⟩ := ih (by omega)
    obtain ⟨value, hv⟩ := view.cell_defined ⟨count, by omega⟩
    exact ⟨previous.push value, by simp [gather?, hp, hv]⟩

/-- A successfully checked finite-row constructor really decodes EVERY source
cell; coordinate correspondence is not vacuous through an always-None reader. -/
theorem Row.values_defined {source : SourceObject FGL} {kind : Kind}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : Row kind resolved mode index) : ∃ values, view.values? = some values :=
  gather_defined view _ (Nat.le_refl _)

end ZiskFv.AirsClean.NativeTraceCells
