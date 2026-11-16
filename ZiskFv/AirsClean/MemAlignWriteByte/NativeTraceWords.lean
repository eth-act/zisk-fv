import ZiskFv.AirsClean.MemAlignWriteByte.RawSource
import ZiskFv.Field.Goldilocks

/-! One primary raw UInt64 trace store, with separate mathematical unpacked
field views. No decoded trace array or word-to-field callback is stored.

ff0e33a9 fields/src/goldilocks.rs19–23 defines Goldilocks(u64) and P;
246–255 as_canonical_u64 subtracts P ONCE iff raw >= P. For every UInt64,
2*P > 2^64 proves this is raw % P. This is an intentionally noninjective FIELD
projection, never a packed bit decoder. The raw accessor retains every bit.

common/src/trace.rs129–164 retains original buffer len/cap/element_size before
casting to R;175–194 get_buffer restores that ORIGINAL length, not N*logical
columns;235–274 forwards the same buffer and R::IS_PACKED. The image carrier
must be materialized from that actual same store/metadata. Rust/FFI ABI and
actual native-memory-to-image materialization remain UNPROVED: the declaration
Goldilocks(u64) itself has no repr(C)/transparent, and is not an ABI theorem.

Only requested finite words are field-projected. No 4m-row trace map/copy is
performed. Packed, GPU and machine-address decoding remain separate obligations;
None from a partial reader is not a Root scope exclusion. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.RawSource.NativeTraceWords

open Goldilocks

/-- Exact conditional in native PrimeField64::as_canonical_u64. -/
def canonicalNat (word : UInt64) : Nat :=
  if GL_prime ≤ word.toNat then word.toNat - GL_prime else word.toNat

/-- Native one-subtraction canonicalization is sufficient for ALL UInt64 words,
including noncanonical representatives; no raw<p input restriction is added. -/
theorem canonicalNat_mod (word : UInt64) :
    canonicalNat word = word.toNat % GL_prime := by
  have hword : word.toNat < 18446744073709551616 := word.toNat_lt_size
  by_cases h : GL_prime ≤ word.toNat
  · have hsmall : word.toNat - GL_prime < GL_prime := by omega
    have hsplit : word.toNat = (word.toNat - GL_prime) + GL_prime := by omega
    rw [canonicalNat, if_pos h]
    symm
    calc
      word.toNat % GL_prime = ((word.toNat - GL_prime) + GL_prime) % GL_prime :=
        congrArg (fun value : Nat => value % GL_prime) hsplit
      _ = word.toNat - GL_prime := by simp [Nat.add_mod, Nat.mod_eq_of_lt hsmall]
  · have hsmall : word.toNat < GL_prime := by omega
    simp [canonicalNat, h, Nat.mod_eq_of_lt hsmall]

theorem canonicalNat_lt (word : UInt64) : canonicalNat word < GL_prime := by
  rw [canonicalNat_mod]
  exact Nat.mod_lt _ (by decide)

/-- Concrete FGL quotient, derived from the source conditional, not a free
conversion oracle. This value is NOT a lossless representation of raw bits. -/
def unpackedField (word : UInt64) : FGL := ⟨canonicalNat word, canonicalNat_lt word⟩

theorem unpackedField_eq_natCast (word : UInt64) :
    unpackedField word = (word.toNat : FGL) := by
  apply Fin.ext
  change canonicalNat word = word.toNat % GL_prime
  exact canonicalNat_mod word

/-- Native raw word identity is retained through the SAME Params trace store. -/
theorem traceWord_original (params : Params F) (index : Nat) :
    traceWord? params index = params.trace[index]? := rfl

/-- A single unpacked field read, without materializing a decoded trace. -/
def unpackedWord? (params : Params FGL) (index : Nat) : Option FGL :=
  (traceWord? params index).map unpackedField

/-- Decode exactly width requested cells, not a whole-row/domain array map.
The dependent bound gives direct safe native-word reads without default values. -/
def unpackedBlock? (params : Params FGL) (offset width : Nat) : Option (Array FGL) :=
  if width = 0 then none
  else if hbound : offset + width ≤ params.trace.size then
    some (Array.ofFn fun index : Fin width =>
      unpackedField (params.trace[offset + index.val]'(by omega)))
  else none

theorem unpackedWord_source (params : Params FGL) (index : Nat) :
    unpackedWord? params index = (params.trace[index]?).map unpackedField := rfl

theorem unpackedBlock_constructible (params : Params FGL) (offset width : Nat)
    (hwidth : width ≠ 0) (hbound : offset + width ≤ params.trace.size) :
    unpackedBlock? params offset width = some (Array.ofFn fun index : Fin width =>
      unpackedField (params.trace[offset + index.val]'(by omega))) := by
  simp [unpackedBlock?, hwidth, hbound]

theorem unpackedBlock_size (params : Params FGL) (offset width : Nat)
    (words : Array FGL) (h : unpackedBlock? params offset width = some words) :
    words.size = width := by
  by_cases hz : width = 0
  · simp [unpackedBlock?, hz] at h
  · by_cases hb : offset + width ≤ params.trace.size
    · simp only [unpackedBlock?, hz, hb, ↓reduceIte, Option.some.injEq] at h
      subst words
      simp
    · simp [unpackedBlock?, hz, hb] at h

/-- The primary raw store distinguishes the two legitimate bit patterns. -/
theorem raw_zero_ne_prime : (0 : UInt64) ≠ UInt64.ofNat GL_prime := by decide

theorem unpacked_zero : unpackedField 0 = 0 := by
  rw [unpackedField_eq_natCast]
  norm_num

theorem unpacked_prime : unpackedField (UInt64.ofNat GL_prime) = 0 := by
  rw [unpackedField_eq_natCast]
  norm_num

/-- Field reduction must NEVER be used as lossless packed storage. -/
theorem unpackedField_not_injective : ¬ Function.Injective unpackedField := by
  intro hinjective
  apply raw_zero_ne_prime
  apply hinjective
  rw [unpacked_zero, unpacked_prime]

end ZiskFv.AirsClean.MemAlignWriteByte.RawSource.NativeTraceWords
