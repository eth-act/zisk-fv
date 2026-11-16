import ZiskFv.AirsClean.ByteMemoryCompiledPadding
import ZiskFv.AirsClean.MemAlignWriteByte.RawByteSource
import ZiskFv.AirsClean.MemAlignWriteByte.SourceLiterals
import ZiskFv.AirsClean.NativeValuesLayout

/-!
Exact source-to-compiled ties for MemAlignByte13/14 and MemAlignReadByte7/8.
The existing RawByteSource fail-closed decoder supplies the actual hints and
Params; no independent tuple roster or scalar is accepted. WriteOnly remains
in the complete source decoder and is not removed from any global balance.
Source-image/Accepted/once-world and provider composition remain separate.
-/
namespace ZiskFv.AirsClean.ByteMemoryPadding

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawByteSource
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

def readCapable : ByteAir → Bool
  | .readWrite | .readOnly => true
  | .writeOnly => false

/-- Exact four actual constraint-to-hint links, not invented adjacent tuples. -/
theorem source_links :
    link_MemAlignByte_13.hints = [hint_MemAlignByte_13_0] ∧
    link_MemAlignByte_14.hints = [hint_MemAlignByte_14_0] ∧
    link_MemAlignReadByte_7.hints = [hint_MemAlignReadByte_7_0] ∧
    link_MemAlignReadByte_8.hints = [hint_MemAlignReadByte_8_0] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Direction, bus, selector and every slot are pinned independently of the
compiled model operations. Native extension word width is not inferred here. -/
theorem source_tuple_metadata :
    (hint_MemAlignByte_13_0.piop, hint_MemAlignByte_13_0.proves,
      hint_MemAlignByte_13_0.busId, hint_MemAlignByte_13_0.multiplicity,
      hint_MemAlignByte_13_0.slots.map (·.value)) =
      ("Direct", true, Expr.constant "10", Expr.add (.airValue 0) (.constant "0"),
       [Expr.constant "1", .constant "0", .constant "0", .constant "8", .constant "0", .constant "0"]) ∧
    (hint_MemAlignByte_14_0.piop, hint_MemAlignByte_14_0.proves,
      hint_MemAlignByte_14_0.busId, hint_MemAlignByte_14_0.multiplicity,
      hint_MemAlignByte_14_0.slots.map (·.value)) =
      ("Direct", false, Expr.constant "10", Expr.add (.airValue 0) (.constant "0"),
       [Expr.constant "1", .constant "0", .constant "0", .constant "1", .constant "0", .constant "0"]) ∧
    (hint_MemAlignReadByte_7_0.piop, hint_MemAlignReadByte_7_0.proves,
      hint_MemAlignReadByte_7_0.busId, hint_MemAlignReadByte_7_0.multiplicity,
      hint_MemAlignReadByte_7_0.slots.map (·.value)) =
      ("Direct", true, Expr.constant "10", Expr.add (.airValue 0) (.constant "0"),
       [Expr.constant "1", .constant "0", .constant "0", .constant "8", .constant "0", .constant "0"]) ∧
    (hint_MemAlignReadByte_8_0.piop, hint_MemAlignReadByte_8_0.proves,
      hint_MemAlignReadByte_8_0.busId, hint_MemAlignReadByte_8_0.multiplicity,
      hint_MemAlignReadByte_8_0.slots.map (·.value)) =
      ("Direct", false, Expr.constant "10", Expr.add (.airValue 0) (.constant "0"),
       [Expr.constant "1", .constant "0", .constant "0", .constant "1", .constant "0", .constant "0"]) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The actual linked constraint lists are consumed by the decoder proof. -/
theorem actual_hint_lists :
    ByteAir.readWrite.hints = link_MemAlignByte_13.hints ++ link_MemAlignByte_14.hints ∧
    ByteAir.readOnly.hints = link_MemAlignReadByte_7.hints ++ link_MemAlignReadByte_8.hints := by
  rw [source_links.1, source_links.2.1, source_links.2.2.1, source_links.2.2.2]
  exact ⟨rfl, rfl⟩

private theorem read_capable_pair (air : ByteAir) (params : Params FGL)
    (hcap : readCapable air = true) :
    air.hints.mapM (RawByteSource.lowerDirect? air params) =
      params.airvalues[0]?.map (fun scalar =>
        [MemBusChannel.pushedIfValue scalar (ByteMemoryCompiledPadding.zeroLoadValue 8),
         MemBusChannel.pushedIfValue (-scalar) (ByteMemoryCompiledPadding.zeroLoadValue 1)]) := by
  cases air <;> simp only [readCapable, Bool.false_eq_true] at hcap
  all_goals
    simp only [actual_hint_lists.1, actual_hint_lists.2]
    cases hword : params.airvalues[0]? <;>
      simp [RawByteSource.lowerDirect?, link_MemAlignByte_13, link_MemAlignByte_14,
        link_MemAlignReadByte_7, link_MemAlignReadByte_8,
        hint_MemAlignByte_13_0, hint_MemAlignByte_14_0,
        hint_MemAlignReadByte_7_0, hint_MemAlignReadByte_8_0,
        ByteAir.schema, SourceSchema.air_MemAlignByte, SourceSchema.air_MemAlignReadByte,
        evalDirect?, stage1ScalarAt?, stage1Scalar, readWord?, buffer?,
        SourceLiterals.toNat_zero, SourceLiterals.toNat_one, SourceLiterals.toNat_eight,
        ByteMemoryCompiledPadding.zeroLoadValue, hword]

/-- Exact native wrapper for each source AIR, including the separately open
WriteOnly case; this mapping does not globally remove its interactions. -/
def nativePaddingAir : ByteAir → NativeValuesLayout.PaddingAir
  | .readWrite => .byte
  | .readOnly => .readByte
  | .writeOnly => .writeByte

/-- Actual source hint lowering equals actual compiled LOAD operations using
the independently derived native scalar address in the SAME Params buffer. -/
theorem source_hints_native_compiled (air : ByteAir) (params : Params FGL)
    (hcap : readCapable air = true) (env : Environment FGL) :
    air.hints.mapM (RawByteSource.lowerDirect? air params) =
      (NativeValuesLayout.paddingValue? (nativePaddingAir air) params).map
        (fun scalar => ByteMemoryCompiledPadding.byteValues scalar env) := by
  rw [NativeValuesLayout.padding_reads_actual_buffer]
  rw [read_capable_pair air params hcap]
  cases hword : params.airvalues[0]? <;>
    simp [hword, ByteMemoryCompiledPadding.byte_compiled]

end ZiskFv.AirsClean.ByteMemoryPadding
