import ZiskFv.AirsClean.Mem.Stage2.Native
import ZiskFv.AirsClean.MemAlignWriteByte.SourceLiterals

/-! Kernel normalization of the actual Mem source literals through the shared
String.toNat? implementation. These lemmas do not change the generic decoder or
add a literal whitelist, native_decide, an opaque alias or a default value. -/
namespace ZiskFv.AirsClean.Mem.Stage2
open Goldilocks
namespace LiteralProof
open ZiskFv.AirsClean.MemAlignWriteByte.SourceLiterals

theorem nat_11 : "11".toNat? = some 11 := by
  change (String.ofList ['1', '1']).toNat? = some 11
  simp [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList, String.Slice.isEmpty]
theorem nat_102 : "102".toNat? = some 102 := by
  change (String.ofList ['1', '0', '2']).toNat? = some 102
  simp [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList, String.Slice.isEmpty]
theorem nat_103 : "103".toNat? = some 103 := by
  change (String.ofList ['1', '0', '3']).toNat? = some 103
  simp [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList, String.Slice.isEmpty]
theorem nat_104 : "104".toNat? = some 104 := by
  change (String.ofList ['1', '0', '4']).toNat? = some 104
  simp [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList, String.Slice.isEmpty]
theorem nat_continuation : "2684354560".toNat? = some 2684354560 := by
  change (String.ofList ['2', '6', '8', '4', '3', '5', '4', '5', '6', '0']).toNat? = some 2684354560
  simp [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList, String.Slice.isEmpty]
theorem nat_negative_one : "18446744069414584320".toNat? = some 18446744069414584320 := by
  change (String.ofList ['1', '8', '4', '4', '6', '7', '4', '4', '0', '6',
    '9', '4', '1', '4', '5', '8', '4', '3', '2', '0']).toNat? = some 18446744069414584320
  simp [String.toNat?, String.Slice.toNat?, String.Slice.isNat, foldl_ofList, String.Slice.isEmpty]
end LiteralProof

@[simp] theorem literal_zero : literal? "0" = some (Ext3.ofBase (0 : FGL)) := by
  simp [literal?, MemAlignWriteByte.SourceLiterals.toNat_zero]
@[simp] theorem literal_one : literal? "1" = some (Ext3.ofBase (1 : FGL)) := by
  simp [literal?, MemAlignWriteByte.SourceLiterals.toNat_one]
@[simp] theorem literal_eight : literal? "8" = some (Ext3.ofBase (8 : FGL)) := by
  simp [literal?, MemAlignWriteByte.SourceLiterals.toNat_eight]
@[simp] theorem literal_ten : literal? "10" = some (Ext3.ofBase (10 : FGL)) := by
  simp [literal?, MemAlignWriteByte.SourceLiterals.toNat_ten]
@[simp] theorem literal_eleven : literal? "11" = some (Ext3.ofBase (11 : FGL)) := by
  simp [literal?, LiteralProof.nat_11]
@[simp] theorem literal_range24 : literal? "102" = some (Ext3.ofBase (102 : FGL)) := by
  simp [literal?, LiteralProof.nat_102]
@[simp] theorem literal_range16 : literal? "103" = some (Ext3.ofBase (103 : FGL)) := by
  simp [literal?, LiteralProof.nat_103]
@[simp] theorem literal_range22 : literal? "104" = some (Ext3.ofBase (104 : FGL)) := by
  simp [literal?, LiteralProof.nat_104]
@[simp] theorem literal_continuation : literal? "2684354560" = some (Ext3.ofBase (2684354560 : FGL)) := by
  simp [literal?, LiteralProof.nat_continuation]
@[simp] theorem literal_negative_one : literal? "18446744069414584320" = some (Ext3.ofBase (-1 : FGL)) := by
  have hc : (18446744069414584320 : FGL) = -1 := by decide
  simp [literal?, LiteralProof.nat_negative_one, hc]

end ZiskFv.AirsClean.Mem.Stage2
