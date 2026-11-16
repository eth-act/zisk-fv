import ZiskFv.AirsClean.ByteMemoryPadding

/-!
The registry entry and native padding scalar of ONE resolved source occurrence
own the actual compiled read-capable Direct pair. The environment is only an
observer, never stored input. No independent Params, roster or success promise
is added; production/image/ABI and Accepted integration are not asserted.
-/
namespace ZiskFv.AirsClean.ByteMemorySourceOperations

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open ZiskFv.AirsClean.MemAlignWriteByte

variable {source : SourceObject FGL}

/-- Native source scalar used by the actual compiled read-capable LOAD pair. -/
def byteOperations? (resolved : ResolvedOccurrence source) (env : Environment FGL) :
    Option (List (Interaction FGL)) := do
  let air ← RawByteSource.airForEntry? resolved.registryEntry
  if ByteMemoryPadding.readCapable air then
    (NativeValuesLayout.paddingValue? (ByteMemoryPadding.nativePaddingAir air)
      (resolved.params false)).map (fun scalar => ByteMemoryCompiledPadding.byteValues scalar env)
  else none

/-- Actual RW13/14 or RO7/8 hints, not a caller-provided tuple list. -/
theorem byte_operations_eq_source (resolved : ResolvedOccurrence source)
    (env : Environment FGL) :
    byteOperations? resolved env = (do
      let air ← RawByteSource.airForEntry? resolved.registryEntry
      if ByteMemoryPadding.readCapable air then
        air.hints.mapM (RawByteSource.lowerDirect? air (resolved.params false))
      else none) := by
  unfold byteOperations?
  cases hair : RawByteSource.airForEntry? resolved.registryEntry with
  | none => rfl
  | some air =>
    change (if ByteMemoryPadding.readCapable air then
        (NativeValuesLayout.paddingValue? (ByteMemoryPadding.nativePaddingAir air)
          (resolved.params false)).map (fun scalar => ByteMemoryCompiledPadding.byteValues scalar env)
        else none) =
      if ByteMemoryPadding.readCapable air then
        air.hints.mapM (RawByteSource.lowerDirect? air (resolved.params false))
      else none
    split
    · rename_i hcap
      exact (ByteMemoryPadding.source_hints_native_compiled air (resolved.params false) hcap env).symm
    · rfl

end ZiskFv.AirsClean.ByteMemorySourceOperations
