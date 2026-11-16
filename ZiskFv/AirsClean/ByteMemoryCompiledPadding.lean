import Clean.Air.FlatComponent
import ZiskFv.Channels.MemoryBus
import Init.Data.Vector.Lemmas

/-!
Compiled instance operations for the two read-capable byte-memory AIRs.
PIL b6327450 mem/pil/mem_align_byte.pil:106–118 supplies positive LOAD8 and
negative LOAD1 with the same raw AIR-value padding scalar. No scalar/count,
sign or nonzero rule is introduced; zero messages retain their source order.
-/
namespace ZiskFv.AirsClean.ByteMemoryCompiledPadding

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- All6 memory slots, retaining the distinct source widths. -/
def zeroLoadValue (width : FGL) : MemBusMessage FGL := ⟨1, 0, 0, width, 0, 0⟩

def zeroLoadExpr (width : Expression FGL) : MemBusMessage (Expression FGL) :=
  ⟨1, 0, 0, width, 0, 0⟩

@[circuit_norm]
def byteCircuit (scalar : Expression FGL) : Circuit FGL Unit := do
  MemBusChannel.emit scalar (zeroLoadExpr 8)
  MemBusChannel.emit (-scalar) (zeroLoadExpr 1)

def byteValues (scalar : FGL) (env : Environment FGL) : List (Interaction FGL) :=
  ((byteCircuit (.const scalar)).operations 0).interactionValues env

theorem byte_compiled (scalar : FGL) (env : Environment FGL) :
    byteValues scalar env =
      [MemBusChannel.pushedIfValue scalar (zeroLoadValue 8),
       MemBusChannel.pushedIfValue (-scalar) (zeroLoadValue 1)] := by
  simp only [byteValues, byteCircuit, circuit_norm,
    ChannelInteraction.toRaw, AbstractInteraction.eval]
  simp only [← Vector.toArray_map, ← ProvableType.toElements_eval]
  simp [zeroLoadExpr, zeroLoadValue, circuit_norm]

theorem byte_compiled_length (scalar : FGL) (env : Environment FGL) :
    (byteValues scalar env).length = 2 := by
  rw [byte_compiled]
  rfl

end ZiskFv.AirsClean.ByteMemoryCompiledPadding
