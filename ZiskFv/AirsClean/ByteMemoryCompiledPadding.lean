import Clean.Air.FlatComponent
import ZiskFv.Channels.MemoryBus
import Init.Data.Vector.Lemmas
import ZiskFv.AirsClean.Mem.Stage2.Literals

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

/-!
The following polynomial boundary owns the actual generated four Direct ASTs
and residuals of the actual compiled operations above. Its operands are only
universally quantified algebraic variables: the native model constructs them
from its private same-source projection, not a caller packet or callback.
Keeping this invariant next to the compiled primitive permits genuine changed
source checks without borrowing stale hint-consumer CIs.
-/
namespace DirectEquations

open Goldilocks
open Extraction.LookupWiring
open Mem.Stage2 (Ext3 literal?)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

structure Operands where
  padding : FGL
  alignedInverse : Ext3 FGL
  byteInverse : Ext3 FGL
  alpha : Ext3 FGL
  gamma : Ext3 FGL

private def b (value : FGL) : Ext3 FGL := Ext3.ofBase value

/-- Five supported source leaves only. This is not the Mem row decoder and
never conflates AIR/GROUP/aux or interprets an unsupported leaf as zero. -/
def evaluate? (view : Operands) : Expr → Option (Ext3 FGL)
  | .constant text => literal? text
  | .airValue 0 => some (b view.padding)
  | .airValue 1 => some view.alignedInverse
  | .airValue 2 => some view.byteInverse
  | .challenge 2 0 => some view.alpha
  | .challenge 2 1 => some view.gamma
  | .add left right => return (← evaluate? view left) + (← evaluate? view right)
  | .sub left right => return (← evaluate? view left) - (← evaluate? view right)
  | .mul left right => return (← evaluate? view left) * (← evaluate? view right)
  | .neg value => return -(← evaluate? view value)
  | _ => none

/-- Actual generated expressions, not a re-packed Direct-template roster. -/
def actualExpressions (readOnly : Bool) : Vector Expr 2 :=
  if readOnly then #v[constraint_MemAlignReadByte_7, constraint_MemAlignReadByte_8]
  else #v[constraint_MemAlignByte_13, constraint_MemAlignByte_14]

def actualResiduals? (readOnly : Bool) (view : Operands) : Option (Vector (Ext3 FGL) 2) := do
  return #v[← evaluate? view (actualExpressions readOnly)[0],
    ← evaluate? view (actualExpressions readOnly)[1]]

/-- Independently fixed op=1, width=8, bus=10, positive raw p. -/
def alignedExpected (view : Operands) : Ext3 FGL :=
  view.alignedInverse *
      (((((b 8 * view.alpha) * view.alpha) * view.alpha + b 1) *
        view.alpha + b 10) + view.gamma) - b view.padding

/-- Independently fixed op=1, width=1, bus=10, negative raw p. -/
def byteExpected (view : Operands) : Ext3 FGL :=
  view.byteInverse *
      ((((view.alpha * view.alpha) * view.alpha + b 1) *
        view.alpha + b 10) + view.gamma) - (b 0 - b view.padding)

/-- Actual normal AST interpretation, including all three mixed-product
coefficients. No equation-satisfaction hypothesis or conclusion occurs here. -/
theorem actual_residuals_eq_expected (readOnly : Bool) (view : Operands) :
    actualResiduals? readOnly view = some #v[alignedExpected view, byteExpected view] := by
  cases readOnly <;>
    simp [actualResiduals?, actualExpressions, evaluate?,
      constraint_MemAlignByte_13, constraint_MemAlignByte_14,
      constraint_MemAlignReadByte_7, constraint_MemAlignReadByte_8,
      alignedExpected, byteExpected, b]

/-- Horner encoding of ALL six evaluated tuple cells, followed by source bus10.
Channel/arity/length are checked before interpreting the concrete interaction. -/
def interactionResidual? (inverse alpha gamma : Ext3 FGL)
    (interaction : Interaction FGL) : Option (Ext3 FGL) := do
  if interaction.channel.name = "MemoryBus" ∧ interaction.channel.arity = 6 ∧
      interaction.msg.size = 6 then
    let operation ← interaction.msg[0]?
    let pointer ← interaction.msg[1]?
    let timestamp ← interaction.msg[2]?
    let width ← interaction.msg[3]?
    let value0 ← interaction.msg[4]?
    let value1 ← interaction.msg[5]?
    let h0 := b value1 * alpha + b value0
    let h1 := h0 * alpha + b width
    let h2 := h1 * alpha + b timestamp
    let h3 := h2 * alpha + b pointer
    let h4 := h3 * alpha + b operation
    return inverse * ((h4 * alpha + b 10) + gamma) - b interaction.mult
  else none

def batchResiduals? (view : Operands) : List (Interaction FGL) → Option (Vector (Ext3 FGL) 2)
  | [aligned, byte] => do
    return #v[← interactionResidual? view.alignedInverse view.alpha view.gamma aligned,
      ← interactionResidual? view.byteInverse view.alpha view.gamma byte]
  | _ => none

/-- Operations are observed, not reconstructed from a caller tuple packet. -/
def compiledResiduals? (view : Operands) (operations : Operations FGL) (env : Environment FGL) :
    Option (Vector (Ext3 FGL) 2) :=
  batchResiduals? view (operations.interactionValues env)

private theorem block_zero_mul (value : Ext3 FGL) : (0 : Ext3 FGL) * value = 0 := by
  rw [Ext3.mul_eq_convolutionMul]
  apply Ext3.ext <;> simp [Ext3.convolutionMul]

private theorem block_zero_add (value : Ext3 FGL) : (0 : Ext3 FGL) + value = value := by
  cases value
  apply Ext3.ext <;> simp [HAdd.hAdd, Add.add]

private theorem block_add_zero (value : Ext3 FGL) : value + (0 : Ext3 FGL) = value := by
  cases value
  apply Ext3.ext <;> simp [HAdd.hAdd, Add.add]

private theorem block_one_mul (value : Ext3 FGL) : (1 : Ext3 FGL) * value = value := by
  change Ext3.ofBase (1 : FGL) * value = value
  rw [Ext3.ofBase_mul_block]
  cases value
  apply Ext3.ext <;> simp [HSMul.hSMul, SMul.smul]

private theorem block_zero_sub (value : Ext3 FGL) : (0 : Ext3 FGL) - value = -value := by
  cases value
  apply Ext3.ext <;> simp [Sub.sub, Neg.neg]

/-- The residual uses actual compiled message fields and actual signed
multiplicities, not only a parallel independent local tuple definition. -/
theorem compiled_residuals_eq_expected (view : Operands) (env : Environment FGL) :
    compiledResiduals? view
        ((ByteMemoryCompiledPadding.byteCircuit (.const view.padding)).operations 0) env =
      some #v[alignedExpected view, byteExpected view] := by
  unfold compiledResiduals?
  change batchResiduals? view (ByteMemoryCompiledPadding.byteValues view.padding env) = _
  rw [ByteMemoryCompiledPadding.byte_compiled]
  simp [batchResiduals?, interactionResidual?, ByteMemoryCompiledPadding.zeroLoadValue,
    Channel.pushedIfValue, Channel.toRaw, MemBusChannel,
    alignedExpected, byteExpected, b, Ext3.ofBase_zero,
    block_zero_mul, block_zero_add, block_add_zero, block_one_mul, block_zero_sub]

/-- Load-bearing actual-source/actual-compiled residual identity. Environments
are universally quantified observers; no caller environment equality is needed. -/
theorem actual_residuals_eq_compiled (readOnly : Bool) (view : Operands) (env : Environment FGL) :
    actualResiduals? readOnly view = compiledResiduals? view
      ((ByteMemoryCompiledPadding.byteCircuit (.const view.padding)).operations 0) env := by
  rw [actual_residuals_eq_expected, compiled_residuals_eq_expected]

/-- Every coefficient of each actual residual is retained by the linkage. -/
theorem actual_compiled_all_coefficients (readOnly : Bool) (view : Operands) (env : Environment FGL) (equation : Fin 2)
    (coefficient : Fin 3) :
    (actualResiduals? readOnly view).map (fun values => Ext3.coeff values[equation.val] coefficient) =
      (compiledResiduals? view
        ((ByteMemoryCompiledPadding.byteCircuit (.const view.padding)).operations 0) env).map
          (fun values => Ext3.coeff values[equation.val] coefficient) := by
  rw [actual_residuals_eq_compiled]

end DirectEquations

end ZiskFv.AirsClean.ByteMemoryCompiledPadding
