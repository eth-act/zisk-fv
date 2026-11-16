import Clean.Air.FlatComponent
import ZiskFv.Channels.OperationBus
import ZiskFv.AirsClean.Mem.Stage2.Literals

/-!
Actual Binary c12 once-instance contribution, not an ordinary live row.
PIL b6327450 state-machines/binary/pil/binary.pil:158–159 calls
pil/operations.pil:160–167 with OP_ADD=10, eleven slots and negative raw
AIR0 multiplicity. The producer writes F::from_usize(num_rows-total_inputs)
(binary_basic.rs:898–924); this module does NOT identify arbitrary raw p with
that number. Zero and negative scalars remain present, with no range promise.

The source polynomial and the actual compiled interaction are compared in the
pinned cubic algebra, including all three coefficients. This is source fidelity,
not source authentication, equation satisfaction, gsum or operation-bus balance.
-/
namespace ZiskFv.AirsClean.BinaryPaddingOperations

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel OpBusMessage)
open Extraction.LookupWiring
open ZiskFv.AirsClean.Mem.Stage2 (Ext3 literal?)

def zeroADD : OpBusMessage FGL := ⟨10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def zeroADDExpr : OpBusMessage (Expression FGL) := ⟨10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[circuit_norm]
def circuit (padding : Expression FGL) : Circuit FGL Unit := do
  OpBusChannel.emit (-padding) zeroADDExpr

def values (padding : FGL) (env : Environment FGL) : List (Interaction FGL) :=
  ((circuit (.const padding)).operations 0).interactionValues env

theorem compiled_values (padding : FGL) (env : Environment FGL) :
    values padding env = [OpBusChannel.pushedIfValue (-padding) zeroADD] := by
  simp only [values, circuit, circuit_norm, ChannelInteraction.toRaw, AbstractInteraction.eval]
  simp only [← Vector.toArray_map, ← ProvableType.toElements_eval]
  simp [zeroADDExpr, zeroADD, circuit_norm]

theorem compiled_length (padding : FGL) (env : Environment FGL) :
    (values padding env).length = 1 := by rw [compiled_values]; rfl

/-- Actual source link, Direct direction, raw selector and ALL eleven source
slots accompany the actual compiled tuple. The native instance consumes this
joint theorem, rather than importing unused source aliases for ledger credit. -/
theorem source_tuple_and_compiled (padding : FGL) (env : Environment FGL) :
    link_Binary_12.hints = [hint_Binary_12_0] ∧
    hint_Binary_12_0.piop = "Direct" ∧
    hint_Binary_12_0.busId = .constant "5000" ∧
    hint_Binary_12_0.proves = false ∧
    hint_Binary_12_0.multiplicity = .add (.airValue 0) (.constant "0") ∧
    hint_Binary_12_0.slots.map (·.value) =
      [.constant "10", .constant "0", .constant "0", .constant "0",
       .constant "0", .constant "0", .constant "0", .constant "0",
       .constant "0", .constant "0", .constant "0"] ∧
    values padding env = [OpBusChannel.pushedIfValue (-padding) zeroADD] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, compiled_values padding env⟩

/-- Algebraic variables only: the native instance computes them from one
resolved source occurrence; this is not an additional native caller packet. -/
structure Operands where
  padding : FGL
  inverse : Ext3 FGL
  alpha : Ext3 FGL
  gamma : Ext3 FGL

private def b (value : FGL) : Ext3 FGL := Ext3.ofBase value

/-- Only the actual four source leaves are supported. No unknown leaf becomes
zero, and AIR/GROUP/aux kinds are not conflated. -/
def evaluate? (view : Operands) : Expr → Option (Ext3 FGL)
  | .constant text => literal? text
  | .airValue 0 => some (b view.padding)
  | .airValue 1 => some view.inverse
  | .challenge 2 0 => some view.alpha
  | .challenge 2 1 => some view.gamma
  | .add left right => return (← evaluate? view left) + (← evaluate? view right)
  | .sub left right => return (← evaluate? view left) - (← evaluate? view right)
  | .mul left right => return (← evaluate? view left) * (← evaluate? view right)
  | .neg value => return -(← evaluate? view value)
  | _ => none

def actualResidual? (view : Operands) : Option (Ext3 FGL) :=
  evaluate? view constraint_Binary_12

/-- Independent source opcode10, bus5000, negative raw p. -/
def expectedResidual (view : Operands) : Ext3 FGL :=
  view.inverse * ((b 10 * view.alpha + b 5000) + view.gamma) - (b 0 - b view.padding)

/-- Kernel normalization of the source bus literal through the SAME decimal
decoder; no literal whitelist, second interpreter or native_decide. -/
private theorem nat_5000 : "5000".toNat? = some 5000 := by
  change (String.ofList ['5', '0', '0', '0']).toNat? = some 5000
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    MemAlignWriteByte.SourceLiterals.foldl_ofList]
  simp [String.Slice.isEmpty]

@[simp] private theorem literal_5000 : literal? "5000" = some (b 5000) := by
  simp [literal?, nat_5000, b]

theorem actual_residual_eq_expected (view : Operands) :
    actualResidual? view = some (expectedResidual view) := by
  simp [actualResidual?, evaluate?, constraint_Binary_12, expectedResidual, b]

/-- Read ALL eleven actual evaluated message cells in source Horner order.
Channel, arity and length are checked; no parallel tuple is silently substituted. -/
def interactionResidual? (view : Operands) (interaction : Interaction FGL) :
    Option (Ext3 FGL) := do
  if interaction.channel.name = "OperationBus" ∧ interaction.channel.arity = 11 ∧
      interaction.msg.size = 11 then
    let op ← interaction.msg[0]?
    let a0 ← interaction.msg[1]?
    let a1 ← interaction.msg[2]?
    let b0 ← interaction.msg[3]?
    let b1 ← interaction.msg[4]?
    let c0 ← interaction.msg[5]?
    let c1 ← interaction.msg[6]?
    let flag ← interaction.msg[7]?
    let step ← interaction.msg[8]?
    let extended ← interaction.msg[9]?
    let extra ← interaction.msg[10]?
    let h0 := b extra * view.alpha + b extended
    let h1 := h0 * view.alpha + b step
    let h2 := h1 * view.alpha + b flag
    let h3 := h2 * view.alpha + b c1
    let h4 := h3 * view.alpha + b c0
    let h5 := h4 * view.alpha + b b1
    let h6 := h5 * view.alpha + b b0
    let h7 := h6 * view.alpha + b a1
    let h8 := h7 * view.alpha + b a0
    let h9 := h8 * view.alpha + b op
    return view.inverse * ((h9 * view.alpha + b 5000) + view.gamma) - b interaction.mult
  else none

def batchResidual? (view : Operands) : List (Interaction FGL) → Option (Ext3 FGL)
  | [interaction] => interactionResidual? view interaction
  | _ => none

def compiledResidual? (view : Operands) (operations : Operations FGL)
    (env : Environment FGL) : Option (Ext3 FGL) :=
  batchResidual? view (operations.interactionValues env)

private theorem block_zero_mul (value : Ext3 FGL) : (0 : Ext3 FGL) * value = 0 := by
  rw [Ext3.mul_eq_convolutionMul]
  change Ext3.convolutionMul ⟨0, 0, 0⟩ value = ⟨0, 0, 0⟩
  apply Ext3.ext <;> simp [Ext3.convolutionMul]

private theorem block_zero_add (value : Ext3 FGL) : (0 : Ext3 FGL) + value = value := by
  change (⟨0 + value.c0, 0 + value.c1, 0 + value.c2⟩ : Ext3 FGL) = value
  apply Ext3.ext <;> simp

private theorem block_zero_sub (value : Ext3 FGL) : (0 : Ext3 FGL) - value = -value := by
  change (⟨0 - value.c0, 0 - value.c1, 0 - value.c2⟩ : Ext3 FGL) =
    ⟨-value.c0, -value.c1, -value.c2⟩
  apply Ext3.ext <;> simp

private theorem message_size : ProvableType.size OpBusMessage = 11 := rfl

private theorem message_elements {F : Type} (message : OpBusMessage F) :
    ProvableType.toElements (M := OpBusMessage) message =
      #v[message.op, message.a_lo, message.a_hi, message.b_lo, message.b_hi,
        message.c_lo, message.c_hi, message.flag, message.main_step,
        message.extended_arg, message.extra_args_0] := by
  apply Vector.ext
  intro index bound
  have hindex : index < 11 := by simpa only [message_size] using bound
  interval_cases index <;>
    simp [explicit_provable_type, ProvableStruct.componentsToElements,
      ProvableStruct.components, ProvableStruct.toComponents]

theorem compiled_residual_eq_expected (view : Operands) (env : Environment FGL) :
    compiledResidual? view ((circuit (.const view.padding)).operations 0) env =
      some (expectedResidual view) := by
  unfold compiledResidual?
  change batchResidual? view (values view.padding env) = _
  rw [compiled_values]
  simp [batchResidual?, interactionResidual?, zeroADD, Channel.pushedIfValue,
    Channel.toRaw, OpBusChannel, message_size, message_elements,
    expectedResidual, b, block_zero_mul, block_zero_add, block_zero_sub]

/-- The SAME actual source equation is tied to the SAME compiled instance
operation, for every raw p and observation environment. -/
theorem actual_residual_eq_compiled (view : Operands) (env : Environment FGL) :
    actualResidual? view =
      compiledResidual? view ((circuit (.const view.padding)).operations 0) env := by
  rw [actual_residual_eq_expected, compiled_residual_eq_expected]

theorem actual_compiled_all_coefficients (view : Operands) (env : Environment FGL)
    (coefficient : Fin 3) :
    (actualResidual? view).map (fun residual => Ext3.coeff residual coefficient) =
      (compiledResidual? view ((circuit (.const view.padding)).operations 0) env).map
        (fun residual => Ext3.coeff residual coefficient) := by
  rw [actual_residual_eq_compiled]

end ZiskFv.AirsClean.BinaryPaddingOperations
