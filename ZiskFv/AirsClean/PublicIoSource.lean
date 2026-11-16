import ZiskFv.AirsClean.PublicIo
import Extraction.PublicIo

/-!
The two sides of this weld are independent: `PublicIo.messageExpr` is the
local Clean circuit; `Extraction.PublicIo` is generated from protobuf GLOBAL
expressions and actual public-symbol indices. No PIL source string or
`debugLine` is interpreted as an equation.

The generated `source_terms` and `source_term_N_factors` theorems check the
whole cleared GLOBAL sum. `publicEmissions_linked` identifies each public
message denominator and its positive unit omitted-denominator numerator.
This is source correspondence for emissions, not a proof of a cryptographic
PIOP's soundness or of execution of the runtime epilogue.
-/
namespace ZiskFv.AirsClean.PublicIo

open Goldilocks
open ZiskFv.Channels.OperationBus
open Extraction.PublicIo (Expr)

/-- Pins the actual whole verifier vector, not merely the `inputs` subvector. -/
theorem source_public_dimensions :
    Extraction.PublicIo.publicCellCount = 68 ∧
    Extraction.PublicIo.romRootBase = 0 ∧
    Extraction.PublicIo.romRootCellCount = 4 ∧
    Extraction.PublicIo.inputBase = 4 ∧
    Extraction.PublicIo.inputCellCount = 64 ∧
    Extraction.PublicIo.operationArity = 11 ∧
    Extraction.PublicIo.publicEmissions.length = 32 := by decide

def sourceEmission (i : WordIndex) : Extraction.PublicIo.Emission :=
  Extraction.PublicIo.publicEmissions[i.val]'(by change i.val < 32; exact i.isLt)

/-- Independent literal arithmetic pins every source tuple, not a self-equality
of a generated expected string. Changing the source loop bound, bus, opcode,
public-cell index, duplicate limb, or selector breaks this theorem or the
compiled GLOBAL denominator/numerator weld. -/
theorem source_emission_shape (i : WordIndex) :
    (sourceEmission i).bus = .constant 5000 ∧
    (sourceEmission i).slots =
      [.constant 48, .constant i.val, .constant 0,
        .publicValue (4 + 2 * i.val), .publicValue (4 + (2 * i.val + 1)),
        .publicValue (4 + 2 * i.val), .publicValue (4 + (2 * i.val + 1))] ∧
    (sourceEmission i).proves = 1 ∧
    (sourceEmission i).multiplicity = .constant 1 ∧
    (sourceEmission i).termIndex = 42 + i.val := by
  fin_cases i <;> decide

theorem source_emission_termIndex_injective :
    Function.Injective (fun i : WordIndex => (sourceEmission i).termIndex) := by
  intro i j h
  have hi := (source_emission_shape i).2.2.2.2
  have hj := (source_emission_shape j).2.2.2.2
  change (sourceEmission i).termIndex = (sourceEmission j).termIndex at h
  rw [hi, hj] at h
  exact Fin.ext (by omega)

/-- The sign is checked at the actual compiled global emission boundary:
coefficient +1 means the numerator is exactly the product omitting this
message's denominator. This is stronger than reading `type_piop = proves`. -/
theorem source_emission_global_link (i : WordIndex) :
    Extraction.PublicIo.normalize
        (Extraction.PublicIo.sourceDenominators[(sourceEmission i).termIndex]!) =
      .add (Extraction.PublicIo.mix (sourceEmission i).bus (.challenge 2 0)
        (sourceEmission i).slots) (.challenge 2 1) ∧
    Extraction.PublicIo.flattenMul
        (Extraction.PublicIo.sourceTerms[(sourceEmission i).termIndex]!) =
      Extraction.PublicIo.sourceDenominators.eraseIdx (sourceEmission i).termIndex := by
  exact Extraction.PublicIo.publicEmissions_linked
    ⟨i.val, by change i.val < 32; exact i.isLt⟩

theorem inputCell_source_projection {F : Type} (publicIO : PublicIO F)
    (i : CellIndex) :
    inputCell publicIO i = publicIO[Extraction.PublicIo.inputBase + i.val]'(by
      change 4 + i.val < 68; omega) := by rfl

theorem romRootCell_source_projection {F : Type} (publicIO : PublicIO F)
    (i : Fin 4) :
    romRootCell publicIO i = publicIO[Extraction.PublicIo.romRootBase + i.val]'(by
      change 0 + i.val < 68; omega) := by
  simp [romRootCell, Extraction.PublicIo.romRootBase]

/-- Reject every non-public operand instead of inventing an interpretation
for a challenge, proof value, or AIR value. The public tuple itself contains
only constants and actual public cells. -/
def sourceToClean (publicIO : Var PublicIO FGL) : Expr → Option (Expression FGL)
  | .constant n => some (Expression.const (n : FGL))
  | .publicValue n => if h : n < 68 then some publicIO[n] else none
  | _ => none

def opBusSlots {F : Type} (m : OpBusMessage F) : List F :=
  [m.op, m.a_lo, m.a_hi, m.b_lo, m.b_hi, m.c_lo, m.c_hi,
    m.flag, m.main_step, m.extended_arg, m.extra_args_0]

/-- Reify all eleven actual Clean slots from the compiled seven-slot global
emission. The source Main schema fixes arity 11; the unused tail is zero, not
new public data, an unspecified flag, or an unconstrained witness row. -/
theorem source_slot_interpretation (publicIO : Var PublicIO FGL) (i : WordIndex) :
    ((sourceEmission i).slots ++
      List.replicate (Extraction.PublicIo.operationArity - 7) (Expr.constant 0)).mapM
        (sourceToClean publicIO) = some (opBusSlots (messageExpr publicIO i)) := by
  fin_cases i <;> rfl

/-- The source-defined number of unit emissions is the local circuit's exact
finite multiplicity, including when all public words happen to coincide. -/
theorem source_emission_count (publicIO : PublicIO FGL) :
    (interactions publicIO).length = Extraction.PublicIo.publicEmissions.length ∧
    (interactions publicIO).Nodup := by
  constructor
  · rw [interactions_length]
    rfl
  · exact interactions_nodup publicIO


/-- All actual compiled GLOBAL operation-bus terms are covered, not merely
the 32 hints that happened to be selected. An unhinted extra emission cannot
silently evade the local multiplicity model. -/
theorem source_operation_emissions_exact :
    Extraction.PublicIo.sourceOperationTermIndices =
      (List.finRange 32).map (fun i => 42 + i.val) := by
  rw [Extraction.PublicIo.source_operation_emissions_complete]
  rfl

theorem source_operation_emission_count :
    Extraction.PublicIo.sourceOperationTermIndices.length = 32 := by
  rw [source_operation_emissions_exact]
  simp

end ZiskFv.AirsClean.PublicIo
