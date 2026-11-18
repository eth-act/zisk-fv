import ZiskFv.AirsClean.GsumBoundary.Model
import ZiskFv.AirsClean.Mem.GeneratedTransition

/-! Source-kind boundary for live Mem c33.

`std_sum.pil:696` reads the AIR-GROUP result, not Mem's AIR segment id.
The maintained equation below fixes the selector, both subtraction signs and
all six direct terms independently of the generated link. Coordinate-wise
correspondence is only an equation theorem: it does not supply a native source
object, prove the equation holds, or derive numeric logUp from Clean balance.
The native consumer must obtain every coordinate from the same source occurrence.
-/
namespace ZiskFv.AirsClean.Mem.SourceFinalizer

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.GsumBoundary (Source)

/-- Actual source shape, deliberately independent of `link_Mem_33`. -/
def expectedConstraint : Expr :=
  .mul (.fixed 1 1)
    (.sub (.sub (.airGroupValue 0) (.witness 2 0 0))
      (.add (.add (.add (.add (.add (.airValue 15) (.airValue 16))
        (.airValue 17)) (.airValue 18)) (.airValue 19)) (.airValue 20)))

theorem compiled_constraint_eq_expected :
    constraint_Mem_33 = expectedConstraint := rfl

theorem compiled_finalizer_cells :
    link_Mem_33.selector = .fixed 1 1 ∧
    link_Mem_33.groupValue = .airGroupValue 0 ∧
    link_Mem_33.gsum = .witness 2 0 0 ∧
    link_Mem_33.directTerms =
      [.airValue 15, .airValue 16, .airValue 17, .airValue 18, .airValue 19, .airValue 20] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Rank zero is the source scalar rank, not its native extension-word width. -/
theorem distinct_source_kinds :
    SourceSchema.air_Mem.symbols.filter (fun symbol => symbol.kind == .airGroupValue) =
      [⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩] ∧
    SourceSchema.air_Mem.symbols.filter
        (fun symbol => symbol.kind == .airValue && symbol.index == 0) =
      [⟨some 0, some 14, "Mem.segment_id", .airValue, some 1, 0, 0, []⟩] :=
  ⟨rfl, rfl⟩

/-- A source-coordinate equation, not a source-object constructor or validator. -/
theorem coordinate_equation_iff {F : Type} [Field F] (source : Source F) :
    source.Holds constraint_Mem_33 ↔
      source.fixed 1 1 *
        (source.airGroupValue 0 - source.witness 2 0 0 -
          (((((source.airValue 15 + source.airValue 16) + source.airValue 17) +
            source.airValue 18) + source.airValue 19) + source.airValue 20)) = 0 := by
  change some (source.fixed 1 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 -
      (((((source.airValue 15 + source.airValue 16) + source.airValue 17) +
        source.airValue 18) + source.airValue 19) + source.airValue 20))) = some 0 ↔ _
  simp only [Option.some.injEq]

/-- Each of the three source extension coordinates has the independently fixed
c33 equation. This is not a field structure on a coordinate product. -/
theorem three_coordinate_equations_iff {F : Type} [Field F]
    (source : Fin 3 → Source F) :
    (∀ coordinate, (source coordinate).Holds constraint_Mem_33) ↔
      ∀ coordinate, (source coordinate).fixed 1 1 *
        ((source coordinate).airGroupValue 0 - (source coordinate).witness 2 0 0 -
          ((((((source coordinate).airValue 15 + (source coordinate).airValue 16) +
            (source coordinate).airValue 17) + (source coordinate).airValue 18) +
            (source coordinate).airValue 19) + (source coordinate).airValue 20)) = 0 := by
  exact forall_congr' fun coordinate => coordinate_equation_iff (source coordinate)

/-- The linear extension fragment used by c33. Every cell read is partial.
Only a fixed base-field selector may multiply an extension expression;
unsupported nonlinear products, scalar leaves and unknown literals fail closed.
No field structure or coordinate-wise multiplication of extensions is assumed. -/
def evalLinearCoordinate? {F : Type} [Field F] (source : Source (Option F)) :
    Expr → Option F
  | .constant "0" => some 0
  | .witness stage column offset => source.witness stage column offset
  | .airValue index => source.airValue index
  | .airGroupValue index => source.airGroupValue index
  | .add left right => do
      return (← evalLinearCoordinate? source left) + (← evalLinearCoordinate? source right)
  | .sub left right => do
      return (← evalLinearCoordinate? source left) - (← evalLinearCoordinate? source right)
  | .neg value => return -(← evalLinearCoordinate? source value)
  | .mul (.fixed column offset) value => do
      return (← source.fixed column offset) * (← evalLinearCoordinate? source value)
  | .mul value (.fixed column offset) => do
      return (← evalLinearCoordinate? source value) * (← source.fixed column offset)
  | _ => none

/-- Normal generated c33 is interpreted without a missing-cell zero fallback.
The explicit expected order, selector, group kind and signs do not come from
the generated finalizer's term roster. -/
theorem partial_coordinate_equation {F : Type} [Field F]
    (source : Source (Option F)) :
    evalLinearCoordinate? source constraint_Mem_33 = (do
      let selector ← source.fixed 1 1
      let contribution ← source.airGroupValue 0
      let running ← source.witness 2 0 0
      let direct0 ← source.airValue 15
      let direct1 ← source.airValue 16
      let direct2 ← source.airValue 17
      let direct3 ← source.airValue 18
      let direct4 ← source.airValue 19
      let direct5 ← source.airValue 20
      return selector * (contribution - running -
        (((((direct0 + direct1) + direct2) + direct3) + direct4) + direct5))) := by
  simp [evalLinearCoordinate?, constraint_Mem_33, Option.bind_assoc]

theorem linear_coordinate_rejects_nonlinear {F : Type} [Field F]
    (source : Source (Option F)) :
    evalLinearCoordinate? source (.mul (.airGroupValue 0) (.witness 2 0 0)) = none ∧
    evalLinearCoordinate? source (.opaque "unsupported" "payload") = none ∧
    evalLinearCoordinate? source (.constant "unparsed") = none :=
  ⟨rfl, rfl, rfl⟩

/-- A lossless encoding of three arbitrary Goldilocks words into the existing
single Goldilocks field is impossible; no cardinality restriction is assumed. -/
theorem no_injective_three_words_to_scalar :
    ¬ ∃ encode : (Fin 3 → FGL) → FGL, Function.Injective encode := by
  rintro ⟨encode, injective⟩
  have card_le := Fintype.card_le_of_injective encode injective
  simp only [Fintype.card_fun, Fintype.card_fin] at card_le
  norm_num at card_le

/-- The existing fixed schema rotates over its physical domain, not the
materialized prefix length. A strict prefix never enables the finalizer. -/
theorem legacy_selector_zero_on_strict_prefix
    (length row : Nat) (within : row < length) (short : length < memFixedCapacity) :
    memFixedColumns.fixedAt 1 (row + 1) = 0 := by
  change (if (row + 1) % 4194304 = 0 then (1 : FGL) else 0) = 0
  have bound : row + 1 < 4194304 := by
    change length < 4194304 at short
    omega
  rw [Nat.mod_eq_of_lt bound]
  simp

/-- The physical last row does enable the source's next-row L1 selector.
This does not assert that an arbitrary accepted Mem table has this row. -/
theorem legacy_selector_at_physical_last :
    memFixedColumns.fixedAt 1 memFixedCapacity = 1 := rfl

end ZiskFv.AirsClean.Mem.SourceFinalizer
