import ZiskFv.AirsClean.Mem.Stage2.Cubic
import ZiskFv.Field.Goldilocks

/-! A local polynomial row, not a new public Valid_Mem or source certificate.
All stage2 values are three coefficients. Its native factory is separate and
must read the same source occurrence. The construction below establishes only
local algebraic non-vacuity; it is not a native execution/accepted-trace builder.
-/
namespace ZiskFv.AirsClean.Mem.Stage2
open Goldilocks

structure PolynomialRow where
  addr : FGL
  step : FGL
  sel : FGL
  stepDual : FGL
  selDual : FGL
  valueLo : FGL
  valueHi : FGL
  wr : FGL
  lowIncrement : FGL
  highIncrement : FGL
  segmentId : FGL
  isLastSegment : FGL
  previousValueLo : FGL
  previousValueHi : FGL
  previousStep : FGL
  previousAddr : FGL
  lastValueLo : FGL
  lastValueHi : FGL
  lastStep : FGL
  lastAddr : FGL
  distanceBaseLo : FGL
  distanceBaseHi : FGL
  distanceEndLo : FGL
  distanceEndHi : FGL
  alpha : Ext3 FGL
  gamma : Ext3 FGL
  running : Ext3 FGL
  previousRunning : Ext3 FGL
  cluster0 : Ext3 FGL
  cluster1 : Ext3 FGL
  direct0 : Ext3 FGL
  direct1 : Ext3 FGL
  direct2 : Ext3 FGL
  direct3 : Ext3 FGL
  direct4 : Ext3 FGL
  direct5 : Ext3 FGL
  l1 : FGL
  nextL1 : FGL
  groupResult : Ext3 FGL

namespace PolynomialRow
private abbrev b (value : FGL) : Ext3 FGL := Ext3.ofBase value

/-- Every coefficient, sign and Horner step is fixed by Mem c24–c32. -/
def highDen (r : PolynomialRow) := b r.highIncrement * r.alpha + b 103 + r.gamma
def dualStepDen (r : PolynomialRow) := b ((r.stepDual - r.step) - r.wr) * r.alpha + b 102 + r.gamma
def lowDen (r : PolynomialRow) := b r.lowIncrement * r.alpha + b 104 + r.gamma

def primaryDen (r : PolynomialRow) :=
  ((((((b r.valueHi * r.alpha + b r.valueLo) * r.alpha + b 8) * r.alpha + b r.step) *
    r.alpha + b (r.addr * 8)) * r.alpha + b (r.wr + 1)) * r.alpha + b 10) + r.gamma

def dualDen (r : PolynomialRow) :=
  ((((((b r.valueHi * r.alpha + b r.valueLo) * r.alpha + b 8) * r.alpha + b r.stepDual) *
    r.alpha + b (r.addr * 8)) * r.alpha + b 1) * r.alpha + b 10) + r.gamma

def previousDen (r : PolynomialRow) :=
  ((((((b r.previousValueHi * r.alpha + b r.previousValueLo) * r.alpha + b r.previousStep) *
    r.alpha + b r.previousAddr) * r.alpha + b r.segmentId) * r.alpha + b 2684354560) *
    r.alpha + b 11) + r.gamma

def nextDen (r : PolynomialRow) :=
  ((((((b r.lastValueHi * r.alpha + b r.lastValueLo) * r.alpha + b r.lastStep) *
    r.alpha + b r.lastAddr) * r.alpha + b (r.segmentId + 1)) * r.alpha + b 2684354560) *
    r.alpha + b 11) + r.gamma

def residual24 (r : PolynomialRow) : Ext3 FGL :=
  r.cluster0 * (r.highDen * r.dualStepDen) -
    (b (-1) * r.dualStepDen + b (0 - r.selDual) * r.highDen)
def residual25 (r : PolynomialRow) : Ext3 FGL :=
  r.cluster1 * (r.primaryDen * r.dualDen) -
    (b r.sel * r.dualDen + b r.selDual * r.primaryDen)
def residual26 (r : PolynomialRow) : Ext3 FGL :=
  ((r.running - r.previousRunning * b (1 - r.l1)) - (r.cluster0 + r.cluster1)) * r.lowDen + b 1
def residual27 (r : PolynomialRow) : Ext3 FGL := r.direct0 * r.previousDen + b 1
def residual28 (r : PolynomialRow) : Ext3 FGL := r.direct1 * r.nextDen - b (1 - r.isLastSegment)
def residual29 (r : PolynomialRow) : Ext3 FGL := r.direct2 * (b r.distanceBaseLo * r.alpha + b 103 + r.gamma) + b 1
def residual30 (r : PolynomialRow) : Ext3 FGL := r.direct3 * (b r.distanceBaseHi * r.alpha + b 103 + r.gamma) + b 1
def residual31 (r : PolynomialRow) : Ext3 FGL := r.direct4 * (b r.distanceEndLo * r.alpha + b 103 + r.gamma) + b 1
def residual32 (r : PolynomialRow) : Ext3 FGL := r.direct5 * (b r.distanceEndHi * r.alpha + b 103 + r.gamma) + b 1

def residual (r : PolynomialRow) (equation : Fin 9) : Ext3 FGL :=
  match equation.val with
  | 0 => r.residual24
  | 1 => r.residual25
  | 2 => r.residual26
  | 3 => r.residual27
  | 4 => r.residual28
  | 5 => r.residual29
  | 6 => r.residual30
  | 7 => r.residual31
  | _ => r.residual32

def directSum (r : PolynomialRow) : Ext3 FGL :=
  ((((r.direct0 + r.direct1) + r.direct2) + r.direct3) + r.direct4) + r.direct5

def residual33 (r : PolynomialRow) : Ext3 FGL :=
  b r.nextL1 * ((r.groupResult - r.running) - r.directSum)

def Circuit (r : PolynomialRow) : Prop :=
  r.residual24 = 0 ∧ r.residual25 = 0 ∧ r.residual26 = 0 ∧
  r.residual27 = 0 ∧ r.residual28 = 0 ∧ r.residual29 = 0 ∧
  r.residual30 = 0 ∧ r.residual31 = 0 ∧ r.residual32 = 0

def WithFinalizer (r : PolynomialRow) : Prop := r.Circuit ∧ r.residual33 = 0

/-- Local non-vacuity with genuine base-field inverses of nonzero source
constants. No inverse operation or Field instance on Ext3 is invented.
The finalizer group value is computed from this same row, not a free promise. -/
def constructed : PolynomialRow :=
  let cluster := -((104 : FGL)⁻¹)
  let running := cluster - (105 : FGL)⁻¹
  let continuation := -((12 : FGL)⁻¹)
  let direct := -((104 : FGL)⁻¹)
  { addr := 0, step := 0, sel := 0, stepDual := 0, selDual := 0
    valueLo := 0, valueHi := 0, wr := 0, lowIncrement := 0, highIncrement := 0
    segmentId := 0, isLastSegment := 1
    previousValueLo := 0, previousValueHi := 0, previousStep := 0, previousAddr := 0
    lastValueLo := 0, lastValueHi := 0, lastStep := 0, lastAddr := 0
    distanceBaseLo := 0, distanceBaseHi := 0, distanceEndLo := 0, distanceEndHi := 0
    alpha := b 0, gamma := b 1
    running := b running, previousRunning := b 0, cluster0 := b cluster, cluster1 := b 0
    direct0 := b continuation, direct1 := b 0
    direct2 := b direct, direct3 := b direct, direct4 := b direct, direct5 := b direct
    l1 := 0, nextL1 := 1
    groupResult := b (running + continuation + direct + direct + direct + direct) }

theorem constructed_satisfies : constructed.WithFinalizer := by
  have h104 : (104 : FGL) ≠ 0 := by decide
  have h105 : (105 : FGL) ≠ 0 := by decide
  have h12 : (12 : FGL) ≠ 0 := by decide
  unfold WithFinalizer Circuit
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals
    simp only [residual24, residual25, residual26, residual27, residual28,
      residual29, residual30, residual31, residual32, residual33, directSum,
      highDen, dualStepDen, lowDen, primaryDen, dualDen, previousDen, nextDen,
      constructed, b,
      ← Ext3.ofBase_zero, ← Ext3.ofBase_add, ← Ext3.ofBase_sub,
      ← Ext3.ofBase_mul, ← Ext3.ofBase_neg]
  all_goals
    first
    | rfl
    | apply congrArg Ext3.ofBase
      field_simp [h104, h105, h12] <;> ring

end PolynomialRow
end ZiskFv.AirsClean.Mem.Stage2
