import ZiskFv.AirsClean.Mem.Stage2.Literals
import ZiskFv.AirsClean.Mem.Stage2.PolynomialRow

/-! Internal typed local row factory. It accepts ONE source occurrence and a
physical row, not independently supplied cells, an equality certificate or a
validator promise. Source scalar projections below use only statically scalar
stage1/fixed cells; stage2 never passes through a scalar projection.

A successful typed row is a model image, not proof of actual native execution.
In particular the algebraic PolynomialRow.constructed witness is NOT claimed
to be materialized by a live Rust/C++ source occurrence. Packed stage1 and
compiled operand/opening/machine/ABI bindings are still genuine missing work.
-/
namespace ZiskFv.AirsClean.Mem.Stage2
open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

variable {source : SourceObject FGL}

private def baseWitness? (resolved : ResolvedOccurrence source) (row column : Nat) : Option FGL :=
  (witness? resolved row 1 column 0).map (·.c0)

private def baseAir? (resolved : ResolvedOccurrence source) (index : Nat) : Option FGL :=
  if index < 15 then (airValue? resolved index).map (·.c0) else none

private def baseFixed? (resolved : ResolvedOccurrence source) (row : Nat) (rotation : Int) : Option FGL :=
  (fixed? resolved row 1 rotation).map (·.c0)

/-- The exact union of cells used by source c24–c33, all from this source object.
The six direct terms are read separately at source AIR15–20, not repacked from
an arbitrary generated roster or supplied as independent arguments. -/
def decodeRow? (resolved : ResolvedOccurrence source) (row : Nat) : Option PolynomialRow := do
  if SourceFinalizer.memOccurrence resolved then
    let addr ← baseWitness? resolved row 0
    let step ← baseWitness? resolved row 1
    let sel ← baseWitness? resolved row 2
    let stepDual ← baseWitness? resolved row 4
    let selDual ← baseWitness? resolved row 5
    let valueLo ← baseWitness? resolved row 6
    let valueHi ← baseWitness? resolved row 7
    let wr ← baseWitness? resolved row 8
    let lowIncrement ← baseWitness? resolved row 10
    let highIncrement ← baseWitness? resolved row 11
    let segmentId ← baseAir? resolved 0
    let isLastSegment ← baseAir? resolved 2
    let previousValueLo ← baseAir? resolved 3
    let previousValueHi ← baseAir? resolved 4
    let previousStep ← baseAir? resolved 5
    let previousAddr ← baseAir? resolved 6
    let lastValueLo ← baseAir? resolved 7
    let lastValueHi ← baseAir? resolved 8
    let lastStep ← baseAir? resolved 9
    let lastAddr ← baseAir? resolved 10
    let distanceBaseLo ← baseAir? resolved 11
    let distanceBaseHi ← baseAir? resolved 12
    let distanceEndLo ← baseAir? resolved 13
    let distanceEndHi ← baseAir? resolved 14
    let alpha ← challenge? resolved 2 0
    let gamma ← challenge? resolved 2 1
    let running ← witness? resolved row 2 0 0
    let previousRunning ← witness? resolved row 2 0 (-1)
    let cluster0 ← witness? resolved row 2 1 0
    let cluster1 ← witness? resolved row 2 2 0
    let direct0 ← airValue? resolved 15
    let direct1 ← airValue? resolved 16
    let direct2 ← airValue? resolved 17
    let direct3 ← airValue? resolved 18
    let direct4 ← airValue? resolved 19
    let direct5 ← airValue? resolved 20
    let l1 ← baseFixed? resolved row 0
    let nextL1 ← baseFixed? resolved row 1
    let groupResult ← groupValue? resolved 0
    return { addr, step, sel, stepDual, selDual, valueLo, valueHi, wr,
      lowIncrement, highIncrement, segmentId, isLastSegment,
      previousValueLo, previousValueHi, previousStep, previousAddr,
      lastValueLo, lastValueHi, lastStep, lastAddr,
      distanceBaseLo, distanceBaseHi, distanceEndLo, distanceEndHi,
      alpha, gamma, running, previousRunning, cluster0, cluster1,
      direct0, direct1, direct2, direct3, direct4, direct5, l1, nextL1, groupResult }
  else none

/-- Concrete internal polynomial-circuit test of a successfully decoded row.
This is not installed in Accepted/Valid_Mem or passed as a caller premise. -/
def decodedCircuit? (resolved : ResolvedOccurrence source) (row : Nat) : Option Bool := do
  let values ← decodeRow? resolved row
  return decide values.WithFinalizer

theorem decode_rejects_other_registry (resolved : ResolvedOccurrence source) (row : Nat)
    (notMem : SourceFinalizer.memOccurrence resolved = false) :
    decodeRow? resolved row = none := by
  simp [decodeRow?, notMem]

theorem no_independent_parameter_buffers (resolved : ResolvedOccurrence source) :
    (resolved.params false).airvalues = resolved.slotData.airvalues ∧
    (resolved.params false).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params false).challenges = source.globals.challenges := ⟨rfl, rfl, rfl⟩

private theorem baseWords_reembed (words : Option (Array FGL)) :
    (baseWords? words).map (fun value => Ext3.ofBase value.c0) = baseWords? words := by
  unfold baseWords?
  cases h : SourceFinalizer.scalarWord? words <;> rfl

private theorem witness_reembed (resolved : ResolvedOccurrence source) (row column : Nat) :
    (witness? resolved row 1 column 0).map (fun value => Ext3.ofBase value.c0) =
      witness? resolved row 1 column 0 := by
  by_cases bound : column < 13 <;>
    simp [witness?, bound, Option.map_bind, Function.comp_def, baseWords_reembed]

private theorem air_reembed (resolved : ResolvedOccurrence source) (index : Nat)
    (bound : index < 15) :
    (airValue? resolved index).map (fun value => Ext3.ofBase value.c0) =
      airValue? resolved index := by
  have within : index < 21 := by omega
  simp [airValue?, bound, within, Option.map_bind, Function.comp_def, apply_ite,
    baseWords_reembed]

private theorem fixed_reembed (resolved : ResolvedOccurrence source) (row : Nat) (rotation : Int) :
    (fixed? resolved row 1 rotation).map (fun value => Ext3.ofBase value.c0) =
      fixed? resolved row 1 rotation := by
  simp [fixed?, baseWords_reembed]

private theorem witness_from_decoder (resolved : ResolvedOccurrence source) (row column : Nat)
    (value : FGL) (h : baseWitness? resolved row column = some value) :
    witness? resolved row 1 column 0 = some (Ext3.ofBase value) := by
  have lifted := congrArg (Option.map Ext3.ofBase) h
  simpa only [baseWitness?, Option.map_map, Function.comp_def, witness_reembed,
    Option.map_some] using lifted

private theorem air_from_decoder (resolved : ResolvedOccurrence source) (index : Nat)
    (bound : index < 15) (value : FGL) (h : baseAir? resolved index = some value) :
    airValue? resolved index = some (Ext3.ofBase value) := by
  have lifted := congrArg (Option.map Ext3.ofBase) h
  simpa only [baseAir?, if_pos bound, Option.map_map, Function.comp_def,
    air_reembed resolved index bound, Option.map_some] using lifted

private theorem fixed_from_decoder (resolved : ResolvedOccurrence source) (row : Nat) (rotation : Int)
    (value : FGL) (h : baseFixed? resolved row rotation = some value) :
    fixed? resolved row 1 rotation = some (Ext3.ofBase value) := by
  have lifted := congrArg (Option.map Ext3.ofBase) h
  simpa only [baseFixed?, Option.map_map, Function.comp_def, fixed_reembed,
    Option.map_some] using lifted

/-- A postcondition of the computed factory, not a new caller/source-validity
certificate: each actual c24–c32 evaluates to the corresponding independent
typed local polynomial on the returned same-source row. -/
theorem decode_polynomial_correspondence (resolved : ResolvedOccurrence source) (row : Nat)
    (values : PolynomialRow) (decoded : decodeRow? resolved row = some values)
    (equation : Fin 9) :
    evaluate? resolved row (actualNonlinear equation) = some (values.residual equation) := by
  by_cases mem : SourceFinalizer.memOccurrence resolved = true
  · simp only [decodeRow?, mem, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq] at decoded
    rcases decoded with
      ⟨addr, haddr, step, hstep, sel, hsel, stepDual, hstepDual, selDual, hselDual,
       valueLo, hvalueLo, valueHi, hvalueHi, wr, hwr, lowIncrement, hlowIncrement,
       highIncrement, hhighIncrement, segmentId, hsegmentId, isLastSegment, hisLastSegment,
       previousValueLo, hpreviousValueLo, previousValueHi, hpreviousValueHi,
       previousStep, hpreviousStep, previousAddr, hpreviousAddr,
       lastValueLo, hlastValueLo, lastValueHi, hlastValueHi, lastStep, hlastStep,
       lastAddr, hlastAddr, distanceBaseLo, hdistanceBaseLo, distanceBaseHi, hdistanceBaseHi,
       distanceEndLo, hdistanceEndLo, distanceEndHi, hdistanceEndHi,
       alpha, halpha, gamma, hgamma, running, hrunning, previousRunning, hpreviousRunning,
       cluster0, hcluster0, cluster1, hcluster1,
       direct0, hdirect0, direct1, hdirect1, direct2, hdirect2, direct3, hdirect3,
       direct4, hdirect4, direct5, hdirect5, l1, hl1, nextL1, hnextL1,
       groupResult, hgroupResult, rfl⟩
    have wa := witness_from_decoder resolved row 0 addr haddr
    have ws := witness_from_decoder resolved row 1 step hstep
    have wsel := witness_from_decoder resolved row 2 sel hsel
    have wd := witness_from_decoder resolved row 4 stepDual hstepDual
    have wsd := witness_from_decoder resolved row 5 selDual hselDual
    have wlo := witness_from_decoder resolved row 6 valueLo hvalueLo
    have whi := witness_from_decoder resolved row 7 valueHi hvalueHi
    have ww := witness_from_decoder resolved row 8 wr hwr
    have wl := witness_from_decoder resolved row 10 lowIncrement hlowIncrement
    have wh := witness_from_decoder resolved row 11 highIncrement hhighIncrement
    have a0 := air_from_decoder resolved 0 (by decide) segmentId hsegmentId
    have a2 := air_from_decoder resolved 2 (by decide) isLastSegment hisLastSegment
    have a3 := air_from_decoder resolved 3 (by decide) previousValueLo hpreviousValueLo
    have a4 := air_from_decoder resolved 4 (by decide) previousValueHi hpreviousValueHi
    have a5 := air_from_decoder resolved 5 (by decide) previousStep hpreviousStep
    have a6 := air_from_decoder resolved 6 (by decide) previousAddr hpreviousAddr
    have a7 := air_from_decoder resolved 7 (by decide) lastValueLo hlastValueLo
    have a8 := air_from_decoder resolved 8 (by decide) lastValueHi hlastValueHi
    have a9 := air_from_decoder resolved 9 (by decide) lastStep hlastStep
    have a10 := air_from_decoder resolved 10 (by decide) lastAddr hlastAddr
    have a11 := air_from_decoder resolved 11 (by decide) distanceBaseLo hdistanceBaseLo
    have a12 := air_from_decoder resolved 12 (by decide) distanceBaseHi hdistanceBaseHi
    have a13 := air_from_decoder resolved 13 (by decide) distanceEndLo hdistanceEndLo
    have a14 := air_from_decoder resolved 14 (by decide) distanceEndHi hdistanceEndHi
    have f0 := fixed_from_decoder resolved row 0 l1 hl1
    rw [actualNonlinear_eq_expectedNonlinear]
    fin_cases equation <;>
      simp only [evaluate?, mem, ↓reduceIte, expectedNonlinear, expected24, expected25, expected26,
        expected27, expected28, expected29, expected30, expected31, expected32,
        sourceAlpha, sourceGamma, sourceHornerStep, highIncrementDenominator,
        dualStepDenominator, primaryMemoryDenominator, dualMemoryDenominator,
        previousContinuationDenominator, nextContinuationDenominator,
        polynomial?, literal_zero, literal_one, literal_eight, literal_ten,
        literal_eleven, literal_range24, literal_range16, literal_range22,
        literal_continuation, literal_negative_one, Option.bind_some,
        wa, ws, wsel, wd, wsd, wlo, whi, ww, wl, wh,
        a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, f0,
        halpha, hgamma, hrunning, hpreviousRunning, hcluster0, hcluster1,
        hdirect0, hdirect1, hdirect2, hdirect3, hdirect4, hdirect5,
        PolynomialRow.residual, PolynomialRow.residual24, PolynomialRow.residual25,
        PolynomialRow.residual26, PolynomialRow.residual27, PolynomialRow.residual28,
        PolynomialRow.residual29, PolynomialRow.residual30, PolynomialRow.residual31,
        PolynomialRow.residual32, PolynomialRow.highDen, PolynomialRow.dualStepDen,
        PolynomialRow.lowDen, PolynomialRow.primaryDen, PolynomialRow.dualDen,
        PolynomialRow.previousDen, PolynomialRow.nextDen,
        ← Ext3.ofBase_add, ← Ext3.ofBase_sub, ← Ext3.ofBase_mul]
  · simp [decodeRow?, mem] at decoded

end ZiskFv.AirsClean.Mem.Stage2
