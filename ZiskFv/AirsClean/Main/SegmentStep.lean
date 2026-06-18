import ZiskFv.Field.Goldilocks

/-!
# Main `SEGMENT_STEP` fixed column + `STEP` consecutiveness (XCAP #100, PIN (ii))

PIN (ii) of the #100 cross-row PC handshake feasibility gate. The PC-continuation
channel seam relates the row tagged `main_step` (pull) to the row tagged
`main_step + 1` (push). For the seam to connect PHYSICALLY ADJACENT rows we need

  `main_step (i + 1) = main_step i + 1`     within a segment.

Today `main_step` is a FREE witness column with no consecutiveness constraint
(`AirsClean/Main/Row.lean:109`, `Circuit.lean:229`). This module supplies the
missing fact, FAITHFULLY, from the PIL.

## PIL faithfulness (the two cited clauses)

`main.pil:19-20` declares two FIXED (preprocessed) columns:

```
col fixed SEGMENT_L1   = [1,0...];     -- the segment-boundary marker (already modelled)
col fixed SEGMENT_STEP = [0..(N-1)];   -- the in-segment row index 0,1,2,…,N-1
```

`main.pil:90` defines the timestamp `STEP` (the Lean `main_step`) as a `const expr`:

```
const expr STEP = main_segment * N + SEGMENT_STEP;
```

where `main_segment` is a per-SEGMENT air value (`main.pil:73`), CONSTANT across a
segment. So within one segment `main_segment * N` is a fixed constant and the only
varying term is `SEGMENT_STEP`, which is `[0,1,2,…]`. Hence

  `STEP (i+1) − STEP i = SEGMENT_STEP (i+1) − SEGMENT_STEP i = (i+1) − i = 1`.

## Modelling idiom (mirrors the Mem `SEGMENT_L1` fixed column)

The live Clean/AirsClean layer already models a PIL fixed column as a `Prop`
record of its known per-row values plus a deterministic constructor — see
`ZiskFv/AirsClean/FullEnsemble/Balance.lean:4943`
(`MemTableGeneratedFixedColumnFacts` / `segmentWithFixedL1`). We mirror that:

* `SegmentStepFixedColumnFacts` — the `Prop` recording `SEGMENT_STEP`'s known
  consecutive shape (the audit-visible fixed-column obligation).
* `fixedSegmentStep` — the deterministic shape `fun row => (row : FGL)`.
* `fixedSegmentStep_facts` — constructibility: the deterministic shape satisfies
  the facts.

`main_step = main_segment * N + SEGMENT_STEP` is recorded by `MainStepFacts`,
the `const expr` from `main.pil:90` applied per row.

## Trust note

No axioms. No `Valid_<AIR>` constraint is strengthened: this is a NEW per-row
relation mirroring a real PIL `const expr` + a real PIL fixed column, NOT an added
constraint on the existing `Spec`. Kernel-only (`#print axioms` at the bottom).
-/

namespace ZiskFv.AirsClean.Main.SegmentStep

open Goldilocks

/-! ## The `SEGMENT_STEP` fixed column. -/

/-- Fixed-column facts for the `SEGMENT_STEP` preprocessed column
    (`main.pil:20`: `col fixed SEGMENT_STEP = [0..(N-1)]`).

    The only property the handshake needs is **consecutiveness**: the value at
    row `i + 1` is the value at row `i` plus one. (The boundary value
    `segmentStep 0 = 0` is recorded too; it is what pins the absolute scale, but
    the seam only consumes the increment.) -/
structure SegmentStepFixedColumnFacts (segmentStep : ℕ → FGL) : Prop where
  /-- `SEGMENT_STEP` starts at `0` on the first row of the segment. -/
  first : segmentStep 0 = 0
  /-- `SEGMENT_STEP` increments by `1` each row: `[0,1,2,…]`. -/
  consecutive : ∀ i : ℕ, segmentStep (i + 1) = segmentStep i + 1

/-- The deterministic `SEGMENT_STEP` shape `[0,1,2,…]`: row `r ↦ (r : FGL)`.
    Mirrors `segmentWithFixedL1` (`Balance.lean:4955`) for `SEGMENT_L1`. -/
@[reducible]
def fixedSegmentStep : ℕ → FGL := fun row => (row : FGL)

/-- Constructibility: the deterministic `[0,1,2,…]` shape satisfies the fixed-
    column facts. (Mirrors `memTableGeneratedFixedColumnFacts_of_segmentWithFixedL1`.) -/
theorem fixedSegmentStep_facts : SegmentStepFixedColumnFacts fixedSegmentStep where
  first := by simp [fixedSegmentStep]
  consecutive := by
    intro i
    simp [fixedSegmentStep, Nat.cast_add, Nat.cast_one]

/-! ## The `STEP` (`main_step`) composed timestamp. -/

/-- The `main.pil:90` `const expr STEP = main_segment * N + SEGMENT_STEP`, recorded
    per row. `mainSegment` is the per-segment air value (`main.pil:73`), CONSTANT
    across the segment — hence taken as a single `FGL` scalar, not a per-row
    function. `N` is the segment length (the trace height). -/
structure MainStepFacts
    (mainStep : ℕ → FGL) (mainSegment : FGL) (N : ℕ) (segmentStep : ℕ → FGL) :
    Prop where
  /-- `STEP row = main_segment * N + SEGMENT_STEP row` for every row. -/
  step_def : ∀ row : ℕ, mainStep row = mainSegment * (N : FGL) + segmentStep row

/-! ## The payoff: `main_step` consecutiveness within a segment. -/

/-- **PIN (ii) — `main_step` CONSECUTIVENESS.** From the PIL `STEP` definition
    (`main.pil:90`) and the `SEGMENT_STEP` fixed column's consecutive shape
    (`main.pil:20`), the composed timestamp increments by exactly one each row
    within a segment:

      `main_step (i + 1) = main_step i + 1`.

    The per-segment constant `main_segment * N` cancels in the difference; only
    `SEGMENT_STEP`'s `+1` increment survives. This is precisely the adjacency the
    PC-continuation channel seam needs to connect physically adjacent rows. -/
theorem main_step_consecutive
    (mainStep : ℕ → FGL) (mainSegment : FGL) (N : ℕ) (segmentStep : ℕ → FGL)
    (h_step : MainStepFacts mainStep mainSegment N segmentStep)
    (h_seg : SegmentStepFixedColumnFacts segmentStep)
    (i : ℕ) :
    mainStep (i + 1) = mainStep i + 1 := by
  rw [h_step.step_def (i + 1), h_step.step_def i, h_seg.consecutive i]
  ring

/-- The concrete, fully-constructed instance: with the deterministic
    `SEGMENT_STEP = [0,1,2,…]` shape and any per-segment `main_segment` / length
    `N`, the composed timestamp `STEP = main_segment * N + SEGMENT_STEP` is
    consecutive. NON-VACUITY: the antecedents of `main_step_consecutive` are
    satisfiable by a concrete inhabitant (the deterministic fixed column). -/
theorem main_step_consecutive_concrete (mainSegment : FGL) (N : ℕ) (i : ℕ) :
    (fun row => mainSegment * (N : FGL) + fixedSegmentStep row) (i + 1)
      = (fun row => mainSegment * (N : FGL) + fixedSegmentStep row) i + 1 :=
  main_step_consecutive
    (fun row => mainSegment * (N : FGL) + fixedSegmentStep row)
    mainSegment N fixedSegmentStep
    ⟨fun _ => rfl⟩
    fixedSegmentStep_facts
    i

end ZiskFv.AirsClean.Main.SegmentStep

/-! ## Axiom-closure check (kernel-only: `propext`, `Classical.choice`, `Quot.sound`). -/
#print axioms ZiskFv.AirsClean.Main.SegmentStep.fixedSegmentStep_facts
#print axioms ZiskFv.AirsClean.Main.SegmentStep.main_step_consecutive
#print axioms ZiskFv.AirsClean.Main.SegmentStep.main_step_consecutive_concrete
