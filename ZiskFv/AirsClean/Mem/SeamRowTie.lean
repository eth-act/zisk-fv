import ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity

/-!
# Tying the seam boundary columns to real Mem-row state (XCAP #103, route (b), L5 step 1)

The L1 cross-segment seam (`SeamTagChain.boot_chain_derived` /
`boot_chain_derived_generalN`, lifted to the real `fullRv64imEnsemble` by
`SeamNonVacuity.seam_value_equality`) forces, for adjacent segments,

```
seg_{i+1}.previous_segment_* = seg_i.segment_last_*
```

i.e. it equates the CHANNEL / emission boundary columns. By itself this relates
the *free* `previous_segment_*` / `segment_last_*` columns of `MemRow`, not actual
memory state. This file closes that gap with the row-local **`segment_every_row`
tie** (mem.pil's `SEGMENT_LAST` clauses), which pins `segment_last_*` to the
segment's genuine last Mem-row state.

## The tie (mirrored faithfully from `mem.pil`)

`mem.pil:87` defines `SEGMENT_LAST = SEGMENT_L1'` — it is `1` exactly on the LAST
row of a segment (the row whose successor starts a new segment). On that row the
PIL forces the `segment_last_*` air-values to the row's own memory state
(`mem.pil:212-230`):

```
for (int i = 0; i < RC; i++)            // mem.pil:212-216
    SEGMENT_LAST * (value[i] - segment_last_value[i]) === 0;
SEGMENT_LAST * (addr - segment_last_addr) === 0;                       // mem.pil:220
// dual-aware effective step:                                          // mem.pil:226
SEGMENT_LAST * (sel_dual * (step_dual - step) + step - segment_last_step) === 0;
```

So `segment_last_*` IS the segment's genuine last memory state (value chunks,
address, and the dual-aware effective step).

For the route-(b) single-`MemRow`-per-segment model, each segment's row is its
own last row (its successor begins the next segment), so `SEGMENT_LAST = 1` and
the four clauses above specialize to the row-local predicate
`SegmentLastRowTie` below. The `previous_segment_*` side is what the SEAM equates
to the prior segment's `segment_last_*`; composing the two yields the genuine
cross-segment memory continuation #76 needs:

```
seg_{i+1}.previous_segment_* (its incoming boundary)
  = seg_i.segment_last_*      (the SEAM, from balance)
  = seg_i's real last Mem-row state (value, addr, effective step)   (the TIE).
```

## Constructibility

The tie is row-local and EXACTLY the `mem.pil:212-230` clauses with
`SEGMENT_LAST = 1` (the value `SEGMENT_LAST` takes on a segment's last row). It is
NOT stronger than the PIL: the real ZisK Mem trace satisfies it on every
segment-last row by construction. The non-vacuity witnesses `goodSeg0` / `goodSeg1`
(from `SeamNonVacuity`) satisfy it: both carry `segment_last_* = (value_0,
value_1, addr, step)` with `sel_dual = 0`, so the tie holds with the effective
step collapsing to `step` (`good_seg0_tie` / `good_seg1_tie`).

## Trust note

No axioms. The cross-segment continuity theorem composes the balance-derived seam
(channel-balance trust class, already in `AcceptedTrace.balanced`) with the
row-local `SegmentLastRowTie` (a `mem.pil:212-230` constraint, constructible).
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.Channels.SeamTagChain (seam5 SeamVal)
open ZiskFv.AirsClean.FullEnsemble.SeamNonVacuity

/-- The dual-aware effective memory step of a `MemRow` (`mem.pil:226`'s
    `sel_dual * (step_dual - step) + step`). On a non-dual row (`sel_dual = 0`)
    it is just `step`. -/
@[reducible]
def MemRow.effectiveStep (row : MemRow FGL) : FGL :=
  row.sel_dual * (row.step_dual - row.step) + row.step

/-- **The row-local `SEGMENT_LAST` tie** (`mem.pil:212-230`, specialized to a
    segment's LAST row where `SEGMENT_LAST = 1`).

    On the last row of a segment, the `segment_last_*` air-values equal that
    row's own memory state: value chunks, address, and the dual-aware effective
    step. This is the four `SEGMENT_LAST * (... - segment_last_*) === 0` clauses
    of `mem.pil` evaluated at `SEGMENT_LAST = 1`. -/
def MemRow.SegmentLastRowTie (row : MemRow FGL) : Prop :=
  row.value_0 - row.segment_last_value_0 = 0
  ∧ row.value_1 - row.segment_last_value_1 = 0
  ∧ row.addr - row.segment_last_addr = 0
  ∧ row.effectiveStep - row.segment_last_step = 0

/-- The `SEGMENT_LAST` tie pins `segment_last_value_0` to the row's low value
    chunk (`mem.pil:215`). -/
theorem segment_last_value_0_eq_of_tie {row : MemRow FGL}
    (h : row.SegmentLastRowTie) : row.segment_last_value_0 = row.value_0 := by
  have := h.1; linear_combination -this

/-- The `SEGMENT_LAST` tie pins `segment_last_value_1` to the row's high value
    chunk (`mem.pil:215`). -/
theorem segment_last_value_1_eq_of_tie {row : MemRow FGL}
    (h : row.SegmentLastRowTie) : row.segment_last_value_1 = row.value_1 := by
  have := h.2.1; linear_combination -this

/-- The `SEGMENT_LAST` tie pins `segment_last_addr` to the row's address
    (`mem.pil:220`). -/
theorem segment_last_addr_eq_of_tie {row : MemRow FGL}
    (h : row.SegmentLastRowTie) : row.segment_last_addr = row.addr := by
  have := h.2.2.1; linear_combination -this

/-- The `SEGMENT_LAST` tie pins `segment_last_step` to the row's effective step
    (`mem.pil:226`). -/
theorem segment_last_step_eq_of_tie {row : MemRow FGL}
    (h : row.SegmentLastRowTie) :
    row.segment_last_step = row.effectiveStep := by
  have := h.2.2.2; linear_combination -this

/-- The full `SEGMENT_LAST` tie as a single `seam5` tuple equality: the
    `segment_last_*` boundary tuple (tagged `segment_id + 1`, the PUSH tag) equals
    the row's genuine last memory state `(value_0, value_1, addr, effectiveStep)`
    (same tag). -/
theorem segment_last_seam5_eq_row_state_of_tie {row : MemRow FGL}
    (h : row.SegmentLastRowTie) :
    seam5 row.segment_last_value_0 row.segment_last_value_1
        row.segment_last_addr row.segment_last_step (row.segment_id + 1)
      = seam5 row.value_0 row.value_1 row.addr row.effectiveStep
          (row.segment_id + 1) := by
  rw [segment_last_value_0_eq_of_tie h, segment_last_value_1_eq_of_tie h,
    segment_last_addr_eq_of_tie h, segment_last_step_eq_of_tie h]

/-! ## THE CROSS-SEGMENT REAL-MEMORY CONTINUITY THEOREM.

Composing the balance-derived seam (`SeamNonVacuity.seam_value_equality`:
`seg1.previous_segment_* = seg0.segment_last_*`) with the row-local
`SEGMENT_LAST` tie on `seg0` (`seg0.segment_last_* = seg0`'s real last memory
state), we get: `seg1`'s incoming boundary equals `seg0`'s genuine last Mem-row
state. This is the cross-segment memory continuation #76 consumes — the
boundary columns now relate REAL Mem-row state, not free emission columns. -/

/-- **CROSS-SEGMENT REAL-MEMORY CONTINUITY (XCAP #103, route (b), L5 step 1).**

    For a real `fullRv64imEnsemble` accepted trace with `seg0` non-last and
    `seg1` the last segment, whose seam channel balances (the channel-balance
    trust class carried by `AcceptedTrace.balanced`), AND with the row-local
    `SEGMENT_LAST` tie holding on `seg0` (a `mem.pil:212-230` constraint), the
    incoming memory boundary of `seg1` equals the GENUINE LAST MEM-ROW STATE of
    `seg0`:

      `seg1.previous_segment_* = (seg0.value_0, seg0.value_1, seg0.addr,
                                  seg0.effectiveStep)`

    as a tagged `seam5` tuple at tag `seg0.segment_id + 1 = 1`.

    The first two conjuncts (`seg0.segment_id = 0`, `seg1.segment_id = 1`) come
    from the seam's tag derivation; the tuple equality is the real-memory
    continuation. NO free emission column is left dangling: the seam supplies the
    channel-column equality and the tie collapses `seg0.segment_last_*` onto
    `seg0`'s real Mem-row memory state. -/
theorem cross_segment_real_memory_continuity
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    (vb : BootRow FGL) (v0 v1 : MemRow FGL)
    (publicInput : unit FGL) (data : ProverData FGL)
    (h0 : v0.is_last_segment = 0) (h1 : v1.is_last_segment = 1)
    (hl0 : v0.seg_last = 1) (hl1 : v1.seg_last = 1)
    (hseam : Air.Flat.EnsembleWitness.BalancedChannel
      (mkFullWitness (length := length) (program := program) vb v0 v1 publicInput data)
      ZiskFv.Channels.SegmentContinuation.SeamContChannel.toRaw)
    (h_tie : v0.SegmentLastRowTie) :
    v0.segment_id = 0 ∧ v1.segment_id = 1
      ∧ seam5 v1.previous_segment_value_0 v1.previous_segment_value_1
          v1.previous_segment_addr v1.previous_segment_step v1.segment_id
        = seam5 v0.value_0 v0.value_1 v0.addr v0.effectiveStep
            (v0.segment_id + 1) := by
  obtain ⟨ht0, ht1, hseamEq⟩ :=
    seam_value_equality (length := length) (program := program)
      vb v0 v1 publicInput data h0 h1 hl0 hl1 hseam
  refine ⟨ht0, ht1, ?_⟩
  -- `hseamEq : seg1.previous = seg0.segment_last_*` (the SEAM, channel columns)
  -- `tie    : seg0.segment_last_* = seg0's real last state` (the TIE)
  rw [hseamEq, segment_last_seam5_eq_row_state_of_tie h_tie]

/-! ## NON-VACUITY: the strengthened Spec is still satisfiable.

`cross_segment_real_memory_continuity` adds the `SegmentLastRowTie` hypothesis on
`seg0`. To rule out vacuity (an overstrong tie would quantify over `MemRow`s no
real trace produces), we confirm the existing non-vacuity witnesses `goodSeg0` /
`goodSeg1` STILL satisfy the strengthened Spec, then run the continuity theorem
on the concrete real-ensemble witness. -/

/-- `goodSeg0` (the seg0 non-vacuity witness) satisfies the row-local
    `SEGMENT_LAST` tie: its `segment_last_* = (1, 0, 100, 5)` matches its
    `(value_0, value_1, addr, effectiveStep) = (1, 0, 100, 5)` (`sel_dual = 0`, so
    the effective step is `step = 5`). CONSTRUCTIBILITY of the strengthened Spec. -/
theorem good_seg0_tie : goodSeg0.SegmentLastRowTie := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [MemRow.effectiveStep]

/-- `goodSeg1` (the seg1 / last-segment witness) likewise satisfies the tie:
    `segment_last_* = (2, 0, 200, 9) = (value_0, value_1, addr, effectiveStep)`.
    Confirms the tie is satisfiable on EVERY segment of the witness. -/
theorem good_seg1_tie : goodSeg1.SegmentLastRowTie := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [MemRow.effectiveStep]

/-- **NON-VACUITY of the cross-segment real-memory continuity** — run on the
    concrete balanced 2-NONZERO-segment real-ensemble witness. The tags resolve
    to `(0, 1)` and `seg1`'s incoming boundary equals `seg0`'s GENUINE last
    Mem-row state `(value_0, value_1, addr, effectiveStep) = (1, 0, 100, 5)` (NOT
    a free emission column). Certifies the tie is non-vacuous end-to-end on the
    REAL `fullRv64imEnsemble`. -/
theorem good_cross_segment_continuity
    (length : ℕ) (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (publicInput : unit FGL) (data : ProverData FGL) :
    seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1) := by
  obtain ⟨_, _, hcont⟩ :=
    cross_segment_real_memory_continuity (length := length) (program := program)
      goodBoot goodSeg0 goodSeg1 publicInput data (by rfl) (by rfl) (by rfl) (by rfl)
      (good_seam_balancedChannel (length := length) (program := program)
        publicInput data)
      good_seg0_tie
  simp only [MemRow.effectiveStep] at hcont
  exact hcont

end ZiskFv.AirsClean.Mem

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom, NO
`native_decide`. The cross-segment real-memory continuity (boundary cols tied to
real Mem-row state) is kernel-only and NON-VACUOUSLY satisfied by the concrete
2-nonzero-segment witness. -/
#print axioms ZiskFv.AirsClean.Mem.segment_last_seam5_eq_row_state_of_tie
#print axioms ZiskFv.AirsClean.Mem.cross_segment_real_memory_continuity
#print axioms ZiskFv.AirsClean.Mem.good_seg0_tie
#print axioms ZiskFv.AirsClean.Mem.good_seg1_tie
#print axioms ZiskFv.AirsClean.Mem.good_cross_segment_continuity
