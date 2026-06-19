import ZiskFv.Channels.SeamTagChain

/-!
# SPIKE (#76 PR-76.0 / PR-76.5): cross-segment seam on a NON-VACUOUS k≥2-row segment

**Make-or-break question.** The banked #103 capability (`SeamTagChain.boot_chain_derived`,
lifted to `fullRv64imEnsemble` by `FullEnsemble.SeamNonVacuity`) derives the cross-segment
value seam `seg_{i+1}.prev = seg_i.last` from channel balance — BUT only on a model where
**each segment is ONE `MemRow`** (`memWithDualMemBus` emits the seam per-row, ungated; the
witness `[v0, v1]` is one row per segment). A real Mem segment spans **k ≥ 2 rows**; the
per-row ungated emission makes a k-row segment emit k pulls + k pushes → balances only at
k = 1. As banked, the seam is therefore VACUOUS for real multi-row segments.

**The deep refactor (RESEARCH_XCAP §3 sequencing B → A → C):**
- **B** — add a per-row `seg_last` (`SEGMENT_LAST`) selector column to the row model.
- **A** — gate BOTH seam emissions by `seg_last`: the pull's multiplicity becomes
  `-seg_last` and the push's becomes `seg_last * (1 - is_last_segment)`. So a segment's
  k rows emit exactly ONE live pull + ONE live push (the `seg_last = 1` row) and `k - 1`
  DEAD (multiplicity-0) emissions.
- **C** — re-establish the `addChannel` balance for multi-row segments and re-prove a
  **k ≥ 2 non-vacuity witness** (the acceptance bar).

This file is the channel-level spike of B + A + C: it models a multi-row segment whose
rows carry the `seg_last`-gated emission, proves the gated multi-row interaction list has
the SAME balance as the engine's one-emission-per-segment `bootChainN` list (the dead
multiplicity-0 rows drop out of `balanceOf`), and therefore derives the cross-segment seam
from balance on a **k = 2-rows-per-segment, 2-segment** witness — the non-vacuous k ≥ 2
instance that defeats the laundering trap.

## Make-or-break lemma

`multiRowSegSeam_k2` (below): on a 2-segment trace where EACH segment has 2 rows (one
non-`seg_last` dead row + one `seg_last` live row), channel balance of the gated multi-row
seam list forces the cross-segment value seam `seg1.prev = seg0.last`. NON-VACUOUS:
`goodMultiRow_balanced` exhibits a concrete balanced 2×2-row witness; `multiRowSegSeam_k2`
fires on it.

## Trust note

No axioms. The whole derivation is kernel-only; it consumes the channel-balance trust
class (the same `BalancedInteractions` antecedent the banked #103 work consumes) and the
banked `SeamTagChain` engine verbatim. NO new project axiom, NO `sorry`, NO `native_decide`.
-/

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace ZiskFv.Spike.MultiRowSegmentSeam

open Goldilocks
open ZiskFv.Channels.SeamTagChain

/-! ## Foundational: multiplicity-0 interactions are balance-inert.

`balanceOf l msg` filters `l` by message then sums multiplicities. An interaction with
multiplicity `0` contributes `0` to every message's sum, so dropping it (or inserting it)
leaves `balanceOf` unchanged for every message. This is what lets a `seg_last`-gated k-row
segment (k − 1 dead rows) have the same balance as the engine's single-emission segment. -/

/-- A zero-multiplicity interaction does not change `balanceOf` for any message. -/
theorem balanceOf_cons_zero_mult (i : Interaction FGL) (rest : List (Interaction FGL))
    (hz : i.mult = 0) (msg : Array FGL) :
    balanceOf (i :: rest) msg = balanceOf rest msg := by
  simp only [balanceOf, List.filter_cons]
  split
  · simp only [List.map_cons, List.sum_cons]; rw [hz]; ring
  · rfl

/-- `BalancedInteractions` of `as` (the MULTI-ROW gated list) transfers to `bs` (the
    engine's one-emission-per-segment list) given a per-message `balanceOf` equality and
    the no-overflow bound on the SHORTER engine list. We do NOT need the lengths to match:
    the multi-row list is strictly LONGER (it carries `k-1` dead rows per segment), but its
    per-message balance equals the engine list's (the dead rows are multiplicity-0). The
    direction we use is multi-row balance ⇒ engine balance, so we discharge the engine
    list's own (smaller) overflow bound directly. -/
theorem engineBalanced_of_multiRow {as bs : List (Interaction FGL)}
    (hlen : bs.length < ringChar FGL ∨ ringChar FGL = 0)
    (hbal : ∀ msg, balanceOf bs msg = balanceOf as msg)
    (h : BalancedInteractions as) : BalancedInteractions bs := by
  refine ⟨hlen, ?_⟩
  intro msg; rw [hbal msg]; exact h.2 msg

/-! ## The B + A model: a `seg_last`-gated multi-row segment.

A segment now spans MULTIPLE rows. Each row carries a `seg_last` selector (`1` on the
segment's last row, `0` elsewhere) and a `pushGate` (`1 - is_last_segment`, the global
last-segment gate). The seam interactions a row emits (mirroring the would-be gated
`memWithDualMemBus`):

  pull  at tag `t`,     multiplicity `- seg_last`
  push  at tag `t + 1`, multiplicity `seg_last * pushGate`

A `seg_last = 0` row emits TWO multiplicity-0 interactions (DEAD); a `seg_last = 1` row
emits the live pull + gated push — exactly the engine's `segPair`. -/

/-- A row's `seg_last`-gated seam contribution: a pull at tag `t` (mult `-segLast`) and a
    push at tag `t + 1` (mult `segLast * pushGate`). With `segLast = 1` this is the live
    `[pullMsg5 …, gatedMsg5 pushGate …]`; with `segLast = 0` both multiplicities vanish. -/
def rowSeam (segLast pushGate : FGL) (prev last : SeamVal) (t : FGL) :
    List (Interaction FGL) :=
  [ gatedMsg5 (-segLast) (prev.msg t) (SeamVal.msg_size ..)
  , gatedMsg5 (segLast * pushGate) (last.msg (t + 1)) (SeamVal.msg_size ..) ]

/-- A DEAD row (`segLast = 0`) has `balanceOf = 0` for every message: both its
    interactions carry multiplicity `0`. -/
theorem balanceOf_deadRow (pushGate : FGL) (prev last : SeamVal) (t : FGL) (msg : Array FGL) :
    balanceOf (rowSeam 0 pushGate prev last t) msg = 0 := by
  simp only [rowSeam]
  rw [balanceOf_cons_zero_mult _ _ (by simp [gatedMsg5]) msg,
      balanceOf_cons_zero_mult _ _ (by simp [gatedMsg5]) msg]
  rfl

/-- A LIVE row (`segLast = 1`) has the same `balanceOf` as the engine's `segPair`-style
    pull + gated push (the two differ only in `assumeGuarantees`, which `balanceOf`
    ignores). -/
theorem balanceOf_liveRow (pushGate : FGL) (prev last : SeamVal) (t : FGL) (msg : Array FGL) :
    balanceOf (rowSeam 1 pushGate prev last t) msg
      = balanceOf [pullMsg5 (prev.msg t) (SeamVal.msg_size ..),
          gatedMsg5 pushGate (last.msg (t + 1)) (SeamVal.msg_size ..)] msg := by
  simp only [rowSeam, balanceOf, List.filter_cons, List.filter_nil,
    pullMsg5, gatedMsg5, neg_one_mul, one_mul]
  -- the two sides differ only in `assumeGuarantees` on the pull, which `balanceOf`
  -- (via `.map (·.mult)`) ignores; the `if`-guards and multiplicities are identical.
  split <;> split <;> simp

/-! ## A k = 2-rows-per-segment, 2-segment chain (the acceptance-bar instance).

We model TWO segments, EACH spanning TWO rows: one DEAD row (`seg_last = 0`) followed by
one LIVE row (`seg_last = 1`) carrying the segment's `prev`/`last` boundary at the
segment tag. seg0 is non-last (`pushGate = 1`); seg1 is last (`pushGate = 0`). The boot
push at tag 0 closes the chain. This is exactly the real emission once gated by
`SEGMENT_LAST` — a 9-interaction list (1 boot + 2 segments × (2 rows × 2 emissions =
4 interactions, but 1 dead) ... concretely 1 + 4 + 4 = 9). The DEAD rows carry ARBITRARY
boundary values (a real non-last row's `segment_last_*` columns are unconstrained until
its own `SEGMENT_LAST` fires), which is the whole point: balance must NOT depend on them. -/

/-- The two rows of a `seg_last`-gated segment: a dead leading row then the live last row.
    `deadPrev`/`deadLast` are the dead row's (arbitrary, unconstrained) boundary; `prev`/
    `last` are the live row's genuine segment boundary; `t` the segment tag; `pushGate` the
    `1 - is_last_segment` global gate. -/
def twoRowSeg (pushGate : FGL) (deadPrev deadLast prev last : SeamVal) (t : FGL) :
    List (Interaction FGL) :=
  rowSeam 0 pushGate deadPrev deadLast t ++ rowSeam 1 pushGate prev last t

/-- The full k = 2-rows-per-segment, 2-segment multi-row chain. -/
def multiRowChain2x2
    (boot : SeamVal)
    (d0p d0l p0 l0 : SeamVal) (t0 : FGL)         -- seg0: dead row + live row, tag t0
    (d1p d1l p1 l1 : SeamVal) (t1 : FGL)         -- seg1: dead row + live row, tag t1
    : List (Interaction FGL) :=
  pushMsg5 (boot.msg 0) (SeamVal.msg_size ..) ::
    (twoRowSeg 1 d0p d0l p0 l0 t0 ++ twoRowSeg 0 d1p d1l p1 l1 t1)

/-- `gatedMsg5 1` and `pushMsg5` have the same `balanceOf` for any singleton (they differ
    only in `assumeGuarantees`, which `balanceOf` ignores; both have multiplicity `1`). -/
theorem balanceOf_gatedMsg5_one (m : Array FGL) (hm : m.size = 5) (msg : Array FGL) :
    balanceOf [gatedMsg5 1 m (by simpa using hm)] msg
      = balanceOf [pushMsg5 m (by simpa using hm)] msg := by
  simp only [balanceOf, List.filter_cons, List.filter_nil, gatedMsg5, pushMsg5]

/-- **THE CORE REDUCTION (step C).** The k = 2-rows-per-segment multi-row chain has the
    SAME `balanceOf` (every message) as the engine's one-emission-per-segment `bootList2`.
    The DEAD rows drop out (`balanceOf_deadRow`); each LIVE row collapses to the engine's
    pull + gated push (`balanceOf_liveRow`). seg1's `pushGate = 0` matches `bootList2`'s
    gated-off last push. This is what makes the multi-row trace's balance equivalent to the
    engine's — the gating turns k rows into one effective emission per segment. -/
theorem balanceOf_multiRowChain2x2_eq_bootList2
    (boot : SeamVal)
    (d0p d0l p0 l0 : SeamVal) (t0 : FGL)
    (d1p d1l p1 l1 : SeamVal) (t1 : FGL) (msg : Array FGL) :
    balanceOf (multiRowChain2x2 boot d0p d0l p0 l0 t0 d1p d1l p1 l1 t1) msg
      = balanceOf (bootList2
          boot.v0 boot.v1 boot.addr boot.step
          p0.v0 p0.v1 p0.addr p0.step t0
          l0.v0 l0.v1 l0.addr l0.step
          p1.v0 p1.v1 p1.addr p1.step t1
          l1.v0 l1.v1 l1.addr l1.step 0) msg := by
  -- Decompose the multi-row chain into appended pieces:
  --   [boot] ++ deadRow0 ++ liveRow0 ++ deadRow1 ++ liveRow1.
  rw [show multiRowChain2x2 boot d0p d0l p0 l0 t0 d1p d1l p1 l1 t1
      = [pushMsg5 (boot.msg 0) (SeamVal.msg_size ..)]
        ++ rowSeam 0 1 d0p d0l t0 ++ rowSeam 1 1 p0 l0 t0
        ++ rowSeam 0 0 d1p d1l t1 ++ rowSeam 1 0 p1 l1 t1
      from by simp [multiRowChain2x2, twoRowSeg, List.append_assoc]]
  -- Distribute `balanceOf` over every append; dead rows vanish, live rows collapse to the
  -- engine's pull + gated push.
  rw [balanceOf_append, balanceOf_append, balanceOf_append, balanceOf_append,
      balanceOf_deadRow, balanceOf_deadRow, balanceOf_liveRow, balanceOf_liveRow]
  -- The engine's `bootList2` is boot push :: seg0(pull, push) ++ seg1(pull, gated push).
  -- Distribute its `balanceOf` the same way; seg0's push is `pushMsg5`, bridged to
  -- `gatedMsg5 1` by `balanceOf` guarantee-blindness; seg1's gated push (gate 0) matches.
  rw [bootList2]
  rw [show (pushMsg5 (seam5 boot.v0 boot.v1 boot.addr boot.step 0) (seam5_size ..) ::
        pullMsg5 (seam5 p0.v0 p0.v1 p0.addr p0.step t0) (seam5_size ..) ::
        pushMsg5 (seam5 l0.v0 l0.v1 l0.addr l0.step (t0 + 1)) (seam5_size ..) ::
        pullMsg5 (seam5 p1.v0 p1.v1 p1.addr p1.step t1) (seam5_size ..) ::
        [gatedMsg5 0 (seam5 l1.v0 l1.v1 l1.addr l1.step (t1 + 1)) (seam5_size ..)])
      = [pushMsg5 (boot.msg 0) (SeamVal.msg_size ..)]
        ++ ([pullMsg5 (p0.msg t0) (SeamVal.msg_size ..)]
        ++ [pushMsg5 (l0.msg (t0 + 1)) (SeamVal.msg_size ..)])
        ++ ([pullMsg5 (p1.msg t1) (SeamVal.msg_size ..)]
        ++ [gatedMsg5 0 (l1.msg (t1 + 1)) (SeamVal.msg_size ..)])
      from by simp only [SeamVal.msg, List.cons_append, List.nil_append, List.singleton_append]]
  rw [balanceOf_append, balanceOf_append, balanceOf_append, balanceOf_append]
  -- Split the LHS 2-element live-row lists into singletons via `balanceOf_append`.
  rw [show ([pullMsg5 (p0.msg t0) (SeamVal.msg_size ..),
        gatedMsg5 1 (l0.msg (t0 + 1)) (SeamVal.msg_size ..)] : List (Interaction FGL))
      = [pullMsg5 (p0.msg t0) (SeamVal.msg_size ..)]
        ++ [gatedMsg5 1 (l0.msg (t0 + 1)) (SeamVal.msg_size ..)] from rfl,
    show ([pullMsg5 (p1.msg t1) (SeamVal.msg_size ..),
        gatedMsg5 0 (l1.msg (t1 + 1)) (SeamVal.msg_size ..)] : List (Interaction FGL))
      = [pullMsg5 (p1.msg t1) (SeamVal.msg_size ..)]
        ++ [gatedMsg5 0 (l1.msg (t1 + 1)) (SeamVal.msg_size ..)] from rfl,
    balanceOf_append, balanceOf_append,
    balanceOf_gatedMsg5_one (l0.msg (t0 + 1)) (SeamVal.msg_size ..)]
  ring

/-! ## THE MAKE-OR-BREAK THEOREM: cross-segment seam from MULTI-ROW (k = 2) balance.

We now run the engine on the multi-row trace. From `BalancedInteractions` of the REAL
k = 2-rows-per-segment chain (the channel-balance trust class on a genuine multi-row Mem
trace), the core reduction transports the balance to the engine's `bootList2`, and
`SeamTagChain.boot_chain_derived` lands the cross-segment value seam
`seg1.prev = seg0.last`. Crucially the antecedent is balance of a chain where EACH segment
spans TWO rows — the k ≥ 2 instance the banked one-row-per-segment witness could not state. -/

/-- The `bootList2` engine list has fewer than `ringChar FGL` interactions (it has 5). -/
theorem bootList2_length_lt_ringChar
    (bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0 l0v0 l0v1 l0a l0s
     p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s g1 : FGL) :
    (bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0 l0v0 l0v1 l0a l0s
        p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s g1).length < ringChar FGL ∨ ringChar FGL = 0 := by
  left
  have : (5 : ℕ) < ringChar FGL := by
    haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
    rw [ringChar.eq FGL GL_prime]; norm_num
  simpa [bootList2] using this

/-- **THE MAKE-OR-BREAK LEMMA (#76 PR-76.0 / PR-76.5 acceptance bar).**

    For a 2-segment trace where EACH segment spans TWO `MemRow`s (one DEAD `seg_last = 0`
    row carrying arbitrary boundary `d0p/d0l`, `d1p/d1l`, then one LIVE `seg_last = 1` row
    carrying the segment's genuine boundary `p0/l0`, `p1/l1`), with seg1 the last segment
    (its `pushGate = 0`), channel balance of the `seg_last`-GATED multi-row seam emission
    FORCES the cross-segment value seam:

      `t0 = 0`, `t1 = 1`, and `seg1.prev (= p1) = seg0.last (= l0)`.

    This is the k ≥ 2 cross-segment seam derived from balance — the deliverable the banked
    one-row-per-segment model could not reach. The DEAD rows' boundary values
    (`d0p/d0l/d1p/d1l`) are GENUINELY FREE and play NO role: balance does not depend on
    them (the gating zeroes their emission), so the seam is forced by the live rows alone. -/
theorem multiRowSegSeam_k2
    (boot : SeamVal)
    (d0p d0l p0 l0 : SeamVal) (t0 : FGL)
    (d1p d1l p1 l1 : SeamVal) (t1 : FGL)
    (balance : BalancedInteractions
      (multiRowChain2x2 boot d0p d0l p0 l0 t0 d1p d1l p1 l1 t1)) :
    t0 = 0 ∧ t1 = 1
      ∧ seam5 p1.v0 p1.v1 p1.addr p1.step t1
        = seam5 l0.v0 l0.v1 l0.addr l0.step (t0 + 1) := by
  -- Transport the multi-row balance to the engine's `bootList2` balance (step C).
  have hengine : BalancedInteractions
      (bootList2 boot.v0 boot.v1 boot.addr boot.step
        p0.v0 p0.v1 p0.addr p0.step t0 l0.v0 l0.v1 l0.addr l0.step
        p1.v0 p1.v1 p1.addr p1.step t1 l1.v0 l1.v1 l1.addr l1.step 0) :=
    engineBalanced_of_multiRow (bootList2_length_lt_ringChar ..)
      (fun msg =>
        (balanceOf_multiRowChain2x2_eq_bootList2 boot d0p d0l p0 l0 t0 d1p d1l p1 l1 t1 msg).symm)
      balance
  -- Run the banked engine derivation on the transported balance.
  obtain ⟨ht0, ht1, _hseam0, hseam⟩ := boot_chain_derived
    boot.v0 boot.v1 boot.addr boot.step
    p0.v0 p0.v1 p0.addr p0.step t0 l0.v0 l0.v1 l0.addr l0.step
    p1.v0 p1.v1 p1.addr p1.step t1 l1.v0 l1.v1 l1.addr l1.step hengine
  exact ⟨ht0, ht1, hseam⟩

/-! ## NON-VACUITY (the anti-laundering guard — the acceptance bar).

`multiRowSegSeam_k2` is worthless if its antecedent `BalancedInteractions
(multiRowChain2x2 …)` is unsatisfiable, or only satisfiable for a degenerate one-row /
`rfl` instance. We exhibit a CONCRETE k = 2-rows-per-segment, 2-segment chain whose:

  * DEAD rows carry GENUINELY DISTINCT junk boundary values (NOT equal to the live
    boundary, NOT zero) — proving the gating truly suppresses them; and
  * LIVE rows carry the intended cross-segment chain (boot → seg0.last → seg1.prev seam).

We PROVE this concrete multi-row chain BALANCES (via the core reduction to the banked
`goodBootList2_balanced`) and run `multiRowSegSeam_k2` on it, landing the SEAM
`seg1.prev = seg0.last = (1,0,100,5)`. This is a genuine k = 2 (two rows per segment),
non-`rfl` witness — it defeats the laundering shape the one-row banked witness exhibits. -/

/-- The boot value: `(0,0,B,0)` at tag 0 (`B = 335544320`, ZisK's `internal_base_address`). -/
def vBoot : SeamVal := ⟨0, 0, 335544320, 0⟩

/-- seg0 DEAD row's junk prev boundary — distinct from every live value (note: a real
    non-`SEGMENT_LAST` row's `segment_last_*`/`previous_segment_*` columns are
    unconstrained, so this junk is exactly what a real dead row looks like). -/
def vDead0Prev : SeamVal := ⟨7, 7, 7, 7⟩
def vDead0Last : SeamVal := ⟨8, 8, 8, 8⟩
def vDead1Prev : SeamVal := ⟨9, 9, 9, 9⟩
def vDead1Last : SeamVal := ⟨11, 11, 11, 11⟩

/-- seg0 LIVE boundary: prev = boot `(0,0,B,0)`, last = `(1,0,100,5)`. -/
def vSeg0Prev : SeamVal := ⟨0, 0, 335544320, 0⟩
def vSeg0Last : SeamVal := ⟨1, 0, 100, 5⟩
/-- seg1 LIVE boundary: prev = seg0.last `(1,0,100,5)` (THE SEAM), last = `(2,0,200,9)`. -/
def vSeg1Prev : SeamVal := ⟨1, 0, 100, 5⟩
def vSeg1Last : SeamVal := ⟨2, 0, 200, 9⟩

/-- The concrete k = 2-rows-per-segment, 2-segment multi-row chain (9 interactions:
    boot push + 2 segments × (dead row 2 + live row 2)). -/
def goodMultiRow : List (Interaction FGL) :=
  multiRowChain2x2 vBoot
    vDead0Prev vDead0Last vSeg0Prev vSeg0Last 0
    vDead1Prev vDead1Last vSeg1Prev vSeg1Last 1

/-- Sanity: the DEAD rows are genuinely distinct from the live boundary (so the witness is
    NOT the degenerate "all rows identical" shape). -/
theorem goodMultiRow_dead_distinct :
    vDead0Prev ≠ vSeg0Prev ∧ vDead0Prev ≠ vSeg0Last
    ∧ vDead1Prev ≠ vSeg1Prev ∧ vDead1Prev ≠ vSeg1Last := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [vDead0Prev, vDead1Prev, vSeg0Prev, vSeg0Last, vSeg1Prev, vSeg1Last,
      ne_eq, SeamVal.mk.injEq, not_and] <;>
    intro h <;> exact absurd h (by decide)

/-- The concrete multi-row chain has 9 interactions (genuinely k = 2 per segment: each
    segment contributes 4 emissions, of which 2 are dead). NOT the one-row floor. -/
theorem goodMultiRow_length : goodMultiRow.length = 9 := by
  simp [goodMultiRow, multiRowChain2x2, twoRowSeg, rowSeam]

/-- **THE SATISFIABILITY WITNESS (k = 2 non-vacuity).** The concrete 2-rows-per-segment
    chain BALANCES: its `balanceOf` reduces (core reduction) to the engine's `goodBootList2`
    balance, which is the banked `goodBootList2_balanced`. The 4 DEAD interactions
    (multiplicity 0) drop out; the 5 live interactions are the intended boot chain. -/
theorem goodMultiRow_balanced : BalancedInteractions goodMultiRow := by
  refine ⟨?_, ?_⟩
  · left; rw [goodMultiRow_length]
    have : (9 : ℕ) < ringChar FGL := by
      haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
      rw [ringChar.eq FGL GL_prime]; norm_num
    simpa using this
  · intro msg
    rw [goodMultiRow,
      balanceOf_multiRowChain2x2_eq_bootList2 vBoot
        vDead0Prev vDead0Last vSeg0Prev vSeg0Last 0
        vDead1Prev vDead1Last vSeg1Prev vSeg1Last 1 msg]
    -- the reduced engine list IS `goodBootList2`; its balance is the banked fact.
    rw [show bootList2
          vBoot.v0 vBoot.v1 vBoot.addr vBoot.step
          vSeg0Prev.v0 vSeg0Prev.v1 vSeg0Prev.addr vSeg0Prev.step 0
          vSeg0Last.v0 vSeg0Last.v1 vSeg0Last.addr vSeg0Last.step
          vSeg1Prev.v0 vSeg1Prev.v1 vSeg1Prev.addr vSeg1Prev.step 1
          vSeg1Last.v0 vSeg1Last.v1 vSeg1Last.addr vSeg1Last.step 0
        = goodBootList2 from by
          simp [goodBootList2, bootList2, vBoot, vSeg0Prev, vSeg0Last, vSeg1Prev, vSeg1Last]]
    exact goodBootList2_balanced.2 msg

/-- **NON-VACUITY END-TO-END.** Running `multiRowSegSeam_k2` on the concrete BALANCED
    2-rows-per-segment witness lands the tags at `(0,1)` and the SEAM holds:
    `seg1.prev (1,0,100,5) = seg0.last (1,0,100,5)`. This certifies that the k ≥ 2
    cross-segment seam derivation from balance is NON-VACUOUS — the antecedent is
    satisfiable on a genuine 2-rows-per-segment trace (dead rows distinct from live),
    NOT only on the degenerate one-row instance the banked model was limited to. -/
theorem goodMultiRow_seam_holds :
    seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1) := by
  obtain ⟨_, _, hseam⟩ := multiRowSegSeam_k2 vBoot
    vDead0Prev vDead0Last vSeg0Prev vSeg0Last 0
    vDead1Prev vDead1Last vSeg1Prev vSeg1Last 1
    goodMultiRow_balanced
  simpa [vSeg1Prev, vSeg0Last] using hseam

end ZiskFv.Spike.MultiRowSegmentSeam

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom, NO
`native_decide`. The k ≥ 2 cross-segment seam derivation + its non-vacuity on the concrete
2-rows-per-segment witness are kernel-only. -/
#print axioms ZiskFv.Spike.MultiRowSegmentSeam.balanceOf_multiRowChain2x2_eq_bootList2
#print axioms ZiskFv.Spike.MultiRowSegmentSeam.multiRowSegSeam_k2
#print axioms ZiskFv.Spike.MultiRowSegmentSeam.goodMultiRow_balanced
#print axioms ZiskFv.Spike.MultiRowSegmentSeam.goodMultiRow_seam_holds
#print axioms ZiskFv.Spike.MultiRowSegmentSeam.goodMultiRow_dead_distinct
