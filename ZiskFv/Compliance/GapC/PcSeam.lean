import ZiskFv.Channels.SeamTagChain
import ZiskFv.AirsClean.Main.SegmentStep
import ZiskFv.AirsClean.Main.Constraints

/-!
# PR-X100.1a — the Main PC-continuation seam as a THEOREM (`pc_seam_of_balanced`)

This module is the #100 analogue of `ZiskFv/Channels/SeamTagChain.lean`'s
general-N memory boot chain (`boot_chain_derived_generalN`), adapted to the Main
PC-continuation channel. The deliverable is `pc_seam_of_balanced`: for the real
Main ensemble's PC chain, channel balance forces, for every adjacent row pair,

  `pc (i+1) = (pcLastMessage (row i)).pc`

i.e. the next row's pc equals row `i`'s pushed next-PC mux. This is exactly the
cross-row PC handshake the #100 capability needs.

## The PC chain's emission shape (Main/Constraints.lean:459-460)

Per Main row `i`, the `PcContChannel` emits

  * pull  `(pc_i, main_step_i)`              (`pcPrevMessageExpr`, mult -1)
  * push  `(nextpc_i, main_step_i + 1)`      (`pcLastMessageExpr`, mult +1)

with `main_step` consecutive (`SegmentStep.main_step_consecutive`:
`main_step_{i+1} = main_step_i + 1`).

## THE STRUCTURAL DIFFERENCE FROM #103 (honest)

The #103 Mem chain GATES the last segment's push (`1 - is_last_segment`), so a
single tag-0 boot push closes the whole chain (`bootChainN`). The Main PC chain
as ACTUALLY emitted (`Main/Constraints.lean:459-460`) is UNGATED — `emit (-1)` /
`emit 1` are constant. An ungated open chain does NOT balance: row 0's pull (tag
`main_step_0`) has no matching push and the last row's push (tag
`main_step_{N-1}+1`) has no matching pull. So to model the REAL emission as a
balanced list we must supply BOTH endpoints (a boot push at the first tag and a
final pull at the last tag) — the verifier endpoints. We model that here as
`pcChainN`: a boot push + N (pull, push) pairs + a final pull, all on the same
PcMessage channel.

This file derives the seam from `pcChainN` balance and instantiates it
NON-VACUOUSLY on a concrete N = 3 chain (interior-row seams fire).

## Trust note

No PROJECT (`ZiskFv.*`) axioms. The whole derivation reuses the kernel-only
`SeamTagChain` weighted-balance machinery. `#print axioms` at the bottom.
-/

set_option linter.unnecessarySimpa false

namespace ZiskFv.Compliance.GapC.PcSeam

open Goldilocks
open ZiskFv.Channels.SeamTagChain
open ZiskFv.Channels.PcContinuation (PcMessage)

/-! ## A 2-slot PC message `[pc, tag]` over the seam-channel infrastructure.

We reuse `SeamTagChain`'s `pullMsg5` / `pushMsg5` / `seam5` machinery but only
populate the value lane 0 (= pc) and the tag (lane 4); lanes 1..3 are 0. This
lets us reuse `tagW`, `seam5_tag_ne`, `weightedSum_*`, and `exists_push_of_pull`
verbatim, with no new array friction. -/

/-- A PC message as a `seam5` 5-tuple: pc in lane 0, tag in lane 4, rest 0. -/
@[reducible] def pcMsg (pc tag : FGL) : Array FGL := seam5 pc 0 0 0 tag

theorem pcMsg_size (pc tag : FGL) : (pcMsg pc tag).size = 5 := rfl

@[simp] theorem tagW_pcMsg (pc tag : FGL) : tagW (pcMsg pc tag) = tag := rfl

/-- The pc lane of a PC message (lane 0). -/
@[simp] theorem pcMsg_lane0 (pc tag : FGL) : (pcMsg pc tag).getD 0 0 = pc := rfl

/-- `pcMsg` is injective: equal messages give equal pc and tag. -/
theorem pcMsg_inj {pc tag pc' tag' : FGL} (h : pcMsg pc tag = pcMsg pc' tag') :
    pc = pc' ∧ tag = tag' := by
  refine ⟨?_, ?_⟩
  · have := congrArg (·.getD 0 0) h; simpa [pcMsg, seam5] using this
  · have := congrArg (·.getD 4 0) h; simpa [pcMsg, seam5] using this

/-! ## The general-N PC chain.

Mirrors `bootChainN`, but with BOTH endpoints supplied (the Main emission is
ungated, so the chain is closed by a boot push at the head and a final pull at
the tail — both verifier endpoints):

  boot:          push (bootPc, t_boot)                       [endpoint]
  row i:         pull (pc i, tag i),  push (nextpc i, tag i + 1)
  final:         pull (finalPc, t_final)                     [endpoint]

`pc i` / `nextpc i` are the FREE incoming pc / pushed next-pc of row `i`; `tag i`
its FREE pull-tag. -/

/-- The two interactions contributed by Main row `i`: its pull at tag `tag i`
    (carrying `pc i`) and its push at tag `tag i + 1` (carrying `nextpc i`). -/
def rowPair (pc nextpc : ℕ → FGL) (tag : ℕ → FGL) (i : ℕ) : List (Interaction FGL) :=
  [ pullMsg5 (pcMsg (pc i) (tag i)) (pcMsg_size ..)
  , pushMsg5 (pcMsg (nextpc i) (tag i + 1)) (pcMsg_size ..) ]

/-- The general-N PC chain: a boot push (head endpoint) + every row's pull+push +
    a final pull (tail endpoint). -/
def pcChainN (N : ℕ) (bootPc tBoot finalPc tFinal : FGL)
    (pc nextpc : ℕ → FGL) (tag : ℕ → FGL) : List (Interaction FGL) :=
  pushMsg5 (pcMsg bootPc tBoot) (pcMsg_size ..) ::
    ((List.range N).flatMap (rowPair pc nextpc tag)
      ++ [ pullMsg5 (pcMsg finalPc tFinal) (pcMsg_size ..) ])

/-- Row `i`'s pull is a member of the PC chain (for `i < N`). -/
theorem rowPull_mem (N : ℕ) (bootPc tBoot finalPc tFinal : FGL)
    (pc nextpc : ℕ → FGL) (tag : ℕ → FGL) {i : ℕ} (hi : i < N) :
    pullMsg5 (pcMsg (pc i) (tag i)) (pcMsg_size ..)
      ∈ pcChainN N bootPc tBoot finalPc tFinal pc nextpc tag := by
  refine List.mem_cons.mpr (Or.inr ?_)
  rw [List.mem_append]
  refine Or.inl ?_
  rw [List.mem_flatMap]
  exact ⟨i, List.mem_range.mpr hi, by simp [rowPair]⟩

/-- Classification of the pushes (non-`-1` multiplicity members) of the PC chain.
    Any such `b` is EITHER the boot push (tag `tBoot`, value `bootPc`) OR some
    row `j`'s push (tag `tag j + 1`, value `nextpc j`). The pulls (mult `-1`,
    including the final pull) are excluded by `hb1`. -/
theorem pcPush_classify (N : ℕ) (bootPc tBoot finalPc tFinal : FGL)
    (pc nextpc : ℕ → FGL) (tag : ℕ → FGL)
    {b : Interaction FGL} (hb_mem : b ∈ pcChainN N bootPc tBoot finalPc tFinal pc nextpc tag)
    (hb1 : b.mult ≠ -1) :
    (b.msg = pcMsg bootPc tBoot)
    ∨ (∃ j, j < N ∧ b.msg = pcMsg (nextpc j) (tag j + 1)) := by
  rw [pcChainN, List.mem_cons] at hb_mem
  rcases hb_mem with hboot | hrest
  · exact Or.inl (by rw [hboot, pushMsg5])
  · rw [List.mem_append] at hrest
    rcases hrest with hseg | hfinal
    · rw [List.mem_flatMap] at hseg
      obtain ⟨j, hj_range, hj_mem⟩ := hseg
      rw [List.mem_range] at hj_range
      simp only [rowPair, List.mem_cons, List.not_mem_nil, or_false] at hj_mem
      rcases hj_mem with hpull | hpush
      · exact absurd (by rw [hpull, pullMsg5]) hb1
      · exact Or.inr ⟨j, hj_range, by rw [hpush, pushMsg5]⟩
    · -- the final pull has mult -1, excluded
      simp only [List.mem_singleton] at hfinal
      exact absurd (by rw [hfinal, pullMsg5]) hb1

/-! ### THE GENERAL-N PER-ROW PC SEAM (the channel-level deliverable). -/

/-- **THE GENERAL-N PER-ROW PC SEAM.** For every row `i < N`, from channel
    balance alone (the boot push a verifier endpoint, NOT a caller premise) and
    the `+1` emission, row `i`'s incoming pc `pc i` is continued by a matched
    push:

      * either `tag i = tBoot` and `pc i = bootPc`        (row `i` pulls the boot), OR
      * `∃ j < N` with `tag i = tag j + 1` and `pc i = nextpc j`
        (THE SEAM: row `i`'s incoming pc = row `j`'s pushed next-pc). -/
theorem pcChainN_seam (N : ℕ) (bootPc tBoot finalPc tFinal : FGL)
    (pc nextpc : ℕ → FGL) (tag : ℕ → FGL)
    (balance : BalancedInteractions (pcChainN N bootPc tBoot finalPc tFinal pc nextpc tag))
    {i : ℕ} (hi : i < N) :
    (tag i = tBoot ∧ pc i = bootPc)
    ∨ (∃ j, j < N ∧ tag i = tag j + 1 ∧ pc i = nextpc j) := by
  obtain ⟨b, hb_mem, hb_msg, hb1, _hb0⟩ :=
    exists_push_of_pull _ balance _ (rowPull_mem N bootPc tBoot finalPc tFinal pc nextpc tag hi) rfl
  simp only [pullMsg5] at hb_msg
  -- hb_msg : b.msg = pcMsg (pc i) (tag i)
  rcases pcPush_classify N bootPc tBoot finalPc tFinal pc nextpc tag hb_mem hb1 with hboot | ⟨j, hj, hjmsg⟩
  · left
    have hmsg : pcMsg (pc i) (tag i) = pcMsg bootPc tBoot := hb_msg ▸ hboot
    obtain ⟨hpc, htag⟩ := pcMsg_inj hmsg
    exact ⟨htag, hpc⟩
  · right
    have hmsg : pcMsg (pc i) (tag i) = pcMsg (nextpc j) (tag j + 1) := hb_msg ▸ hjmsg
    obtain ⟨hpc, htag⟩ := pcMsg_inj hmsg
    exact ⟨j, hj, htag, hpc⟩

/-! ### Consecutive tags collapse the seam to PHYSICAL adjacency.

`pcChainN_seam` is tag-indexed: row `i`'s incoming pc is matched to SOME row `j`'s
pushed next-pc, with `tag i = tag j + 1`. The Main `main_step` column is
CONSECUTIVE within a segment (`SegmentStep.main_step_consecutive`:
`tag (k+1) = tag k + 1`), so `tag k = tag 0 + k` for all `k`. Combined with the
tags being DISTINCT as field elements over a range `< ringChar FGL`, the matched
`j` is forced to be `i - 1`, giving the physical-adjacency seam

  `pc i = nextpc (i - 1)`,   i.e.   `pc (i+1) = nextpc i`.

The chain head (row 0) matches the boot instead (`tag 0 = tBoot`). -/

/-- With consecutive tags `tag k = tag 0 + (k : FGL)`. -/
def tagsConsecutive (tag : ℕ → FGL) : Prop := ∀ k : ℕ, tag k = tag 0 + (k : FGL)

/-- `main_step_consecutive` (the PIL fixed-column fact) gives `tagsConsecutive`. -/
theorem tagsConsecutive_of_main_step_consecutive (tag : ℕ → FGL)
    (h : ∀ i : ℕ, tag (i + 1) = tag i + 1) : tagsConsecutive tag := by
  intro k
  induction k with
  | zero => simp
  | succ n ih => rw [h n, ih]; push_cast; ring

/-- `Nat.cast` is injective on `[0, GL_prime)` in `FGL`. The chain rows index a
    range below the Goldilocks prime, so consecutive row tags `tag 0 + a` are
    pairwise distinct as field elements. -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < GL_prime) (hb : b < GL_prime)
    (h : (a : FGL) = (b : FGL)) : a = b := by
  haveI hcp : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · have : ((b - a : ℕ) : FGL) = 0 := by
      have : ((b : ℕ) : FGL) - ((a : ℕ) : FGL) = 0 := by rw [h]; ring
      rwa [Nat.cast_sub (le_of_lt hlt)]
    rw [CharP.cast_eq_zero_iff FGL GL_prime] at this
    omega
  · have hba : b < a := by omega
    have : ((a - b : ℕ) : FGL) = 0 := by
      have : ((a : ℕ) : FGL) - ((b : ℕ) : FGL) = 0 := by rw [h]; ring
      rwa [Nat.cast_sub (le_of_lt hba)]
    rw [CharP.cast_eq_zero_iff FGL GL_prime] at this
    omega

/-- Distinctness of consecutive tags over a range below `GL_prime`. -/
theorem tag_inj_of_lt {tag : ℕ → FGL} (hc : tagsConsecutive tag) {a b : ℕ}
    (hab : a ≠ b) (ha : a < GL_prime) (hb : b < GL_prime) :
    tag a ≠ tag b := by
  rw [hc a, hc b]
  intro h
  exact hab (natCast_inj_of_lt ha hb (add_left_cancel h))

/-- Equality of consecutive tags below `GL_prime` collapses the index relation:
    `tag i = tag j + 1` with `tag k = tag 0 + k` and `i, j+1 < GL_prime` forces
    `i = j + 1`. -/
theorem tag_step_collapse {tag : ℕ → FGL} (hc : tagsConsecutive tag) {i j : ℕ}
    (htag : tag i = tag j + 1) (hi : i < GL_prime) (hj1 : j + 1 < GL_prime) :
    i = j + 1 := by
  have h : tag i = tag (j + 1) := by rw [htag, hc (j + 1), hc j]; push_cast; ring
  rw [hc i, hc (j + 1)] at h
  exact natCast_inj_of_lt hi hj1 (add_left_cancel h)

/-! ### THE PHYSICAL-ADJACENCY PC SEAM (the `pc_seam_of_balanced` deliverable). -/

/-- **`pc_seam_of_balanced` — THE PC SEAM AS A THEOREM.** From channel balance on
    the Main PC chain (the verifier boot/final endpoints are MEMBERS of the
    balanced list, NOT caller premises) plus `main_step` consecutiveness
    (`SegmentStep.main_step_consecutive`, the PIL `SEGMENT_STEP` fixed column),
    every INTERIOR row pair satisfies the cross-row PC handshake:

      `pc (i+1) = nextpc i`     for `i + 1 < N`,

    i.e. the next row's incoming pc equals row `i`'s pushed next-PC mux. This is
    DERIVED from balance — `pc i` / `nextpc i` / `tag i` are all genuinely free,
    and only the matched continuation is forced. (Row 0 instead matches the boot;
    the last row's push matches the final pull.) -/
theorem pc_seam_of_balanced (N : ℕ) (bootPc tBoot finalPc tFinal : FGL)
    (pc nextpc : ℕ → FGL) (tag : ℕ → FGL)
    (balance : BalancedInteractions (pcChainN N bootPc tBoot finalPc tFinal pc nextpc tag))
    (hc : tagsConsecutive tag)
    (hlen : N < GL_prime)
    -- the boot tag does NOT collide with any in-range row tag (the boot is the
    -- head endpoint; pinning its tag below row 0's tag, e.g. tBoot = tag 0, keeps
    -- the interior matches unambiguous). The faithful instance has tBoot = tag 0.
    (hboot_tag : tBoot = tag 0)
    {i : ℕ} (hi1 : i + 1 < N) :
    pc (i + 1) = nextpc i := by
  rcases pcChainN_seam N bootPc tBoot finalPc tFinal pc nextpc tag balance
      (i := i + 1) hi1 with ⟨htag, _hpc⟩ | ⟨j, hj, htag, hpc⟩
  · -- row (i+1) cannot match the boot: tag (i+1) = tBoot = tag 0 forces i+1 = 0
    exfalso
    rw [hboot_tag] at htag
    have hne := tag_inj_of_lt hc (a := i + 1) (b := 0) (by omega) (by omega) (by omega)
    exact hne htag
  · -- the seam disjunct: tag (i+1) = tag j + 1 forces j = i, so pc (i+1) = nextpc i
    have hji : i + 1 = j + 1 :=
      tag_step_collapse hc htag (by omega) (by omega)
    have hij : j = i := by omega
    rw [hij] at hpc; exact hpc

/-! ### NON-VACUITY at N = 3 (interior-row seams fire on a REAL multi-row chain).

`pc_seam_of_balanced` is `∀`-quantified over a `BalancedInteractions` antecedent;
a green `Balance → …` theorem is worthless if `Balance` is unsatisfiable. We
exhibit a CONCRETE BALANCED N = 3 PC chain — 3 sequential rows `pc = 4096, 4100,
4104` (`nextpc i = pc i + 4`), tags `0, 1, 2`, boot push (pc 4096, tag 0), final
pull (pc 4108, tag 3) — and run `pc_seam_of_balanced` on each INTERIOR row,
confirming the cross-row seam `pc (i+1) = nextpc i` fires for `i = 0, 1`. This is
the exact non-vacuity trap #103's per-row-on-segment chain hit; for #100 the chain
links ARE the Main rows (one pull + one push per row, consecutive tags), so a real
multi-ROW chain balances and the interior seam fires — NOT a 1-row degenerate. -/

/-- The concrete N = 3 sequential pc column: `4096, 4100, 4104`. -/
def pc3 : ℕ → FGL
  | 0 => 4096
  | 1 => 4100
  | 2 => 4104
  | _ => 0

/-- The concrete N = 3 pushed next-pc: `nextpc i = pc i + 4`. -/
def nextpc3 : ℕ → FGL
  | 0 => 4100
  | 1 => 4104
  | 2 => 4108
  | _ => 0

/-- The concrete N = 3 tags: `tag3 k = (k : FGL)` — the genuine `SEGMENT_STEP`
    `[0,1,2,…]` fixed-column shape (`SegmentStep.fixedSegmentStep`), so it is
    consecutive for ALL `k` (not just the live range). -/
def tag3 : ℕ → FGL := fun k => (k : FGL)

/-- The concrete N = 3 PC chain (8 interactions): boot push (tag 0) + 3 rows
    (pull + push) + final pull (tag 3). -/
def goodPcChain3 : List (Interaction FGL) :=
  pcChainN 3 4096 0 4108 3 pc3 nextpc3 tag3

/-- The concrete N = 3 chain reduces to its explicit 8-interaction cons-list:
    boot push, seg0/1/2 pull+push, final pull. -/
theorem goodPcChain3_eq :
    goodPcChain3 =
      [ pushMsg5 (pcMsg 4096 0) (pcMsg_size ..)   -- boot push, tag 0
      , pullMsg5 (pcMsg 4096 0) (pcMsg_size ..)   -- row0 pull, tag 0
      , pushMsg5 (pcMsg 4100 1) (pcMsg_size ..)   -- row0 push, tag 1
      , pullMsg5 (pcMsg 4100 1) (pcMsg_size ..)   -- row1 pull, tag 1
      , pushMsg5 (pcMsg 4104 2) (pcMsg_size ..)   -- row1 push, tag 2
      , pullMsg5 (pcMsg 4104 2) (pcMsg_size ..)   -- row2 pull, tag 2
      , pushMsg5 (pcMsg 4108 3) (pcMsg_size ..)   -- row2 push, tag 3
      , pullMsg5 (pcMsg 4108 3) (pcMsg_size ..) ] := by -- final pull, tag 3
  simp only [goodPcChain3, pcChainN, show (3 : ℕ) = 2 + 1 from rfl,
    List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, rowPair, pc3, nextpc3, tag3]
  norm_num [pcMsg, seam5]

/-- The concrete N = 3 PC chain IS balanced: the four live messages
    `(4096,0)`, `(4100,1)`, `(4104,2)`, `(4108,3)` each have exactly one pull
    (-1) and one push (+1). NON-VACUOUS positive witness at N = 3 (a real
    multi-ROW chain, not a 1-row degenerate). -/
theorem goodPcChain3_balanced : BalancedInteractions goodPcChain3 := by
  refine ⟨Or.inl ?_, ?_⟩
  · rw [goodPcChain3_eq]
    show ([_, _, _, _, _, _, _, _] : List _).length < ringChar FGL
    haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
    rw [ringChar.eq FGL GL_prime]; norm_num
  · intro msg
    rw [goodPcChain3_eq]
    unfold balanceOf pullMsg5 pushMsg5 pcMsg seam5
    have d01 : (#[4096,0,0,0,0] : Array FGL) ≠ #[4100,0,0,0,1] := by decide
    have d02 : (#[4096,0,0,0,0] : Array FGL) ≠ #[4104,0,0,0,2] := by decide
    have d03 : (#[4096,0,0,0,0] : Array FGL) ≠ #[4108,0,0,0,3] := by decide
    have d12 : (#[4100,0,0,0,1] : Array FGL) ≠ #[4104,0,0,0,2] := by decide
    have d13 : (#[4100,0,0,0,1] : Array FGL) ≠ #[4108,0,0,0,3] := by decide
    have d23 : (#[4104,0,0,0,2] : Array FGL) ≠ #[4108,0,0,0,3] := by decide
    by_cases h0 : (#[4096,0,0,0,0] : Array FGL) = msg <;>
    by_cases h1 : (#[4100,0,0,0,1] : Array FGL) = msg <;>
    by_cases h2 : (#[4104,0,0,0,2] : Array FGL) = msg <;>
    by_cases h3 : (#[4108,0,0,0,3] : Array FGL) = msg <;>
      simp_all [List.filter, List.sum]

/-- `tag3` is consecutive for ALL `k` (it is the `(k : FGL)` cast). -/
theorem tag3_consecutive : tagsConsecutive tag3 := by
  intro k; simp [tag3]

/-- **NON-VACUITY END-TO-END.** Running `pc_seam_of_balanced` on the concrete
    balanced N = 3 chain: the INTERIOR cross-row seams fire —
    `pc3 1 = nextpc3 0` (`4100 = 4100`) and `pc3 2 = nextpc3 1` (`4104 = 4104`).
    This certifies `pc_seam_of_balanced` is satisfied non-vacuously on a real
    multi-ROW chain (N = 3), interior rows included — NOT the 1-row degenerate
    case. -/
theorem goodPcChain3_seams :
    pc3 1 = nextpc3 0 ∧ pc3 2 = nextpc3 1 := by
  -- tag3 is consecutive only over the live range; restrict via a patched version.
  refine ⟨?_, ?_⟩
  · exact pc_seam_of_balanced 3 4096 0 4108 3 pc3 nextpc3 tag3
      goodPcChain3_balanced tag3_consecutive (by norm_num) (by norm_num [tag3])
      (i := 0) (by norm_num)
  · exact pc_seam_of_balanced 3 4096 0 4108 3 pc3 nextpc3 tag3
      goodPcChain3_balanced tag3_consecutive (by norm_num) (by norm_num [tag3])
      (i := 1) (by norm_num)

/-- The interior seam values evaluated concretely: `pc3 1 = 4100` (the genuine
    `nextpc3 0 = pc3 0 + 4`). Confirms the seam carries the REAL next-PC. -/
theorem goodPcChain3_seam_values : pc3 1 = (4100 : FGL) ∧ nextpc3 0 = (4100 : FGL) := by
  refine ⟨?_, ?_⟩ <;> decide

end ZiskFv.Compliance.GapC.PcSeam

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom, NO
`native_decide`. The PC seam is DERIVED from channel balance, NON-VACUOUSLY
satisfied by a concrete N = 3 multi-row chain (interior seams fire). -/
#print axioms ZiskFv.Compliance.GapC.PcSeam.pcChainN_seam
#print axioms ZiskFv.Compliance.GapC.PcSeam.pc_seam_of_balanced
#print axioms ZiskFv.Compliance.GapC.PcSeam.goodPcChain3_balanced
#print axioms ZiskFv.Compliance.GapC.PcSeam.goodPcChain3_seams
#print axioms ZiskFv.Compliance.GapC.PcSeam.goodPcChain3_seam_values
