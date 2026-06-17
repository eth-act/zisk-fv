import ZiskFv.Channels.SeamTagChain

/-!
# PR-X100.0 — channel-level probe for the cross-row Main PC handshake (XCAP #100)

This file is a make-or-break proof-of-concept for XCAP #100 (cross-row Main PC
handshake). The question it answers:

  Can the cross-row PC handshake `pc(row i+1) = pc(row i) + 4` be FORCED by
  channel balance, by REUSING the channel-agnostic seam engine
  `SeamTagChain.boot_chain_derived` — interpreting the seam's value lanes as PC?

It mirrors `ZiskFv/AirsClean/FullEnsemble/SeamNonVacuity.lean` (which certifies
the Mem seam on the real ensemble), but for PC and at the channel level only.

## What is proved

1. `pc_handshake_forced` (GENERIC): from `BalancedInteractions (bootList2 ...)`
   AND a row-local next-PC pin `h_pin : l0v0 = p0v0 + 4` (seg0's last-pc =
   seg0's pc + 4 — the sequential `constraint_18` specialization, here a
   HYPOTHESIS), the seam forced by balance gives seg1's pc = seg0's pc + 4
   (`p1v0 = p0v0 + 4`). The PC is carried in the `v0` value lane of the seam.

2. `pc_handshake_nonvacuous` (CONCRETE NON-VACUITY): a concrete balanced witness
   `pcBootList2` (PROVEN balanced, not assumed — `pcBootList2_balanced`) encoding
   pc0 = 0, nextpc = 4. Running theorem 1 on it certifies the derivation FIRES on
   a real balanced instance: pc0 = 0 ⟹ pc1 = 4, i.e. `(4 : FGL) = 0 + 4`.

## Scope / honesty note

The next-PC pin `l0v0 = p0v0 + 4` is a HYPOTHESIS here (channel-level PoC). It is
the sequential `constraint_18` specialization; DISCHARGING it from the real Main
AIR's row constraints is the SEPARATE SPINE-#2 work. What this probe establishes
is the CHANNEL half: balance + the pin ⟹ the cross-row +4 handshake, with a
concrete non-vacuous witness, kernel-only (0 `ZiskFv.*` axioms).

## Trust note

No axioms. The concrete witness's `BalancedInteractions` is PROVEN, mirroring
`SeamTagChain.goodBootList2_balanced`; see the `#print axioms` check at the end.
-/

namespace ZiskFv.Spike.PcHandshakeProbe

open Goldilocks
open ZiskFv.Channels.SeamTagChain

/-! ## Theorem 1 — the generic PC-handshake derivation.

We reuse the channel-agnostic boot-chain engine `boot_chain_derived` verbatim,
reading the seam's `v0` value lane as the program counter. Balance forces the
value seam `seg1.prev = seg0.last` (the 4th conjunct of `boot_chain_derived`);
the row-local pin `seg0.last_pc = seg0.pc + 4` then propagates the +4 across the
cross-row handshake. -/

/-- Extract the `v0` (PC) lane from a `seam5` equality. `seam5` carries the full
    4-lane value plus the tag, so equal messages give equal lanes. -/
theorem seam5_v0_eq {v0 v1 a s t v0' v1' a' s' t' : FGL}
    (h : seam5 v0 v1 a s t = seam5 v0' v1' a' s' t') : v0 = v0' := by
  have := congrArg (·[0]!) h
  simpa [seam5] using this

/-- **THE PC HANDSHAKE, forced by channel balance.** With the seam's `v0` lane
    interpreted as the program counter:

      * `p0v0` = seg0's PC (the PC pulled in at row i),
      * `l0v0` = seg0's last-PC (the PC pushed out of row i),
      * `p1v0` = seg1's PC (the PC pulled in at row i+1),

    channel balance forces the cross-row value seam `seg1.prev = seg0.last`
    (`boot_chain_derived`'s 4th conjunct), i.e. `p1v0 = l0v0`. Combined with the
    row-local next-PC pin `h_pin : l0v0 = p0v0 + 4` (the sequential
    `constraint_18` specialization, a HYPOTHESIS here), this yields the cross-row
    handshake `p1v0 = p0v0 + 4`: the PC pulled in at row i+1 equals the PC at
    row i plus 4. -/
theorem pc_handshake_forced
    (bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
     l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s : FGL)
    (balance : BalancedInteractions
      (bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
        l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s 0))
    (h_pin : l0v0 = p0v0 + 4) :
    p1v0 = p0v0 + 4 := by
  -- Balance forces the value seam: seg1.prev = seg0.last (the 4th conjunct).
  obtain ⟨_ht0, _ht1, _hseam0, hseam⟩ := boot_chain_derived
    bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
    l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s balance
  -- hseam : seam5 p1v0 .. t1 = seam5 l0v0 .. (t0 + 1).  Extract the PC (v0) lane.
  have hpc : p1v0 = l0v0 := seam5_v0_eq hseam
  -- Propagate the row-local +4 pin across the seam.
  rw [hpc, h_pin]

/-! ## Theorem 2 — a CONCRETE, PROVEN-balanced non-vacuity witness.

We instantiate `bootList2` with PC-flavoured literals encoding pc0 = 0 and
nextpc = 4: the `v0` lane carries the PC. The three distinct messages are

  * boot     `(0,0,335544320,0,0)`   — boot PC 0, tag 0,
  * seg0.last/seg1.prev `(4,0,100,5,1)` — next-PC 4 (THE SEAM), tag 1,
  * seg1.last (gated off) `(8,0,200,9,2)` — tag 2, multiplicity 0.

`seg1.prev` equals `seg0.last` on ALL lanes (required for balance), and seg1's
push is gated off (`g1 = 0`). The balance proof mirrors
`SeamTagChain.goodBootList2_balanced` literally; only the literals differ. -/

/-- The concrete PC-flavoured boot chain: boot PC `0` at tag 0; seg0 pulls boot,
    pushes next-PC `4` (with the other lanes `(0,100,5)`) at tag 1; seg1 pulls
    that `(4,0,100,5)` (THE SEAM) at tag 1, is the LAST segment so its push
    `(8,0,200,9)` at tag 2 is GATED OFF (`g1 = 0`). The `v0` lane is the PC:
    `pc0 = 0`, `nextpc = 4`. -/
def pcBootList2 : List (Interaction FGL) :=
  bootList2
    0 0 335544320 0                 -- boot value: PC 0, tag 0
    0 0 335544320 0 0               -- seg0.prev = boot (PC 0), tag t0 = 0
    4 0 100 5                        -- seg0.last: next-PC 4, pushed tag t0+1 = 1
    4 0 100 5 1                      -- seg1.prev = seg0.last (PC 4, SEAM), tag t1 = 1
    8 0 200 9 0                      -- seg1.last (gated off, g1 = 0), would-be tag 2

/-- THE NON-VACUITY CERTIFICATE: the concrete PC chain IS balanced. Each of the
    three distinct messages `(0,0,335544320,0,0)`, `(4,0,100,5,1)`,
    `(8,0,200,9,2)` has one matching pull (-1) and one push (+1); the gated-off
    seg1 push contributes multiplicity 0. PROVEN, not assumed — mirrors
    `SeamTagChain.goodBootList2_balanced`. -/
theorem pcBootList2_balanced : BalancedInteractions pcBootList2 := by
  refine ⟨Or.inl ?_, ?_⟩
  · show ([_, _, _, _, _] : List _).length < ringChar FGL
    have : (5 : ℕ) < ringChar FGL := by
      haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
      rw [ringChar.eq FGL GL_prime]; norm_num
    simpa using this
  · intro msg
    unfold pcBootList2 bootList2 balanceOf pullMsg5 pushMsg5 gatedMsg5 seam5
    have d01 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[4,0,100,5,1] := by decide
    have d02 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[8,0,200,9,2] := by decide
    have d12 : (#[4,0,100,5,1] : Array FGL) ≠ #[8,0,200,9,2] := by decide
    by_cases h0 : (#[0,0,335544320,0,0] : Array FGL) = msg <;>
    by_cases h1 : (#[4,0,100,5,1] : Array FGL) = msg <;>
    by_cases h2 : (#[8,0,200,9,2] : Array FGL) = msg <;>
      simp_all [List.filter, List.sum]

/-- **PC HANDSHAKE, NON-VACUOUS.** Running `pc_handshake_forced` on the concrete
    PROVEN-balanced witness `pcBootList2` (so its `BalancedInteractions`
    antecedent is genuinely satisfied) with the concrete next-PC pin
    `(4 : FGL) = 0 + 4` certifies the derivation FIRES on a real balanced
    instance: pc0 = 0 ⟹ pc1 = 4. This confirms `pc_handshake_forced` is NOT
    vacuous — balance is satisfiable by a concrete inhabitant. -/
theorem pc_handshake_nonvacuous : (4 : FGL) = 0 + 4 :=
  pc_handshake_forced
    0 0 335544320 0 0 0 335544320 0 0 4 0 100 5 4 0 100 5 1 8 0 200 9
    pcBootList2_balanced
    (by ring)

end ZiskFv.Spike.PcHandshakeProbe

/-! ## Axiom-closure check.

`#print axioms` must return only Lean-kernel axioms (`propext`,
`Classical.choice`, `Quot.sound`): 0 PROJECT (`ZiskFv.*`) axioms, NO `sorry`.
The PC handshake derivation + its concrete non-vacuity witness are kernel-only. -/
#print axioms ZiskFv.Spike.PcHandshakeProbe.pc_handshake_forced
#print axioms ZiskFv.Spike.PcHandshakeProbe.pc_handshake_nonvacuous
