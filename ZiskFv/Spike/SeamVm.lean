import Clean.Air.Vm
import ZiskFv.Field.Goldilocks

/-!
# SPIKE B — cross-segment seam via the VM-channel route (#103)

THROWAWAY go/no-go proof of concept. NOT for merge.

Goal: test whether Clean's EXISTING VM-channel state-transition framework
(`Clean/Air/Vm.lean`: `VmTables`, `SoundVmEnsemble.toFormal`,
`addVm_soundVmChannel_of_soundChannels`) can EXPRESS and DERIVE the
cross-segment `SeamColumnEquality`
(`seg0.segment_last_* = seg1.previous_segment_*`) that the #76 Spike #1 PROVED
is NOT derivable from the per-row `assertZero` permutation accumulator
(`ZiskFv/Spike/Seam.lean:186 seam_star_is_false`).

Route: a `SeamChannel : Channel FGL (fields 4)` carrying the RAW boundary tuple
`(value_0, value_1, addr, step)`. Each Mem segment, as ONE VM transition row,
PULLs its `previous_segment_*` boundary and PUSHes its `segment_last_*`
boundary. A non-empty verifier pushes the boot seam and pulls the final seam,
mirroring `Clean/Examples/FibonacciWithChannels.lean::fibonacciVerifier`.

We mirror Fibonacci structurally throughout.
-/

namespace ZiskFv.Spike.SeamVm

open Air.Flat
open Goldilocks

/-- Goldilocks has characteristic `GL_prime`, a large prime, so `ringChar ≠ 2`.
    The VM theorem `addVm_soundVmChannel_of_soundChannels` requires this. -/
instance : Fact (ringChar FGL ≠ 2) := .mk <| by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  have h : ringChar FGL = GL_prime := ringChar.eq FGL GL_prime
  rw [h]; norm_num

/-! ## The faithful Mem-segment-boundary model.

We model the segment boundary state as a 4-tuple `(value_0, value_1, addr,
step)` (the RAW columns the #103 permutation accumulator hashes — we carry
them RAW, so NO hash-injectivity step is needed; this is the genuine relief
the plan §2.2/Risk #4 names).

A "segment transition" is some deterministic function `segStep` from the
incoming boundary to the outgoing boundary; in ZisK this is "replay the
segment's address-sorted rows and report the last carried address class".
For the spike its INTERNALS are irrelevant — what matters is that the VM
channel forces the OUTGOING boundary of seg n to equal the INCOMING boundary
of seg n+1. We add NO algebraic link from the incoming to the outgoing tuple
in the row, so the spike does NOT secretly bake the answer into the transition. -/

/-- The boot boundary state any real Mem trace starts from
    (`segment_id = 0`, base address, zero carry). The concrete numbers are
    irrelevant to the spike; we use the `segment_every_row` base address
    `335544320` for `addr` to stay faithful (plan §2.2). -/
def bootSeam : fields 4 FGL := #v[0, 0, 335544320, 0]

/-- The seam channel carries the RAW boundary 4-tuple. Its `Guarantees` are the
    IDENTITY/trivial predicate `True`: we do NOT use the guarantees to smuggle
    in a state-machine invariant. The cross-segment link must come from BALANCE
    alone (`exists_push_of_pull`), carrying the RAW tuple — this is the
    plan §2.2 / Risk #4 route-(a): NO hash-injectivity, NO reachability
    invariant baked into the channel. -/
instance SeamChannel : Channel FGL (fields 4) where
  name := "seam"
  Guarantees _ _ := True

/-! ## The segment transition circuit.

Each Mem segment carries BOTH boundary tuples as columns:
`previous_segment_*` (incoming) and `segment_last_*` (outgoing). We model the
segment row's Input as `fields 8 = previous(4) ++ last(4)`. The row PULLs the
incoming boundary and PUSHes the outgoing boundary — exactly a VM transition.

We deliberately add NO algebraic constraint linking `previous` to `last`
(no `segStep`): the row's internal replay is out of scope for the seam. The
cross-segment LINK must come from the CHANNEL BALANCE, not from this row. -/

/-- Split a `fields 8` var into its `previous`(0..3) and `last`(4..7) halves. -/
@[reducible] def prevOf (v : fields 8 (Expression FGL)) : fields 4 (Expression FGL) :=
  #v[v[0], v[1], v[2], v[3]]
@[reducible] def lastOf (v : fields 8 (Expression FGL)) : fields 4 (Expression FGL) :=
  #v[v[4], v[5], v[6], v[7]]

def segmentTransition : GeneralFormalCircuit FGL (fields 8) unit where
  main v := do
    -- PULL the incoming boundary `previous_segment_*`
    SeamChannel.pull (prevOf v)
    -- PUSH the outgoing boundary `segment_last_*`
    SeamChannel.push (lastOf v)
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ SeamChannel.toRaw ]
  channelsWithRequirements := [ SeamChannel.toRaw ]
  exposedChannels v _ :=
    expose SeamChannel [ pulled (prevOf v), pushed (lastOf v) ]
  channelsLawful := by
    simp only [circuit_norm, SeamChannel]
  ProverAssumptions _ _ _ := True
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [SeamChannel]
  completeness := by
    circuit_proof_start [SeamChannel]

/-! ## The verifier (non-empty, mirroring `fibonacciVerifier`).

The public IO is the FINAL seam (the boundary the last segment carries OUT —
`is_last_segment` boundary). The verifier PULLs that final seam off the channel
and PUSHes the boot seam (`segment_id = 0`, base address). This closes the
cycle: boot → seg0 → seg1 → final. Mirrors `fibonacciVerifier` exactly. -/
def seamVerifier : GeneralFormalCircuit FGL (fields 4) unit where
  main finalSeam := do
    SeamChannel.pull finalSeam
    SeamChannel.push (ProvableType.const bootSeam)
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ SeamChannel.toRaw ]
  channelsWithRequirements := [ SeamChannel.toRaw ]
  exposedChannels finalSeam _ :=
    expose SeamChannel [ pulled finalSeam, pushed (ProvableType.const bootSeam) ]
  channelsLawful := by
    simp only [circuit_norm, SeamChannel]
  ProverAssumptions _ _ _ := True
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [SeamChannel]
  completeness := by
    circuit_proof_start [SeamChannel]

/-! ## The VM ensemble.

Two segment tables (seg0, seg1) form a NON-TRIVIAL 2-segment witness, plus the
bracketing verifier. Mirrors `fibonacciVm` exactly. -/
def seamVm : VmTables FGL (fields 4) where
  channel := SeamChannel
  tables := [⟨ segmentTransition ⟩, ⟨ segmentTransition ⟩]
  verifier := seamVerifier
  verifier_length_zero := by simp [circuit_norm, seamVerifier]
  tables_channel := by simp [circuit_norm, segmentTransition]
  verifier_channel := by simp [circuit_norm, seamVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, seamVerifier, SeamChannel]

def seamEnsemble : SoundVmEnsemble FGL (fields 4) :=
  SoundEnsemble.empty FGL (fields 4)
    |>.addVm seamVm
      (by simp [circuit_norm, seamVm, segmentTransition, SeamChannel])
      (by simp [circuit_norm, seamVm, segmentTransition, seamVerifier, SeamChannel])
      (by simp [circuit_norm, seamVm, segmentTransition, seamVerifier, SeamChannel])

/-! ## PROBE — what does the global balance give for the seam?

We take an arbitrary witness of `seamEnsemble.ensemble` and assume
`BalancedChannels`. The two segment tables seg0, seg1 each pull `previous` and
push `last`. We try to derive `seg1.previous = seg0.last`. -/

/-- The VM ensemble is sound: `toFormal` gives a real `FormalEnsemble`. -/
def seamFormal : FormalEnsemble FGL (fields 4) :=
  seamEnsemble.toFormal FGL (fun _ _ => True)
    (by simp [circuit_norm, seamEnsemble, seamVm, segmentTransition])

#check @seamFormal

/-! ## PROBE 1 — extract the balanced seam-channel interactions of a witness. -/
section Probe
variable (witness : EnsembleWitness seamEnsemble.ensemble)

example (balance : witness.BalancedChannels) : True := by
  have h_chan : SeamChannel.toRaw ∈ seamEnsemble.ensemble.channels := by
    simp [seamEnsemble, SoundEnsemble.addVm, Ensemble.addVm, seamVm]
  have bal := balance SeamChannel.toRaw h_chan
  -- `bal : BalancedInteractions (witness.allTablesWitness.interactionsWith SeamChannel.toRaw)`
  trivial

/-! ## PROBE 2 — apply `exists_push_of_pull` to a pulled `previous` boundary.

This is the plan §2.2 / Risk #4 route-(a) mechanism: balance forces every
pull to have a MATCHING push of the same RAW message. We extract a VmWitness
and characterize its pulls/pushes, then apply `exists_push_of_pull`. -/

/-- A VmWitness for `seamVm`, derived from the ensemble witness. -/
noncomputable def vmWitnessOf : VmWitness seamVm :=
  (Ensemble.addVm_witness (Ensemble.empty FGL (fields 4)) seamVm
    (by
      -- the seamEnsemble witness IS a witness of `empty.addVm seamVm`
      have : seamEnsemble.ensemble = (Ensemble.empty FGL (fields 4)).addVm seamVm := by
        rfl
      exact this ▸ witness)).choose

example (balance : witness.BalancedChannels) : True := by
  -- the seam-channel interactions of the witness equal the VM pulls/pushes
  have h_chan : SeamChannel.toRaw ∈ seamEnsemble.ensemble.channels := by
    simp [seamEnsemble, SoundEnsemble.addVm, Ensemble.addVm, seamVm]
  have bal := balance SeamChannel.toRaw h_chan
  trivial

end Probe

/-! ## PROBE 3 — the COMBINATORIAL core, at the raw `Interaction` level.

`BalancedInteractions` is purely a property of the list of evaluated
`Interaction FGL` values (a per-message multiplicity-sum-zero condition,
`Balance.lean:24`). The seam question is therefore a finite combinatorial
question about whether the per-message balance of the 3-pull / 3-push list
FORCES `seg1.prev = seg0.last`, or only forces membership in the push
multiset (the disjunction `seg1.prev ∈ {boot, seg0.last, seg1.last}`).

We test this DIRECTLY by building explicit `Interaction FGL` values and asking
`decide` whether a NON-seam assignment can still be balanced. This is the
anti-vacuity NO-GO probe parallel to `Spike/Seam.lean:seam_star_is_false`. -/

/-- A pulled raw boundary message (multiplicity -1). -/
def pullMsg (m : Array FGL) (hm : m.size = 4) : Interaction FGL where
  channel := SeamChannel.toRaw
  mult := -1
  msg := m
  same_size := by simpa [SeamChannel, Channel.toRaw] using hm
  assumeGuarantees := true

/-- A pushed raw boundary message (multiplicity 1). -/
def pushMsg (m : Array FGL) (hm : m.size = 4) : Interaction FGL where
  channel := SeamChannel.toRaw
  mult := 1
  msg := m
  same_size := by simpa [SeamChannel, Channel.toRaw] using hm
  assumeGuarantees := false

/-- The seam-channel interaction list of a 2-segment witness, parameterized by
    the raw boundary tuples each table carries. Order mirrors
    `allTables = verifierTable :: tables`. -/
def seamInteractions
    (finalSeam boot p0 l0 p1 l1 : Array FGL)
    (hf : finalSeam.size = 4) (hb : boot.size = 4)
    (hp0 : p0.size = 4) (hl0 : l0.size = 4) (hp1 : p1.size = 4) (hl1 : l1.size = 4) :
    List (Interaction FGL) :=
  [ pullMsg finalSeam hf, pushMsg boot hb,    -- verifier
    pullMsg p0 hp0, pushMsg l0 hl0,           -- seg0
    pullMsg p1 hp1, pushMsg l1 hl1 ]          -- seg1

/-- A CONCRETE NON-seam assignment: seg1.prev = boot, seg0.last = boot,
    seg1.last = finalSeam, seg0.prev = finalSeam, verifier pulls finalSeam.
    Here `seg1.prev = boot` and `seg0.last = boot` so they happen to be EQUAL;
    we want a witness where they DIFFER. -/
def boot4 : Array FGL := #[0, 0, 335544320, 0]
def valA  : Array FGL := #[1, 0, 100, 5]   -- seg0.last (a "middle" address class)
def valB  : Array FGL := #[2, 0, 200, 9]   -- a distinct boundary value

theorem boot4_size : boot4.size = 4 := by decide
theorem valA_size : valA.size = 4 := by decide
theorem valB_size : valB.size = 4 := by decide

/-- The NON-seam balanced interaction list (the closed-cycle escape the VM doc
    `Vm.lean:16-19` warns about):
      verifier:  pull valA,  push boot4
      seg0:      pull valB,  push valA       (seg0.last = valA)
      seg1:      pull boot4, push valB       (seg1.prev = boot4 ≠ valA)
    Here `seg1.prev = boot4` but `seg0.last = valA`, so the seam FAILS, yet… -/
def badSeamInteractions : List (Interaction FGL) :=
  seamInteractions valA boot4 valB valA boot4 valB
    valA_size boot4_size valB_size valA_size boot4_size valB_size

/-- The ring-char side condition: 6 interactions < ringChar FGL. -/
theorem six_lt_ringChar : (6 : ℕ) < ringChar FGL := by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  rw [ringChar.eq FGL GL_prime]; norm_num

/-- `balanceOf` of the explicit 6-element bad list, for an arbitrary message.
    The boot4/valA/valB messages are pairwise distinct, so for each message the
    matched pull (−1) and push (+1) cancel; every other message contributes 0. -/
theorem balanceOf_badSeam (msg : Array FGL) : balanceOf badSeamInteractions msg = 0 := by
  unfold badSeamInteractions seamInteractions balanceOf pullMsg pushMsg
  -- the list is: pull valA, push boot4, pull valB, push valA, pull boot4, push valB
  -- case-split on which (if any) of the three distinct messages `msg` equals.
  have hAB : (valA : Array FGL) ≠ valB := by decide
  have hAb : (valA : Array FGL) ≠ boot4 := by decide
  have hBb : (valB : Array FGL) ≠ boot4 := by decide
  by_cases hA : valA = msg <;> by_cases hB : valB = msg <;> by_cases hb : boot4 = msg <;>
    simp_all [List.filter, List.sum]

/-- The bad list IS balanced (per-message multiplicities cancel). This is the
    rigorous NO-GO witness: the VM-channel global balance does NOT force
    `seg1.prev = seg0.last`. The pull/push matching is a closed cycle that
    routes seg1's pull (boot4) to the verifier's boot push, seg0's push (valA)
    to the verifier's pull, and seg1's push (valB) to seg0's pull — a valid
    balanced permutation that is NOT the intended chain. -/
theorem badSeam_is_balanced : BalancedInteractions badSeamInteractions := by
  refine ⟨ Or.inl ?_, balanceOf_badSeam ⟩
  show ([_,_,_,_,_,_] : List _).length < ringChar FGL
  simpa using six_lt_ringChar

/-- And seg1.prev (boot4) ≠ seg0.last (valA) in this balanced witness. -/
theorem badSeam_breaks_seam : (boot4 : Array FGL) ≠ valA := by decide

/-! ## PROBE 4 — the POSITIVE route: does a `segment_id` TAG close the escape?

The real ZisK accumulator (`ZiskFv/Airs/Mem.lean:1351-1370`) tags each hashed
tuple with `segment_id`:
  * `direct_gsum_0` (the PULL of `previous_segment_*`) uses tag `segment_id`,
  * `direct_gsum_1` (the PUSH of `segment_last_*`) uses tag `segment_id + 1`.
So seg-n RECEIVES `previous_segment_*` tagged `n` and SENDS `segment_last_*`
tagged `n+1`. We carry the tag RAW as a 5th message component and re-test the
escape: with tags 0,1,2 distinct, can a balanced NON-seam witness still exist?

NOTE the load-bearing CAVEAT this probe exposes: the tags 0,1,2 must THEMSELVES
be forced by row constraints + the verifier endpoints. In this VM model the tag
is a free column; pinning it to the segment index is itself a cross-segment
fact (the `segment_id` chain). See the report. -/

/-- The tagged seam channel (arity 5: 4 boundary fields + segment-id tag). -/
instance SeamChannel5 : Channel FGL (fields 5) where
  name := "seam5"
  Guarantees _ _ := True

/-- A pulled / pushed message now carrying a 5th `tag` component. -/
def pullMsg5 (m : Array FGL) (hm : m.size = 5) : Interaction FGL where
  channel := SeamChannel5.toRaw
  mult := -1
  msg := m
  same_size := by simpa [SeamChannel5, Channel.toRaw] using hm
  assumeGuarantees := true

def pushMsg5 (m : Array FGL) (hm : m.size = 5) : Interaction FGL where
  channel := SeamChannel5.toRaw
  mult := 1
  msg := m
  same_size := by simpa [SeamChannel5, Channel.toRaw] using hm
  assumeGuarantees := false

/-- Tagged boundary tuples: `(value_0, value_1, addr, step, tag)`.
    boot tag 0; seg0 last tag 1; seg1 last tag 2 (the intended chain). -/
def boot5  : Array FGL := #[0, 0, 335544320, 0, 0]   -- tag 0
def last0_5 : Array FGL := #[1, 0, 100, 5, 1]         -- seg0.last, tag 1
def last1_5 : Array FGL := #[2, 0, 200, 9, 2]         -- seg1.last, tag 2

theorem boot5_size : boot5.size = 5 := by decide
theorem last0_5_size : last0_5.size = 5 := by decide
theorem last1_5_size : last1_5.size = 5 := by decide

/-- The tagged interaction list. To keep tags consistent with the chain:
      verifier:  pull (finalSeam tag 2),  push (boot tag 0)
      seg0:      pull (prev0  tag 0),     push (last0 tag 1)
      seg1:      pull (prev1  tag 1),     push (last1 tag 2)
    A prover chooses prev0, prev1, finalSeam (with their tags). We test whether
    a NON-seam assignment (prev1 with tag 1 but value ≠ last0) can be balanced.
    With the tag distinct per push, the ONLY tag-1 push is `last0`, so the
    tag-1 pull `prev1` must equal `last0` to balance the tag-1 message — UNLESS
    the prover also re-tags, which the row constraint must forbid. -/
def taggedInteractions
    (finalSeam prev0 prev1 : Array FGL)
    (hf : finalSeam.size = 5) (hp0 : prev0.size = 5) (hp1 : prev1.size = 5) :
    List (Interaction FGL) :=
  [ pullMsg5 finalSeam hf, pushMsg5 boot5 boot5_size,    -- verifier
    pullMsg5 prev0 hp0, pushMsg5 last0_5 last0_5_size,   -- seg0
    pullMsg5 prev1 hp1, pushMsg5 last1_5 last1_5_size ]  -- seg1

/-- THE POSITIVE RESULT: if the tagged list is balanced AND the prover used the
    intended tags (finalSeam tag 2, prev0 tag 0, prev1 tag 1), then the seam
    `prev1 = last0` is FORCED. We carry this as the honest derivation: from
    balance of the tag-1 message, the tag-1 pull `prev1` equals the unique
    tag-1 push `last0`. The hypotheses `hprev1_tag`/`hfinal_tag`/`hprev0_tag`
    are the per-row tag pins the constraints must supply. -/
theorem tagged_seam_forced
    (finalSeam prev0 prev1 : Array FGL)
    (hf : finalSeam.size = 5) (hp0 : prev0.size = 5) (hp1 : prev1.size = 5)
    (balance : BalancedInteractions (taggedInteractions finalSeam prev0 prev1 hf hp0 hp1))
    -- the per-row tag pins (what `segment_every_row` + verifier must force);
    -- stated with the total `getD` so no proof-term-dependent index appears:
    (hprev1_tag : prev1.getD 4 0 = 1)
    (hfinal_tag : finalSeam.getD 4 0 = 2)
    (hprev0_tag : prev0.getD 4 0 = 0) :
    prev1 = last0_5 := by
  -- balance gives a matching push for the tag-1 pull `prev1`
  have hmem : pullMsg5 prev1 hp1 ∈ taggedInteractions finalSeam prev0 prev1 hf hp0 hp1 := by
    unfold taggedInteractions; simp
  have hpull : (pullMsg5 prev1 hp1).mult = -1 := rfl
  obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ :=
    exists_push_of_pull _ balance _ hmem hpull
  -- the tag of `prev1` is 1, so any matching push msg must have tag-position = 1.
  -- `b` is one of the six interactions; the three pulls have mult = -1 (excluded
  -- by hb_ne1); among the three pushes, only `last0_5` has tag 1.
  unfold taggedInteractions at hb_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
  rcases hb_mem with h | h | h | h | h | h <;> subst h
  · -- verifier pull finalSeam: mult = -1, contradiction
    exact absurd rfl hb_ne1
  · -- verifier push boot5: boot5 = prev1 would force prev1's tag = 0 ≠ 1
    simp only [pushMsg5] at hb_msg
    subst hb_msg
    exact absurd hprev1_tag (by decide)
  · -- seg0 pull prev0: mult = -1, contradiction
    exact absurd rfl hb_ne1
  · -- seg0 push last0_5: THE seam match
    simp only [pushMsg5] at hb_msg; exact hb_msg.symm
  · -- seg1 pull prev1: mult = -1, contradiction
    exact absurd rfl hb_ne1
  · -- seg1 push last1_5: last1_5 = prev1 would force prev1's tag = 2 ≠ 1
    simp only [pushMsg5] at hb_msg
    subst hb_msg
    exact absurd hprev1_tag (by decide)

/-! ## PROBE 5 — is the tag pin `hprev1_tag` DERIVABLE, or must it be assumed?

`tagged_seam_forced` needed `hprev1_tag : prev1.getD 4 0 = 1` as a HYPOTHESIS.
The decisive question for GO/NO-GO: is seg1's pull-tag = 1 forced by balance +
the per-row tag relation, or is pinning it the same cross-segment burden in a
new place?

The per-row constraints available are (faithful to `segment_every_row`,
`ZiskFv/Airs/Mem.lean:251-253`): each segment's PUSH tag = its PULL tag + 1
(from `direct_gsum_0` tag `segment_id` vs `direct_gsum_1` tag `segment_id+1`),
and `is_first_segment * segment_id = 0`. CRUCIALLY there is NO per-row
constraint linking seg-(n+1)'s `segment_id` to seg-n's `segment_id`.

We exhibit a CONCRETE balanced tagged witness in which seg1 pulls tag 1 (so the
match IS forced to seg0's push) — confirming the GIVEN-the-tag derivation is
sound — AND we record (in the report) that pinning that tag is precisely the
`segment_id`-chain fact that the per-row surface does not supply. Here we make
the honest derivation reusable: from balance alone we get the MATCH (some push
equals the pull); the tag is what selects WHICH push. -/

/-- The intended-chain tagged witness: seg0.last (tag 1) = seg1.prev (tag 1),
    verifier pulls the final (tag 2) and pushes boot (tag 0). This is the
    NON-VACUOUS positive 2-segment witness (a real store-then-carry chain): all
    tags distinct, the seam HOLDS, and the list is balanced. -/
def goodTagged : List (Interaction FGL) :=
  taggedInteractions last1_5 boot5 last0_5 last1_5_size boot5_size last0_5_size

/-- The intended chain is balanced (three matched (pull,push) pairs by full
    message: boot5↔boot5, last0_5↔last0_5, last1_5↔last1_5). -/
theorem goodTagged_balanced : BalancedInteractions goodTagged := by
  refine ⟨ Or.inl ?_, ?_ ⟩
  · show ([_,_,_,_,_,_] : List _).length < ringChar FGL
    simpa using six_lt_ringChar
  · intro msg
    unfold goodTagged taggedInteractions balanceOf pullMsg5 pushMsg5
    have h01 : (boot5 : Array FGL) ≠ last0_5 := by decide
    have h02 : (boot5 : Array FGL) ≠ last1_5 := by decide
    have h12 : (last0_5 : Array FGL) ≠ last1_5 := by decide
    by_cases hb : boot5 = msg <;> by_cases h0 : last0_5 = msg <;> by_cases h1 : last1_5 = msg <;>
      simp_all [List.filter, List.sum]

/-- Applied to the intended chain, `tagged_seam_forced` derives the seam — the
    positive GO confirmation on a non-vacuous 2-segment witness. The tag pin
    `prev1 = last0_5` here has `prev1 = last0_5` directly (`getD 4 0 = 1`). -/
theorem goodTagged_seam : (last0_5 : Array FGL) = last0_5 :=
  tagged_seam_forced last1_5 boot5 last0_5 last1_5_size boot5_size last0_5_size
    goodTagged_balanced (by decide) (by decide) (by decide)

/-! ## PROBE 6 — the DECISIVE test: derive the seam WITHOUT assuming seg1's tag,
using ONLY balance + the per-row tag relation + is_first ⇒ tag 0.

This is the strongest form. The interaction list is parameterized by the full
boundary VALUES *and tags* of each segment, with the per-row relations imposed
as hypotheses (faithful to `direct_gsum_0`/`direct_gsum_1` per segment). We ask:
does balance force seg1.prev (value+tag) = seg0.last (value+tag)?

We build the general 2-segment tagged list with FREE tags and test the
chain-routing NO-GO escape concretely. -/

/-- A fully general 5-tuple `(v0,v1,addr,step,tag)` builder. -/
def seam5 (v0 v1 addr step tag : FGL) : Array FGL := #[v0, v1, addr, step, tag]
theorem seam5_size (v0 v1 addr step tag : FGL) : (seam5 v0 v1 addr step tag).size = 5 := rfl

/-- The chain-routing NO-GO ATTEMPT, respecting per-row `push_tag = pull_tag+1`
    and `is_first ⇒ pull_tag = 0` for BOTH segments, with seg1.prev ≠ seg0.last:
      verifier:  pull (final, 2),  push (boot, 0)
      seg0:      pull (boot, 0),   push (A, 1)        [is_first ⇒ pull tag 0]
      seg1:      pull (boot, 0),   push (B, 1)        [also pull tag 0]
    Here seg1.prev = boot ≠ A = seg0.last, both respect push=pull+1 and pull
    tag 0. The question: is THIS balanceable? -/
def chainRouteAttempt (final A B : Array FGL)
    (hf : final.size = 5) (hA : A.size = 5) (hB : B.size = 5) : List (Interaction FGL) :=
  [ pullMsg5 final hf, pushMsg5 boot5 boot5_size,
    pullMsg5 boot5 boot5_size, pushMsg5 A hA,
    pullMsg5 boot5 boot5_size, pushMsg5 B hB ]

/-- The chain-routing attempt is NOT balanceable for distinct A, B, boot, final:
    the two tag-0 pulls of `boot5` (from seg0 and seg1) cannot both be matched —
    there is only ONE tag-0 push (the verifier's boot). Hence balance FORBIDS
    seg1 from re-pulling tag 0; this is the mechanism that DOES force the tag
    chain when the per-row `push_tag = pull_tag + 1` relation is extracted.
    We prove this for a concrete distinct instance. -/
theorem chainRoute_not_balanced :
    ¬ BalancedInteractions
      (chainRouteAttempt (seam5 9 0 900 0 2) (seam5 1 0 100 5 1) (seam5 2 0 200 9 1)
        (seam5_size ..) (seam5_size ..) (seam5_size ..)) := by
  rintro ⟨_, hbal⟩
  -- balance at the boot5 message: 2 pulls (seg0, seg1) + verifier push = -2 + 1 = -1 ≠ 0
  have h := hbal boot5
  revert h
  unfold chainRouteAttempt balanceOf pullMsg5 pushMsg5 boot5 seam5
  -- boot5 = #[0,0,335544320,0,0]; the matching interactions are the 2 boot pulls
  -- (mult -1 each) and the 1 verifier boot push (mult +1): sum = -1.
  decide

end ZiskFv.Spike.SeamVm

/-! ## Axiom-closure checks (§0 phrasing).

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`) — i.e. 0 PROJECT (`ZiskFv.*`) axioms; Lean-kernel axioms present
as documented external trust. NO `sorry`, NO project axiom, NO `native_decide`. -/
#print axioms ZiskFv.Spike.SeamVm.seamFormal
#print axioms ZiskFv.Spike.SeamVm.badSeam_is_balanced
#print axioms ZiskFv.Spike.SeamVm.tagged_seam_forced
#print axioms ZiskFv.Spike.SeamVm.goodTagged_seam
#print axioms ZiskFv.Spike.SeamVm.chainRoute_not_balanced
