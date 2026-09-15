# NOTE — The cross-segment memory-continuation "seam" (#103): the wall, the question, and what it tells us about ZisK

**Status:** ✅ **RESOLVED 2026-06-16 — NO Clean fork needed.** (Was "blocked on a
framework decision"; that framing is superseded — see the RESOLUTION banner below.
§4–§6 are kept as the historical record of the wrong-turn for context.) Standalone
reference so the core question doesn't get lost across context switches.
GitHub issue: eth-act/zisk-fv#103. Related: #76 (loads/stores), #61 (P4
construction / trace-level theorem).

---

## RESOLUTION (2026-06-16) — Clean already supports this; the `addVm` path was the wrong idiom

We do **not** need to change Clean. The right idiom is **`SoundEnsemble.addChannel`**
(`Clean/Air/OrderedChannel.lean:683`): it adds the continuation channel to
`ens.channels`, so its **balance becomes an assumed conjunct of `BalancedChannels`**
— the *same* `trace.balanced` trust class we already rely on — **with no soundness
obligation, no `addVm`, and without moving the Mem rows** (so the "wall" in §4 and the
deeper provider-in-VM balance issue never arise). The only reason it *looked* blocked:
our seam component emitted via `.pull` (→ `channelsWithGuarantees`, which trips
`subset_finished` and forces the channel to be finished — impossible for a
both-push-and-pull channel). The fix is to emit via `.emit (-1)` (→
`channelsWithRequirements`), which is exactly how production `Main` already consumes
MemBus.

**Confirmed NON-VACUOUS end-to-end** (git branch `seam-path1-evidence`,
`ZiskFv/Spike/SeamNonVacuousProbe.lean` + `SeamVmTagChain.lean`): a boot + 2-segment
ensemble using the **real** `SeamContChannel`/`SeamMessage` with the faithful `+1` tag
emission; `good_balancedChannels` *proves* the seam-balance antecedent is satisfiable
(not a degenerate/vacuous instance), and `seam_value_equality` derives
`seg1.previous_* = seg0.segment_last_*` from that balance via the proven tag-chain
derivation. Builds green, kernel-only axioms (0 PROJECT axioms). Adversarially verified:
the reviewer independently proved the antecedent inhabited (`∃ vb v0 v1,
BalancedChannels …`), confirmed the seamed boundary distinct from boot/final, forced a
real recompile, and got `lean_verify axioms:[]`.

**Why this is the right call, not laundering:** assuming the continuation channel's
balance is the *same* trust class as every other `ens.channels` member (`trace.balanced`
= proof-system soundness, which ZisK's global grand-product check genuinely provides);
nothing consumes the continuation channel's *guarantees* (its `Guarantees := True`), only
its *balance*; and §7's bug-hunt independently established ZisK's continuation is sound
*given* that balance.

**Residual to land on the real `fullRv64imEnsemble`** (all generalization / production
substitution — no new soundness question): (1) general N — generalize the N=2 tag-chain
derivation to arbitrary N (Newton power-sum chain); (2) swap the lightweight probe
component for production `componentWithSeamAndMemBus` + the literal `(1 - is_last_segment)`
push gating (exercises `exists_push_of_pull`'s zero-multiplicity clause); (3) `addChannel`
wiring on the real 11-table `SoundEnsemble`; (4) hook the derived seam into the #76
per-opcode Mem cross-entry obligations.

**Process note (for honesty):** the `addVm`/fork path (§4–§6) was a genuine wrong turn —
three successive read-only analyses called it "tractable/sound/minimal" and each was
refuted one layer deeper by an actual build. The breakthrough came from re-examining
whether Clean *already* supported it (Cody's prompt) and from ending the investigation in
a **non-vacuous compile probe** rather than an argument. Lesson recorded: for this kind of
framework-integration question, trust compiling non-vacuous code over design analysis.

---

## 0. The one-paragraph version

To verify ZisK's loads/stores (#76) at the trace level, we need a *cross-segment
memory seam*: a proof that the memory state ZisK carries from one execution
segment to the next is consistent (segment *n*'s final memory boundary equals
segment *n+1*'s starting boundary). We proved the **math** of that seam is
sound — the per-segment `segment_id` "tag chain" is forced by channel balance
with no smuggled assumption. But when we tried to **wire it into the real
ensemble**, we hit a wall in the *Clean* framework (the ZK-circuit DSL we build
on): the same memory rows that feed the per-row memory bus cannot also drive the
cross-segment "VM" channel, because Clean's `addVm` forbids it. The only clear
fix is a change to Clean itself. **The open question: is that Clean change a
tractable patch or a research-grade metatheory problem — and is there a
non-`addVm` route?**

---

## 1. Why we want this (the goal)

The endgame (#61) moves the global compliance theorem from an
envelope-conditional statement to a **trace-level** statement over raw committed
traces. Loads/stores (#76, 11 opcodes) are the largest remaining frontier, and
they are blocked on one thing: **memory consistency across segment boundaries.**

ZisK splits a program execution into **segments**, each proved as a separate AIR
instance. Within a segment, our load proofs already work (`LoadDerivation.lean`,
`SextLoadBridge.lean`, `MemAlignBridge.lean` — the per-row memory bus + the
address-sorted argument). The gap is: a load in segment *n+1* must read the last
value written in segment *n*. That cross-segment link is carried by ZisK's
**memory-continuation channel** (`MEMORY_CONTINUATION_ID`), and we need a Lean
proof that it does its job. We call that proof obligation the **seam**:

> `SeamColumnEquality`: for consecutive segments, `seg_n.segment_last_* =
> seg_{n+1}.previous_segment_*` (the boundary carried out of *n* equals the
> boundary carried into *n+1*).

## 2. How ZisK's continuation actually works (the mechanism)

Per the Mem PIL (`zisk/state-machines/mem/pil/mem.pil`) and our extraction
(`ZiskFv/Airs/Mem.lean`):

- Each segment carries boundary columns `previous_segment_*` (incoming) and
  `segment_last_*` (outgoing), plus an air-value `segment_id`.
- Each segment **pulls** its incoming boundary tagged `segment_id`
  (`direct_gsum_0`, hash tag `segment_id`) and **pushes** its outgoing boundary
  tagged `segment_id + 1` (`direct_gsum_1`, hash tag `segment_id + 1`), with the
  push **gated off on the last segment** (`* (1 - is_last_segment)`).
- A **boot endpoint** seeds the chain: `direct_global_update_proves(
  MEMORY_CONTINUATION_ID, [base_address, 0, internal_base_address, 0, ...zeros],
  sel: enable_flag)` (mem.pil:253) — the public boundary the verifier checks.
- The whole thing is a **grand-product / permutation** argument: the per-segment
  pulls and pushes telescope, so globally the boundaries chain up
  (seg 0 → seg 1 → … → final), anchored at the boot.

This is a **both-push-and-pull** channel (each segment both consumes and
produces a boundary). That single fact is the source of everything below.

## 3. What we proved (the de-risking — and an honest correction)

Two "make-or-break" questions, both **GO**, both adversarially verified:

- **The tag chain is *derived*, not assumed.** Given channel balance + the boot
  push (a verifier endpoint, same trust class as the assumed channel balance) +
  the `+1` emission, the segment ids are *forced* to be `0, 1, 2, …` in order,
  and the seam follows — with **no per-segment caller-supplied premise**. Proof:
  `ZiskFv/Spike/SeamVmTagChain.lean` (branch `spike-tagchain-evidence`), via a
  weighted-balance lemma + Newton's identities + `exists_push_of_pull`. This is
  the anti-laundering crux passing: the seam is *discharged*, not *relocated*.
- **No-wrap is free.** `segment_id` has **no range check** in ZisK (it's an
  air-value pinned only by `is_first_segment * segment_id = 0`, mem.pil:97/107).
  But `BalancedInteractions` carries its own side condition
  `interactions.length < ringChar` (Clean `Balance.lean:24`), so for an
  N-segment trace `2N+2 < p ⟹ N < p ⟹` the tags `0…N-1` are distinct field
  elements. No-wrap is part of the assumed channel-balance trust class, not a
  new premise.

> **Honest correction (recorded so it isn't repeated):** I earlier told Cody the
> route was *"fully de-risked end-to-end."* That was an **overclaim**. The
> spikes de-risked the seam **math in isolation**; they never exercised the
> **integration** of the seam channel with the real memory-bus-providing rows —
> which is exactly where the wall (§4) is. Lesson: when scoping a
> framework-composition step, read **all** of the target primitive's
> preconditions and de-risk the **integration**, not just the isolated math.

## 4. The wall (why it's blocked)

To make the seam real, the *same* Mem rows must emit **both** the per-row memory
bus (`MemBus`, a normal "finished" provider/consumer channel) **and** the
cross-segment seam (a "VM"/transition channel). Clean refuses this:

- The cross-segment seam **cannot be a normal "finished" channel**: a
  both-push-and-pull channel "does not hold `SoundChannels` for ANY list of
  channels" (Clean `OrderedChannel.lean:440-445`). That's precisely why it must
  be hosted as a **VM channel** via `addVm` (Clean's state-transition primitive).
- But `addVm`'s precondition `reqs_disjoint_finished` (Clean `Vm.lean:688`)
  requires: *no finished channel may appear in the VM table's
  `channelsWithRequirements`.* The Mem rows **provide** `MemBus`, and a provider
  `emit` is classified into `channelsWithRequirements` (Clean
  `Operations.lean:1094`). `MemBus` is finished. ⟹ the precondition is **provably
  false**.
- And `MemBus` **cannot just be left unfinished** — then it has no soundness
  path (neither finished nor a VM channel).

So: the seam must be a VM channel; a VM table can't also provide a finished
channel; the Mem rows do both. **Stuck.** (This is a *Clean* limitation, not a
ZisK-design problem — ZisK's real circuit happily has the same rows emit both.)

Verified BLOCKED state: whole project still green, all 63 canonical theorems
byte-identical, 0 project axioms, nothing faked (commit `26fbad01`, branch
`xcap-seam-tag`). The sound dual-bus VM host `memSegVmFull` is committed as the
artifact any fix would consume.

## 5. The fork clarification (corrects a second overstatement)

I initially framed the fix as "forking Clean = a scope deviation." **We already
have a Clean fork:** `flake.nix` pins `clean-src = github:codygunton/clean/…` —
Cody's own repo (changeable freely), currently a thin snapshot of upstream
`Verified-zkEVM/clean` plus one compatibility shim, intended to re-point at
upstream once both merge. So:

- **Fork ownership is a non-issue.** Patching `Clean/Air/Vm.lean` is just another
  commit on a fork we control.
- The real consideration is **maintenance posture**: the fork has so far only
  *tracked* upstream; a substantive `addVm` variant is a *divergent* patch we'd
  carry (or try to upstream to `Verified-zkEVM/clean`).
- The real **risk** is the **metatheory**, not the fork: is the precondition
  conservative (easy variant) or load-bearing (hard/unsound to relax)?

## 6. THE OPEN QUESTION (don't lose this)

> **Is a Clean `addVm` variant — one that admits a VM table which *also* provides
> an already-finished channel — a tractable patch or a research-grade metatheory
> problem? And is there a non-`addVm` route that gets the continuation channel's
> balance into the proof obligation without it (e.g. deriving the seam directly
> from the raw continuation-channel balance, the way `SeamVmTagChain.lean` does
> at the `BalancedInteractions` level)?**

Candidate fixes, in rough order of appeal:
1. **`addVm` variant** in `codygunton/clean` admitting a VM table that also
   provides a finished channel (needs a *combined balance* argument). Unknown
   difficulty — this is the thing to feasibility-check first.
2. **Multi-channel VM** hosting both `MemBus` and the seam. Likely a poor fit —
   `MemBus` is provider/consumer, not a transition.
3. **Non-`addVm` derivation**: add the continuation channel to the ensemble's
   balance obligation by some route other than `addVm`/finished, and derive the
   seam directly from its assumed balance. Unverified whether Clean's
   `channels` model permits this.

Decision options on the table (no commitment yet): (a) short feasibility read
first [recommended], (b) commit to building the `addVm` variant, (c) pause #103
and do buildable-now P4 work (M-extension, LUI/AUIPC), (d) reconsider whether
#76 can land single-segment-first.

---

## 7. What this tells us about possible ZisK bugs, and how to validate

> The memory-continuation seam is exactly the kind of place real **soundness
> bugs** could hide: it's a global, cross-proof argument with a hand-rolled
> permutation, several unchecked air-values, and a boundary that compresses a
> whole segment's memory state into a few columns. Our FV effort is valuable here
> not just because it *proves* the seam, but because building the proof
> **surfaces every assumption the circuit silently relies on** — and any
> assumption the circuit does *not* actually enforce is a candidate bug.

_Source-grounded against `mem.pil` (532 lines), `zisk.pil`, `std_direct.pil`,
the Rust generator (`mem.rs`, `mem_sm.rs`, `mem_module_planner.rs`), Clean's
`Balance.lean`, our `Airs/Mem.lean`, and the balance-escape spikes — then
**adversarially re-checked** against the same source. The first pass overstated
three items; the verdicts below are the corrected ones. Methodological honesty:
this is exactly why we adversarially verify — the naive list flagged `enable_flag`
as the "top unaudited dependency" and "padding inflates step" as a soundness
edge; both turned out to be already-closed or a source misread._

### The one structural insight (the spine of everything)

ZisK's cross-segment chain has **no local PIL constraint linking segment *n* to
segment *n+1*.** All linkage — `prev = prior-last`, single cycle,
exactly-one-first/last, the `segment_id` chaining — is delegated to the **global
sum-bus balance** over `MEMORY_CONTINUATION_ID = 11`, anchored by **one** global
boot push (mem.pil:253) and terminated by `is_last_segment` suppressing the
outgoing push (mem.pil:241). And the continuation air-values (`segment_id`,
`previous_segment_*`, `segment_last_*`, `is_first/last_segment`) carry **no
`bits()` and no `range_check`** (only two one-sided distance clamps). So the
candidate bugs are the distinct ways that delegation could be unsound — and our
seam proof's job is to show the delegation is, in fact, sound (and to make every
silent assumption explicit).

There are **exactly three participants** on the bus (the whole defense): the
unconditional per-segment **assume** (pulls tag `segment_id`), the per-segment
**prove** (pushes tag `segment_id+1`, gated `1 - is_last_segment`), and the
single **boot** push (tag `0`, gated `enable_flag`). Everything below follows
from enumerating those three.

### Candidate bug classes (corrected, ranked by genuine residual leverage)

| # | Candidate | Verdict | Why |
|---|-----------|---------|-----|
| **1** | **Seam non-derivation** — balance forces *membership* (each pulled boundary = *some* pushed one), not the *specific* link `last(n)=prev(n+1)`. A balanced-but-wrong routing can break the seam. | **REAL, open — but a *proof* obligation, not a live circuit hole** | Machine-checked adversarial witness exists (`SeamVm.lean::badSeam_is_balanced`/`badSeam_breaks_seam`): a fully-balanced permutation where `seg1.prev ≠ seg0.last`. The `+1` tag emission (pull tag `segment_id` `Mem.lean:1357` vs push tag `segment_id+1` `:1367`) *does* close it in the circuit; our `tag_chain_derived` proves so. Nothing currently landed depends on the continuation (trust ledger = 0 axioms), so this is an obligation for #76/#103, not a bug in what's proved today. |
| **4** | **Generator-vs-PIL permissiveness** — PIL accepts traces the honest generator never emits: `segment_id` bare (only `is_first*segment_id=0`); `is_last_segment` not *locally* forced unique; `segment_last_*` checked only on physical row N−1 (the padding row). | **REAL, but downstream of #1** | All three verified in source. Each is "correct only because the global bus catches it." Not an independent hole — it's the *checklist of what the local constraints do not defend*, which the seam proof (via the tags) must cover. |
| **6** | **Latent dual-step coupling** — PIL reads `segment_last_step` off row N−1 with only a self-consistency check; the generator computes it from its own bookkeeping (`mem_sm.rs:275-276` dual resolution). A future padding edit could desync them and PIL would still accept. | **Latent / not live** | Current code is correct. Maintenance/regression-guard concern, not a soundness hole. |
| **7** | **One-sided distance clamps; large-mem chunk width** — `previous_segment_addr ≥ base`, `segment_last_addr ≤ end` are one-sided; `assert(size_mb≤4096)` is compile-time, not a circuit constraint. | **Cosmetic** | Region size is instantiation-fixed (zisk.pil:102-104); no per-run prover freedom. Documentation of clamp granularity, nothing more. |

### Items the naive pass flagged that the adversarial check CLOSED or corrected

- **No-wrap (`segment_id` reaching field size) — CLOSED, not an open assumption.**
  `BalancedInteractions` carries `interactions.length < ringChar` (Balance.lean:24)
  as a *built-in* side condition of the trusted balance antecedent: `2N+2 < p ⟹`
  tags `0..N-1` distinct. Realistic worst-case segment count is `~2^14` (Rust
  audit) vs `p ≈ 2^64` — ~50-bit margin. So no-wrap is already inside the
  channel-balance trust class; **not a new premise.** (The unchecked-`segment_id`
  seed from §3 is *real as a fact* but *benign* for this reason.)
- **Boot `enable_flag` "unaudited external dependency" — OVERSTATED; effectively
  CLOSED.** The naive pass called this the top residual. But `enable_rom_data` /
  `enable_input_data` *are* declared and boolean-constrained (zisk.pil:35-39), and
  the escape is structurally impossible: the only tag-0 producer is the boot, so a
  real first segment's tag-0 *assume* is **unbalanced unless `enable_flag=1`** —
  balance forces the boot on whenever a segment exists. Residual reduces to a
  ~10-minute Lean lemma when #103 lands (confirm exactly one tag-0 push per
  `base_address` in the rendered channel). The missing memory-**END** global
  assume (asymmetric vs `main.pil:528-529`, which pins both ends) is **real and
  intentional** — the end is closed by `is_last_segment` suppression + the
  upper-bound clamp, worth a one-line confirmation with the ZisK authors, not a
  hole.
- **"Padding inflates `segment_last_step`" — REJECTED (generator misread).** The
  PIL comment says "incrementing step" (mem.pil:405) but the generator HOLDS step
  constant on padding rows (`mem_sm.rs:280-300`: `set_step(step)`,
  `addr_changes=false`, `increment=0`). So `segment_last_step` = the true
  last-access step; the supposed inflation mechanism doesn't exist. The only
  residual is the generic "step is bus-pinned, not locally" — already covered by
  #1/#4.

### Validation strategy (highest value first)

1. **Land the cross-segment seam derivation (#76/#103) over the real whole-trace
   row list** — this *is* the validation of class #1, and transitively #4. Fold
   the per-segment facts via the `_append` lemmas (`MemTrace.lean:1046/1055/1076`)
   into one whole-trace alignment, replacing the currently-free `previous_segment_*`
   seed (`Airs/Mem.lean:324`) with a *proven* carry-out. **Acceptance test for
   non-vacuity: the proof must FAIL to typecheck if you delete the tag
   projection** (i.e. it genuinely depends on the `+1` tags, not bare balance).
   **But note:** the real make-or-break for #1 is no longer the seam *math* (done,
   `tag_chain_derived`, axiom-clean) — it is the **Clean `addVm` framework wall**
   in §4-6. *That* is where validation effort should go, not re-spiking the chain.
2. **Two small confirmations when #103 lands** (both ~one lemma): (a) general-N
   no-wrap as the `Balance.lean` length-bound side condition for
   `MEMORY_CONTINUATION` (currently proved at N=2); (b) single tag-0 producer per
   `base_address` (closes boot-uniqueness / the `enable_flag` residual).
3. **Class #4 as adversarial-witness fixtures** — extend the `badSeamInteractions`
   family at the Lean channel level: a non-dense `segment_id` set; two segments
   with `is_last_segment=1`; a self-consistent-but-wrong padded `segment_last_*`.
   Each should pass *local* constraints and fail the grand sum — confirming "the
   bus is the only defense" and that it has no degeneracy.
4. **Class #6** — a generator-side assertion / CI guard that padding's step pick
   matches the dual resolution at `mem_sm.rs:275-276`. Not a proof; a regression
   tripwire.
5. **One author question** — confirm the missing memory-END global assume
   (vs `main.pil:528-529`) is intended.

### What our FV effort validates vs. what needs separate checks

- **Validated by landing the seam proof:** class #1 (directly — its whole
  purpose), no-wrap (folds in as the length-bound side condition), and the
  topology half of class #4 (the tags force "exactly one chain").
- **NOT validated by the seam proof — separate checks:** boot-uniqueness /
  single-tag-0-producer (the small lemma in step 2b — the seam proof *hosts* the
  boot as a verifier endpoint but assumes its uniqueness); class #6 (generator
  guard); class #7 (documentation). None of these are live holes today (0 axioms,
  no landed theorem consumes the continuation) — they are obligations that come
  due *when* loads/stores land on the seam.

**Bottom line for ZisK soundness:** the continuation design is sound *given* the
global-bus balance (the upstream-trusted antecedent), and the one genuinely
unusual choice — unranged `segment_id` with a single global anchor and no local
n↔n+1 link — is safe because balance + the `+1` tags + the length bound carry the
weight. The most valuable thing we can do is **land the seam proof** (which makes
all of this machine-checked and surfaces the boot-uniqueness lemma explicitly) —
and that is currently gated by the Clean framework wall (§4-6), not by any ZisK
soundness question.
