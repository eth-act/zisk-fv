import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.ZiskCircuit.MemTimeline.Construction
import ZiskFv.ZiskCircuit.MemTimeline.Ordering

/-!
# SPIKE #1 — cross-segment whole-trace seam (2-segment de-risk)

THROWAWAY go/no-go proof of concept. NOT for merge.

Goal: take two per-segment `AcceptedMemoryReplayEvidence` objects (seg0 + seg1,
each project-axiom-clean via the existing first/continuation constructors) and
glue them into ONE whole-trace `AcceptedMemoryReplayEvidence` via the existing
`memoryBusRowsPrefixReadSound_append`. Surface the EXACT seam equality the glue
demands, and decide whether it closes from the extracted Mem constraints
(`segment_every_row` ∧ `permutation_every_row`) + memory-bus balance, with NO
new axiom/premise.
-/

namespace ZiskFv.Spike.Seam

open Goldilocks
open Interaction
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.AirsClean.Mem (GeneratedMemReplayFacts)
open ZiskFv.AirsClean.FullEnsemble

/-! ## Step 1 — restate the append glue at the AcceptedMemoryReplayEvidence level.

`memoryBusRowsPrefixReadSound_append` gives whole-trace prefix-read soundness
from:
  - seg0's prefixReadSound over `initialMemory0` and `rows0`, and
  - seg1's prefixReadSound over `replayMemoryAfterBusRows initialMemory0 rows0`
    and `rows1`.

But each per-segment constructor gives seg1's prefixReadSound over seg1's OWN
initial memory `initialMemory1` (= `previousSegmentInitialMemoryOfRows seg1 …`),
NOT over `replayMemoryAfterBusRows initialMemory0 rows0`.

So the SEAM EQUALITY that the glue requires is exactly:

  replayMemoryAfterBusRows initialMemory0 rows0  =  initialMemory1            (★)

i.e. the memory state segment 0 carries OUT (replaying all of seg0's rows from
its zero/boot initial memory) equals the memory segment 1 is SEEDED with.

This abstract lemma states the glue cleanly given (★) as a hypothesis, to make
the obligation explicit and confirm the append machinery composes. -/
theorem whole_trace_prefixReadSound_of_segments
    (initialMemory0 initialMemory1 : Std.ExtHashMap Nat (BitVec 8))
    (rows0 rows1 : List (MemoryBusEntry FGL))
    (h0 : MemoryBusRowsPrefixReadSound initialMemory0 rows0)
    (h1 : MemoryBusRowsPrefixReadSound initialMemory1 rows1)
    -- (★) the seam equality, supplied here as a hypothesis to isolate it:
    (h_seam : replayMemoryAfterBusRows initialMemory0 rows0 = initialMemory1) :
    MemoryBusRowsPrefixReadSound initialMemory0 (rows0 ++ rows1) := by
  apply memoryBusRowsPrefixReadSound_append initialMemory0 rows0 rows1 h0
  rw [h_seam]
  exact h1

/-! ## Step 2 — what `initialMemory1` actually IS, and why (★) cannot close.

The continuation per-segment constructor seeds segment 1 with

  initialMemory1 = previousSegmentInitialMemoryOfRows seg1 rows1
                 = writeMemoryOfEntry (zeroMemoryOfRows rows1)
                     (memPreviousSegmentReplayEntry seg1)

`memPreviousSegmentReplayEntry seg1` is a SINGLE write entry built from seg1's
`previous_segment_addr / previous_segment_value_0 / previous_segment_value_1`
columns. So `initialMemory1` is a map that:
  - is zero (8 zero bytes) at every pointer mentioned by `rows1`, EXCEPT
  - carries ONE address: seg1's `previous_segment_addr`, with seg1's
    `previous_segment_value_*`.

But `replayMemoryAfterBusRows initialMemory0 rows0` is the FULL replayed memory
after segment 0 — it has a (potentially) DISTINCT entry for EVERY address that
segment 0 wrote, plus seg0's boot-zero preload over rows0's pointers.

These two maps have DIFFERENT DOMAINS in general:
  LHS domain ⊇ { every addr seg0 touched } ∪ { boot-zero preload of rows0 }
  RHS domain = { boot-zero preload of rows1 } ∪ { seg1.previous_segment_addr }

Equality (★) of `ExtHashMap`s therefore DOES NOT HOLD as stated. The
per-segment continuation seed deliberately carries ONLY the single straddling
boundary address (address-sorted Mem: only the address whose rows cross the
segment boundary needs carry-in), NOT seg0's whole final memory. -/

/-! ## Step 3 — the WEAKER, correct obligation, and where IT stalls.

The glue does not actually need full map equality. It needs seg1's
prefixReadSound to hold against `replayMemoryAfterBusRows initialMemory0 rows0`.
Each selected read in `rows1` only inspects ITS OWN 8 bytes. So the honest
obligation is the byte-local agreement, for every read row in rows1, between
  replayMemoryAfterBusRows initialMemory0 (rows0 ++ priorRows1)   -- whole-trace
  replayMemoryAfterBusRows initialMemory1 priorRows1              -- per-segment
restricted to that read's pointer.

This reduces to a per-address claim:
  for the boundary address A that seg1 reads via the carry path,
  the value seg0 leaves at A (replaying seg0) equals seg1.previous_segment_value
  (the carry-in seed).

THAT is the genuine cross-segment seam fact. It is NOT a consequence of
`segment_every_row`/`permutation_every_row` of seg0 alone, nor of seg1 alone:
  - seg0's `segment_last_value_*` columns equal seg0's LAST ROW value
    (theorem `segment_last_carry_eq_of_next_boundary_segment_every_row`), but
    only when seg0's NEXT row starts a new segment — and seg0's last row value
    is NOT in general the replayed value at the boundary address A (address
    sorting means A's last write/read may be in the MIDDLE of seg0's rows, not
    its last row; `segment_last_*` is the carry of the LAST address class, not
    of A).
  - seg1's `previous_segment_value_*` columns are an INPUT to the continuation
    constructor; `segment_previous_carry_eq_previous_segment_of_boundary` ties
    seg1's row-0 to these columns, but says nothing about seg0.
  - the LINK `seg0.segment_last_* = seg1.previous_segment_*` lives ONLY in the
    permutation accumulator (`direct_gsum_0` consumes seg1.previous_segment_*;
    `direct_gsum_1` consumes seg0.segment_last_*), and ONLY as a GLOBAL balance
    (the sum of all segments' direct sends/receives = 0), which is NOT proved
    anywhere and is NOT a per-row fact in `permutation_every_row`.

To make the missing fact a concrete, named obligation, state it. This is the
seam equality at the COLUMN level (the honest minimal cross-segment fact): -/
def SeamColumnEquality
    (seg0 seg1 : ZiskFv.Airs.Mem.SegmentColumns FGL) : Prop :=
  seg0.segment_last_value_0 = seg1.previous_segment_value_0
    ∧ seg0.segment_last_value_1 = seg1.previous_segment_value_1
    ∧ seg0.segment_last_addr = seg1.previous_segment_addr
    ∧ seg0.segment_last_step = seg1.previous_segment_step

/-! Even GIVEN `SeamColumnEquality`, the map-level seam still needs the bridge
"the replayed value seg0 leaves at the boundary address A = seg0.segment_last_*",
which requires that A IS the last address class of seg0 — true for the
address-sorted whole-execution Mem (the global table is one address-sorted run
split into segments), but NOT expressible from a single segment's
`segment_every_row`. That bridge is the genuinely novel whole-trace lemma. -/

/-! ## Step 4 — a CONCRETE non-vacuous witness that (★) is FALSE.

To make the NO-GO rigorous (not merely argued), exhibit a concrete 2-address
segment 0 whose replayed memory differs, AT A SPECIFIC KEY, from the
single-entry continuation seed any per-segment constructor produces for
segment 1. This is the anti-vacuity counter-witness: it shows the map-level
seam (★) is genuinely unprovable, because the two maps differ.

seg0 = one store row writing 8 bytes at byte-pointer 16 with a NONZERO low byte.
The continuation seed `previousSegmentInitialMemoryOfRows seg1 []` carries only
ONE address (seg1.previous_segment_addr), seeded over the empty rows1 list — so
it has NOTHING at key 16. Hence the two maps disagree at key 16. -/

/-- A concrete store row: write `as = 2`, `multiplicity = 1`, pointer 16,
nonzero value. -/
def storeRowAt16 : MemoryBusEntry FGL :=
  { multiplicity := 1, as := 2, ptr := 16,
    value_0 := 1, value_1 := 0, timestamp := 5 }

/-- A concrete continuation `SegmentColumns` whose carried previous-segment
address is 0 (a DIFFERENT address from seg0's write at 16). All other fields
are defaulted to 0; only the previous-segment carry matters here. -/
def seg1Cols : ZiskFv.Airs.Mem.SegmentColumns FGL :=
  { segment_id := 1, is_first_segment := 0, is_last_segment := 0,
    previous_segment_value_0 := 7, previous_segment_value_1 := 0,
    previous_segment_step := 0, previous_segment_addr := 0,
    segment_last_value_0 := 0, segment_last_value_1 := 0,
    segment_last_step := 0, segment_last_addr := 0,
    distance_base_0 := 0, distance_base_1 := 0,
    distance_end_0 := 0, distance_end_1 := 0,
    segment_l1 := fun _ => 0 }

/-- The replayed-after-seg0 memory has a byte present at key 16. -/
theorem seg0_replay_has_key_16 :
    (replayMemoryAfterBusRows ({} : Std.ExtHashMap Nat (BitVec 8))
      [storeRowAt16])[16]?.isSome = true := by
  native_decide

/-- The single-entry continuation seed for seg1 (over empty rows1) has NOTHING
at key 16 — its only write is at `previous_segment_addr * 8 = 0`. -/
theorem seg1_seed_missing_key_16 :
    (previousSegmentInitialMemoryOfRows seg1Cols
      ([] : List (MemoryBusEntry FGL)))[16]?.isSome = false := by
  native_decide

/-- Therefore the seam equality (★) is FALSE on this concrete non-vacuous
2-segment instance: the two memory maps differ at key 16. This is the rigorous
NO-GO witness — the map-level seam the `_append` glue demands cannot hold. -/
theorem seam_star_is_false :
    replayMemoryAfterBusRows ({} : Std.ExtHashMap Nat (BitVec 8)) [storeRowAt16]
      ≠ previousSegmentInitialMemoryOfRows seg1Cols
          ([] : List (MemoryBusEntry FGL)) := by
  intro h_eq
  have h_lhs := seg0_replay_has_key_16
  have h_rhs := seg1_seed_missing_key_16
  rw [h_eq] at h_lhs
  rw [h_lhs] at h_rhs
  exact absurd h_rhs (by decide)

end ZiskFv.Spike.Seam

-- Axiom closure of the append-glue lemma (Step 1), for the §0 phrasing check.
#print axioms ZiskFv.Spike.Seam.whole_trace_prefixReadSound_of_segments
#print axioms ZiskFv.Spike.Seam.seam_star_is_false
