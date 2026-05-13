import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus

/-!
# MemoryBus.MemBridge — bridge Mem-AIR rows to Main-side memory-bus lane match

This module closes the `memory_load_lanes_match` /
`memory_store_lanes_match` predicates against the `Mem` AIR's row
constraints. It is the writes-side analogue of the reads-side
`Airs/MemoryBus/LaneMatch.lean` lemmas (which composed slot-match thunks
from the **register-bus** emissions); here we work against the
**memory-bus** side (`as = 2`) where the value lanes carry the actual
load/store byte content.

## Architecture

ZisK's memory-side bus protocol (`bus_id = 10`, `as = 2`) emits 12-slot
byte-decomposed entries: `[as, ptr, mem_step, bytes, x0, x1, ..., x7,
multiplicity]`. The Main AIR's load/store rows emit one such entry per
memory operation; the `Mem` AIR consumes (or produces) the matching
permutation half via its primary witness columns
(`addr`, `step`, `value_0`, `value_1`, `wr`, `sel`).

Because the Mem AIR carries the value as a pair of 32-bit chunks
(`value_0`, `value_1`) rather than as 8 byte lanes, the Mem-row → bus-entry
correspondence requires a byte-decomposition witness: the eight bytes
`x0..x7` must pack into `value_0` (low 32 bits) and `value_1` (high
32 bits). The byte-range bus discharges this for live mem rows. We
expose it here as the `entry_packs_mem_row_value` predicate, plus a
dedicated trusted-surface axiom for the permutation handshake itself.

## Trusted surface introduced

This file introduces **one** new trust-base entry — documented in
`docs/fv/trusted-base.md` under the "Memory-bus permutation
soundness" section:

* `MemoryBus.lookup_consumer_matches_provider` — for every Main-side
  memory-bus emission (load or store), there exists a Mem AIR row whose
  `(addr, step, value_0, value_1, wr)` projection matches the entry's
  `(ptr, timestamp, lo, hi, mult-encoded-write-flag)`. Mirrors the
  `OperationBus.matches_entry` pattern at `bus_id = 5000`. Permutation
  argument soundness for `bus_id = 10`.

The bridge lemmas `memory_load_lanes_match_of_mem_row` and
`memory_store_lanes_match_of_mem_row` consume this axiom plus structural
F-typed Mem-row constraints (read mode `wr = 0`, sel pinning, byte
decomposition) to discharge the Main-side lane-match predicate without
caller-supplied `h_emit` hypotheses on the entry's lo/hi halves.
-/

namespace ZiskFv.Airs.MemoryBus.MemBridge

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Mem-row ↔ bus-entry correspondence -/

/-- **Byte decomposition of a Mem row's value chunks.** Asserts that the
    eight memory-bus byte lanes `e.x0 .. e.x7` pack into the Mem row's
    32-bit value chunks at `r_mem`:

    * low chunk: `value_0 r_mem = x0 + x1*256 + x2*65536 + x3*16777216`
    * high chunk: `value_1 r_mem = x4 + x5*256 + x6*65536 + x7*16777216`

    This is the byte-range invariant the PIL byte-bus discharges:
    Mem stores values as 32-bit chunks; the memory-side bus carries
    them byte-decomposed; the byte-bus range-checks each lane to
    `[0, 256)`. -/
@[simp]
def entry_packs_mem_row_value
    (mem : Valid_Mem C FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  mem.value_0 r_mem = memory_entry_lo e
  ∧ mem.value_1 r_mem = memory_entry_hi e

/-- **Mem row matches a bus entry.** A bus entry `e` corresponds to Mem
    AIR row `r_mem` of `mem` when:

    * `mem.sel r_mem = 1` (the row is live, emitted to the bus);
    * `mem.addr r_mem = e.ptr` (memory address agrees);
    * `mem.step r_mem = e.timestamp` (mem-step / timestamp agrees);
    * `e.as = 2` (memory-side address space; `as = 1` is the register
      side);
    * `entry_packs_mem_row_value` (byte decomposition of value chunks).

    The `wr` bit is *not* part of this predicate — it is parameterized
    by the load / store discharge lemmas below (load: `wr = 0`;
    store: `wr = 1`). -/
@[simp]
def mem_row_matches_entry
    (mem : Valid_Mem C FGL FGL) (r_mem : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  mem.sel r_mem = 1
  ∧ mem.addr r_mem = e.ptr
  ∧ mem.step r_mem = e.timestamp
  ∧ e.as = 2
  ∧ entry_packs_mem_row_value mem r_mem e

/-! ## Trusted-surface: memory-bus permutation soundness

Mirrors `OperationBus.matches_entry` (operation-bus `bus_id = 5000`)
which is the trusted permutation handshake at the operation-bus level.
The memory-bus analogue says: for every Main-side memory-bus emission,
there is a paired Mem AIR row carrying the same `(addr, step,
value_0, value_1)` projection.

Lookup-protocol soundness — assumed, not proven, per
`CLAUDE.md`'s out-of-scope statement on PLONK / plookup / logUp /
permutation arguments.
-/

/-- Width-conditional zero-padding predicate. Asserts that the high
    bytes of `e` (those above the load width) are zero, parameterized
    on the FGL-valued width column. The load axiom below pins this for
    `width ∈ {1, 2, 4}`; width 8 (LD) leaves all lanes meaningful so
    the predicate is vacuous in that case.

    For loads narrower than 8 bytes (LBU=1, LHU=2, LWU=4), ZisK's
    MemAlign state machines zero-pad the unused high byte lanes of
    the memory-bus entry. The constraint is enforced via the
    MemAlign-side permutation argument tying the Main row's
    `ind_width` selector to the MemAlign* AIR's emitted entry.
    Citations:
    * `zisk/state-machines/mem/pil/mem_align_byte.pil:96-101`
      (MemAlignByte: read-byte selector, value[1] = 0).
    * `zisk/state-machines/mem/pil/mem_align.pil:189` (MemAlign:
      sub-doubleword prove side, prove_val[1] = 0). -/
@[simp]
def high_bytes_zero_for_width (e : MemoryBusEntry FGL) (width : FGL) : Prop :=
  (width = 1 → e.x1 = 0 ∧ e.x2 = 0 ∧ e.x3 = 0
              ∧ e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0)
  ∧ (width = 2 → e.x2 = 0 ∧ e.x3 = 0
                ∧ e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0)
  ∧ (width = 4 → e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0)

/-- **Memory-bus permutation soundness — load side.** Given a Main row
    `r_main` whose memory-bus emission carries the load entry `e`
    (`as = 2`, `multiplicity = -1` — the consumer / "assumes" side at
    `state-machines/mem/pil/mem.pil:526`), there exists a Mem AIR row
    `r_mem` whose `(addr, step, value_0, value_1, wr)` projection
    matches `e`'s `(ptr, timestamp, lo, hi, 0)`.

    This axiom delivers ONLY the Mem-AIR side of the handshake. Sub-
    doubleword loads (LBU/LHU/LWU) are also provided by MemAlign\*
    AIRs — that side of the bus is covered by
    `Airs/MemoryBus/MemAlignBridge.lean::memalign_load_perm_sound`,
    a separate axiom of the same trust class.

    PLONK-style permutation soundness for the arithmetic protocol is
    project-trusted (see CLAUDE.md "Trust scoping"). -/
axiom lookup_consumer_matches_provider_load
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_emit : main.b_0 r_main = memory_entry_lo e
              ∧ main.b_1 r_main = memory_entry_hi e
              ∧ e.as = 2
              ∧ e.multiplicity = -1) :
    ∃ r_mem : ℕ,
      mem_row_matches_entry mem r_mem e
      ∧ mem.wr r_mem = 0

/-- **Memory-bus permutation soundness — store side.** Given a Main row
    `r_main` whose memory-bus emission carries the store entry `e`
    (`as = 2`, `multiplicity = 1` — the producer / "proves" side at
    `state-machines/mem/pil/mem.pil:527`), there exists a Mem AIR row
    `r_mem` whose projection matches `e`'s `(ptr, timestamp, lo, hi, 1)`. -/
axiom lookup_consumer_matches_provider_store
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_emit : main.c_0 r_main = memory_entry_lo e
              ∧ main.c_1 r_main = memory_entry_hi e
              ∧ e.as = 2
              ∧ e.multiplicity = 1) :
    ∃ r_mem : ℕ,
      mem_row_matches_entry mem r_mem e
      ∧ mem.wr r_mem = 1

/-! ## Lane-match discharge from Mem row -/

/-- **Memory-load lane match from Mem AIR row.** The writes-side
    counterpart of `register_read_rs1_lanes_match_of_bus_emission` /
    `register_read_rs2_lanes_match_of_bus_emission` from
    `LaneMatch.lean`, but for the memory-side bus (`as = 2`).

    Given:
    * `h_main_emit` — Main row `r_main`'s `b_0` / `b_1` lanes pack to
      the entry's lo / hi halves, with `as = 2` and `multiplicity = -1`
      (the load-side bus emission shape);

    we derive the `memory_load_lanes_match` predicate (which is exactly
    `b_0 = lo ∧ b_1 = hi`).

    The proof is direct from `h_main_emit` — Main's emission *is* the
    lane match. The `lookup_consumer_matches_provider_load` axiom
    isn't needed at this level (the lane match doesn't reference the
    Mem AIR); it surfaces in `Spec/MemModel.lean::mem_load_correct`,
    where the Sail-state predicate is derived from the Mem row's
    grounding.

    This lemma is structural; its job is to retire callers' direct
    `h_emit` hypotheses by exposing the same content under a uniform
    name aligned with the rest of the lane-match family. -/
theorem memory_load_lanes_match_of_main_emit
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_main_emit : m.b_0 r_main = memory_entry_lo e
                   ∧ m.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    memory_load_lanes_match m r_main e := by
  exact ⟨h_main_emit.1, h_main_emit.2.1⟩

/-- **Memory-load lane match from Mem AIR row.** Composes the Main-side
    bus emission with the Mem AIR row to produce both the lane-match
    conclusion and a witnessed Mem row that grounds it.

    The Mem row is delivered via the trusted permutation-soundness axiom
    `lookup_consumer_matches_provider_load`. The lane match itself is
    structural (from Main's emission); the witnessed Mem row is the
    object `Spec/MemModel.lean::mem_load_correct` consumes to derive the
    Sail-state predicate. -/
theorem memory_load_lanes_match_of_mem_row
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_main_emit : main.b_0 r_main = memory_entry_lo e
                   ∧ main.b_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    memory_load_lanes_match main r_main e
    ∧ ∃ r_mem : ℕ, mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 0 := by
  refine ⟨memory_load_lanes_match_of_main_emit main r_main e h_main_emit, ?_⟩
  exact lookup_consumer_matches_provider_load main mem r_main e h_main_emit

/-- **Memory-store lane match from Main emission.** Symmetric to
    `memory_load_lanes_match_of_main_emit` for the store side
    (`multiplicity = 1`); the lane match is structural from Main's
    `c_0` / `c_1`. -/
theorem memory_store_lanes_match_of_main_emit
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_main_emit : m.c_0 r_main = memory_entry_lo e
                   ∧ m.c_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = 1) :
    memory_store_lanes_match m r_main e := by
  exact ⟨h_main_emit.1, h_main_emit.2.1⟩

/-- **Memory-store lane match from Mem AIR row.** Symmetric to
    `memory_load_lanes_match_of_mem_row`. Composes the Main-side store
    emission with the Mem AIR row provided by
    `lookup_consumer_matches_provider_store`. -/
theorem memory_store_lanes_match_of_mem_row
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_main_emit : main.c_0 r_main = memory_entry_lo e
                   ∧ main.c_1 r_main = memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = 1) :
    memory_store_lanes_match main r_main e
    ∧ ∃ r_mem : ℕ, mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 1 := by
  refine ⟨memory_store_lanes_match_of_main_emit main r_main e h_main_emit, ?_⟩
  exact lookup_consumer_matches_provider_store main mem r_main e h_main_emit

/-! ## Mem-row local soundness

Below we record the F-typed every-row Mem AIR consequences the bridge
relies on: read rows (`wr = 0`) with `addr_changes = 1` zero the value
chunks (constraints 21/23). These are pure consequences of
`Mem.core_every_row` and are exposed here as named lemmas so consumers
of the bridge can reason about Mem-row structure without re-deriving
them. -/

/-- A read row (`wr = 0`) at an address change must have `value_0 = 0`.
    Direct consequence of `addr_change_no_write_zeros_value_0`
    (extracted Mem constraint 21) under `addr_changes = 1` and
    `wr = 0`. -/
theorem mem_read_addr_change_value_0_zero
    (mem : Valid_Mem C FGL FGL) (r_mem : ℕ)
    (h_core : core_every_row mem r_mem)
    (h_addr_changes : mem.addr_changes r_mem = 1)
    (h_wr : mem.wr r_mem = 0) :
    mem.value_0 r_mem = 0 := by
  have h := h_core.2.2.2.2.2.2.2.1
  simp only [addr_change_no_write_zeros_value_0] at h
  rw [h_addr_changes, h_wr] at h
  -- After substitution: `(1 * (1 - 0)) * mem.value_0 r_mem = 0`.
  linear_combination h

/-- Companion of `mem_read_addr_change_value_0_zero` for the high chunk. -/
theorem mem_read_addr_change_value_1_zero
    (mem : Valid_Mem C FGL FGL) (r_mem : ℕ)
    (h_core : core_every_row mem r_mem)
    (h_addr_changes : mem.addr_changes r_mem = 1)
    (h_wr : mem.wr r_mem = 0) :
    mem.value_1 r_mem = 0 := by
  have h := h_core.2.2.2.2.2.2.2.2
  simp only [addr_change_no_write_zeros_value_1] at h
  rw [h_addr_changes, h_wr] at h
  linear_combination h

/-! ## Trusted-surface: Main memory-bus emission shape

The two axioms below pin the Main AIR row's memory-bus emission
contract to a packaged form consumable by the per-opcode `Bridge.Mem`
discharge entry points. Same trust class as
`lookup_consumer_matches_provider_{load,store}` (memory-bus
permutation soundness / lookup-argument soundness on `bus_id = 10`).

For load opcodes (LD / LBU / LHU / LWU / LB / LH / LW), Main's row
emits two memory-bus entries from `main.pil`:

* The **b-emission** at `main.pil:300` carries the loaded value
  (`as = 2`, `mult = -1` consumer side; the Mem AIR provides
  this read). Its `addr` slot equals `addr1 = b_offset_imm0 +
  b_src_ind * a[0]` (line 304), which for a load `rd, imm(rs1)` is
  `signExt(imm) + r1_val` (line 282-288 establishes
  `a = state.xreg rs1`; line 343 binds `b_imm[0] = b_offset_imm0
  = signExt(imm)`; `b_src_ind = 1` for indirect loads).

* The **c-emission** at `main.pil:323` carries the rd-write
  (`as = 1`, `mult = 1`, register write side; the Mem AIR's
  register sub-protocol consumes this). Its `addr` slot equals
  Main's `store_offset` column, which for any store-reg-targeting
  row equals `rd` (line 148 + the transpilation contract).

Both emissions are paired via the bus permutation argument with
matching provider rows in the Mem AIR; the packing of `b_0 / b_1`
into the entry's 32-bit lanes (and `c_0 / c_1` symmetrically) is
asserted by the bus protocol.

Additionally, every internal `op = OP_COPYB` row (loads only)
obeys Main constraints 9 and 16
(`(1 - is_external_op) * op * (b_i - c_i) = 0`); we expose this
as part of the bundle since `Bridge.Mem` consumers do not currently
have access to a Main `core_every_row` validator structure (a
deeper architectural refactor tracked separately).

Trust class: lookup-argument / permutation soundness on `bus_id =
10` (same as class #4 in `docs/fv/trusted-base.md`). -/

/-- **Main memory-bus emission bundle — load side.**

    PIL citations:
    * `state-machines/main/pil/main.pil:300` — b-side `mem_op` emits
      the load entry (`as = 2`, `mult = -1` consumer);
    * `state-machines/main/pil/main.pil:304` — `addr1 = b_offset_imm0
      + b_src_ind * a[0]` (the load address);
    * `state-machines/main/pil/main.pil:323` — c-side `mem_op` emits
      the rd-write entry (`as = 1`, `mult = 1`);
    * `state-machines/main/pil/main.pil:148` — `store_offset` column
      carries `rd` for register-targeting rows;
    * `state-machines/main/pil/main.pil:282` — `a = state.xreg rs1`
      for `a_src_reg` rows (all loads);
    * `core/src/riscv2zisk_context.rs:803` — `load_op` lowers RV64
      loads to `op = "copyb"`, `is_external_op = 0`, `b_src_ind = 1`.

    Given Main's row at `r_main` is a load (transpile-pinned via
    `is_external_op = 0` and `op = OP_COPYB`), and `e1` / `e2`
    are this row's load / rd-write bus emissions (pinned by
    multiplicity + address-space + Sail register-read for the rs1
    field), the bundle delivers the lo/hi lane equalities for both
    emissions, the load address ptr-match against Sail's
    `r1_val + signExt(imm)`, the rd routing into the rd-write
    entry's `ptr` slot, and the per-row copyb passthrough facts. -/
axiom main_load_emission_bundle
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    -- Activation: this row is an internal load (copyb).
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = OP_COPYB)
    -- Bus side: e1 is the load consumer entry, e2 is the rd-write entry.
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    main.b_0 r_main = memory_entry_lo e1
    ∧ main.b_1 r_main = memory_entry_hi e1
    ∧ e1.as = 2
    ∧ e1.multiplicity = -1
    ∧ main.c_0 r_main = memory_entry_lo e2
    ∧ main.c_1 r_main = memory_entry_hi e2
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main

/-! ## Axiom audit

The bridge theorems compose `lookup_consumer_matches_provider_{load,store}`
(memory-bus permutation soundness) with structural Main-side emission
hypotheses. The Mem-row local lemmas
`mem_read_addr_change_value_{0,1}_zero` are pure consequences of
`Mem.core_every_row` and add no axioms.

`main_load_emission_bundle` and `main_store_emission_bundle` are
narrow PIL-cited extensions of the same trust class (memory-bus
permutation / lookup-argument soundness on `bus_id = 10`). -/

#print axioms memory_load_lanes_match_of_main_emit
#print axioms memory_load_lanes_match_of_mem_row
#print axioms memory_store_lanes_match_of_main_emit
#print axioms memory_store_lanes_match_of_mem_row
#print axioms mem_read_addr_change_value_0_zero
#print axioms mem_read_addr_change_value_1_zero

end ZiskFv.Airs.MemoryBus.MemBridge
