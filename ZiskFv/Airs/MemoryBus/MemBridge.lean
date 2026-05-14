import Mathlib
import LeanRV64D

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
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
lemma memory_load_lanes_match_of_main_emit
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
lemma memory_load_lanes_match_of_mem_row
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
lemma mem_read_addr_change_value_0_zero
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
lemma mem_read_addr_change_value_1_zero
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

/-- **Main memory-bus emission bundle — signed-load side.**

    Same emission shape as `main_load_emission_bundle`, but for the
    sign-extended-load family (LB / LH / LW). The activation pin is
    different: these rows are *external* (`is_external_op = 1`) and
    carry `op ∈ {OP_SIGNEXTEND_B, OP_SIGNEXTEND_H, OP_SIGNEXTEND_W}`
    rather than `op = OP_COPYB`. The Main row still emits the same
    pair of memory-bus entries — `b`-side load consumer (`as = 2`,
    `mult = -1`) and `c`-side rd-write (`as = 1`, `mult = 1`) — so
    the lane equalities, ptr-match against `r1_val + signExt(imm)`,
    and rd routing are identical in shape to the copyb load case.

    The copyb passthrough facts (`internal_op1_copies_b{0,1}`,
    constraints 9 / 16) are absent here: those are conditioned on
    `(1 - is_external_op) * op = 1`, which is zero for sext-load rows
    (`is_external_op = 1`). The rd value is grounded downstream via
    the BinaryExtension AIR's per-byte lookups
    (`Circuit/SextLoadBridge.lean`), not via Main's b → c copy.

    PIL citations (same as `main_load_emission_bundle`):
    * `state-machines/main/pil/main.pil:300` — b-side `mem_op`;
    * `state-machines/main/pil/main.pil:181` — `addr1 =
      b_offset_imm0 + b_src_ind * a[0]` for external rows;
    * `state-machines/main/pil/main.pil:323` — c-side `mem_op`;
    * `state-machines/main/pil/main.pil:148` — `store_offset = rd`;
    * `state-machines/main/pil/main.pil:344` — `b_imm[0] =
      b_offset_imm0`;
    * `core/src/riscv2zisk_context.rs` — `load_op` for LB / LH / LW
      lowers to `op = "signextend_{b,h,w}"`, `is_external_op = 1`,
      `b_src_ind = 1` (analogous to the copyb load path but routed
      through BinaryExtension for sign-extension).

    Trust class #4 (memory-bus permutation / lookup-argument
    soundness on `bus_id = 10`) — same class as
    `main_load_emission_bundle` and
    `lookup_consumer_matches_provider_{load,store}`. -/
axiom main_sext_load_emission_bundle
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (op_code : FGL)
    -- Activation: this row is an external sext-load row.
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = op_code)
    (h_op_sext : op_code = OP_SIGNEXTEND_B
                  ∨ op_code = OP_SIGNEXTEND_H
                  ∨ op_code = OP_SIGNEXTEND_W)
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

/-- **Main memory-bus emission bundle — store_pc=1 register write.**

    For the JAL / JALR / AUIPC archetypes, Main's row emits a single
    memory-bus register-write entry (`as = 1`, `mult = 1`,
    `store_pc = 1`, `store_reg = 1`). The PIL `store_value` formula
    at `main.pil:311-312` collapses under `store_pc = 1` to
    `(pc + jmp_offset2, 0)`; equivalently, the uniform
    `store_pc_lanes_match_{lo,hi}` predicates (formulas
    `store_pc * (pc + jmp_offset2 - c_0) + c_0` and
    `(1 - store_pc) * c_1`) hold for both `store_pc = 0` and
    `store_pc = 1` rows.

    The activation pins are parameterized via an `op_code` operand:
    JAL / AUIPC have `op = OP_FLAG` (`is_external_op = 0`); JALR has
    `op = OP_COPYB` (`is_external_op = 0`). This is the only
    `store_pc = 1` family in RV64IM (the only callers of the
    `store_pc_lanes_match_*` predicates), so the bundle's
    `op_code ∈ {OP_FLAG, OP_COPYB}` disjunct covers it.

    PIL citations:
    * `state-machines/main/pil/main.pil:311-312` — `store_value[0/1]`
      formulas in terms of `store_pc`, `pc`, `jmp_offset2`, `c_0`, `c_1`;
    * `state-machines/main/pil/main.pil:323` — c-side `mem_op` emits
      the rd-write entry under `store_reg = 1`;
    * `state-machines/main/pil/main.pil:148` — `store_offset = rd`
      for register-targeting rows;
    * `state-machines/main/pil/main.pil:473` — `store_pc * (1 - store_pc) = 0`
      (booleanity of `store_pc`).

    Trust class #4 (memory-bus permutation / lookup-argument
    soundness on `bus_id = 10`) — same class as
    `main_load_emission_bundle`, `main_sext_load_emission_bundle`,
    and the `memory_bus_register_write_perm_sound{,_store_pc}`
    axioms in `LaneMatch.lean`. The bundle differs only in
    skipping the Mem-side consumer-row machinery: callers
    (the `Bridge.ControlFlow.{jal,jalr,auipc}_discharge_lanes`
    entry points) consume the lane equalities directly. -/
axiom main_store_pc_emission_bundle
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_rd : MemoryBusEntry FGL)
    (op_code : FGL)
    -- Activation: this row is an internal `store_pc = 1` register-write
    -- (JAL / AUIPC `op = OP_FLAG`, or JALR `op = OP_COPYB`).
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = op_code)
    (h_op_disj : op_code = ZiskFv.Trusted.OP_FLAG ∨ op_code = ZiskFv.Trusted.OP_COPYB)
    -- Bus side: e_rd is the rd-write entry.
    (h_e_rd_mult : e_rd.multiplicity = 1) (h_e_rd_as_val : e_rd.as.val = 1) :
    ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo main r_main e_rd
    ∧ ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi main r_main e_rd

/-- **Main memory-bus emission bundle — external arithmetic rd-write.**

    For every Main row in the MUL / DIV family
    (`is_external_op = 1`, `op ∈ {OP_MULU..OP_MUL_W, OP_DIVU..OP_REM_W}`,
    bus literals `0xb0..0xbf` per `zisk/pil/operations.pil:71-86`),
    the rd-write memory-bus entry `e_rd` (`mult = 1`, `as = 1`)
    satisfies the byte-pack lane equalities tying `e_rd`'s
    byte-decomposition `x0..x7` to Main's `c_0` / `c_1` 32-bit lanes.

    On these rows `store_pc = 0` (ZisK's ROM assigns `store_pc = 1`
    only to JAL/JALR/AUIPC); the PIL `store_value` formula at
    `main.pil:311-312` collapses under `store_pc = 0` to
    `(c_0, c_1)`, so the rd-write entry's byte-decomposition packs
    directly to `(c_0, c_1)`. Every byte cell carries `bits(8)`
    (`main.pil:78`), so the byte-range bus discharges the per-byte
    range and the pack equation lifts to `ℕ` cleanly.

    PIL citations:
    * `state-machines/main/pil/main.pil:311-312` — `store_value[0/1]`
      formulas; for `store_pc = 0` they reduce to `c[0]` / `c[1]`;
    * `state-machines/main/pil/main.pil:323` — c-side `mem_op` emits
      the rd-write entry (`as = 1`, `mult = 1`);
    * `state-machines/main/pil/main.pil:148` — `store_offset = rd`
      for register-targeting rows;
    * `state-machines/main/pil/main.pil:78` — `col witness bits(8)
      x[BYTES]` (byte-range invariant on Main's emission lanes);
    * `state-machines/main/pil/main.pil:473` — `store_pc` booleanity;
    * ROM-side: ZisK's arithmetic opcodes (MUL/DIV family) are
      assigned `store_pc = 0` / `store_reg = 1` (no PC-write side
      effect; rd is a general-purpose register).

    Conclusion shape: byte-pack lane equalities in **nat form**
    (consumed directly by `equiv_DIV_from_trust` / `equiv_MUL` etc.
    as the `h_byte_lo` / `h_byte_hi` promise hypotheses); plus the
    rd-routing equation matching the existing `*_load_emission_bundle`
    family. Byte ranges (each `e_rd.xi.val < 256`) are NOT included
    here — callers obtain them from `memory_bus_entry_byte_range_perm_sound`
    (class #5b) so the bundle stays factored.

    Trust class #4 (memory-bus permutation / lookup-argument
    soundness on `bus_id = 10`) — same class as
    `main_load_emission_bundle`, `main_sext_load_emission_bundle`,
    and `main_store_pc_emission_bundle`. -/
axiom main_external_arith_emission_bundle
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_rd : MemoryBusEntry FGL)
    (rd : BitVec 5)
    (op_code : FGL)
    -- Activation: external arithmetic (MUL / DIV family).
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = op_code)
    (h_op_arith : op_code = ZiskFv.Trusted.OP_MULU
                  ∨ op_code = ZiskFv.Trusted.OP_MULUH
                  ∨ op_code = ZiskFv.Trusted.OP_MULSUH
                  ∨ op_code = ZiskFv.Trusted.OP_MUL
                  ∨ op_code = ZiskFv.Trusted.OP_MULH
                  ∨ op_code = ZiskFv.Trusted.OP_MUL_W
                  ∨ op_code = ZiskFv.Trusted.OP_DIVU
                  ∨ op_code = ZiskFv.Trusted.OP_REMU
                  ∨ op_code = ZiskFv.Trusted.OP_DIV
                  ∨ op_code = ZiskFv.Trusted.OP_REM
                  ∨ op_code = ZiskFv.Trusted.OP_DIVU_W
                  ∨ op_code = ZiskFv.Trusted.OP_REMU_W
                  ∨ op_code = ZiskFv.Trusted.OP_DIV_W
                  ∨ op_code = ZiskFv.Trusted.OP_REM_W)
    -- Bus side: e_rd is the rd-write entry.
    (h_e_rd_mult : e_rd.multiplicity = 1) (h_e_rd_as_val : e_rd.as.val = 1) :
    -- Byte-pack lane equalities in nat form (the c_0 / c_1 Main
    -- columns are < 2^32 by `bits(32)` register-bus annotation —
    -- see `main.pil:73` `col witness bits(32) c[RC]` — so the
    -- pack equation lifts to ℕ without modular reduction).
    e_rd.x0.val + e_rd.x1.val * 256
        + e_rd.x2.val * 65536 + e_rd.x3.val * 16777216
      = (main.c_0 r_main).val
    ∧ e_rd.x4.val + e_rd.x5.val * 256
        + e_rd.x6.val * 65536 + e_rd.x7.val * 16777216
      = (main.c_1 r_main).val
    -- rd routing: `e_rd.ptr` is the destination register (PIL
    -- `store_offset = rd` plus `store_offset → ptr` on `as = 1`).
    ∧ (Transpiler.wrap_to_regidx e_rd.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e_rd.ptr).val

/-- **Main memory-bus emission bundle — store (`as = 2`) side, SD width.**

    For every Main row in the SD family (`is_external_op = 0`,
    `op = OP_COPYB`, `store_ind = 1`, `store_pc = 0`, `ind_width = 8`),
    the store memory-bus entry `e_st` (`as = 2`, `mult = 1`)
    carries `xreg rs2`'s 8 byte cells — and the store address slot
    is `xreg rs1 + signExt(imm)`. The bundle exposes these in
    byte-extracted (BitVec 8) form, paralleling how
    `main_external_arith_emission_bundle` exposes the rd-write
    entry's lanes in byte-packed nat form for MUL/DIV.

    Derivation chain folded into the axiom (each step PIL-cited):

    1. **Lane equality.** `main.pil:323` emits the store entry with
       `value: store_value`; `main.pil:311-312` with `store_pc = 0`
       collapses `store_value` to `(c_0, c_1)`. So
       `memory_entry_lo e_st = c_0 r_main`,
       `memory_entry_hi e_st = c_1 r_main`.
    2. **Copyb passthrough.** Main constraints 9/16
       (`(1 - is_external_op) * op * (b_i - c_i) = 0`) under
       `is_external_op = 0, op = OP_COPYB = 1` force
       `c_0 = b_0` and `c_1 = b_1`.
    3. **Transpile.** `transpile_SD` (`Transpiler.lean:682`) pins
       `m.b_0 = lane_lo r2_val`, `m.b_1 = lane_hi r2_val` on the
       Sail-side state's `xreg rs2 = r2_val` register read.
    4. **Byte-range bus.** `main.pil:78` declares
       `col witness bits(8) x[BYTES]` on the memory-bus entry's
       byte lanes, range-checking each to `[0, 256)`; this is the
       same range bus exposed via
       `memory_bus_entry_byte_range_perm_sound`.
    5. **Base-256 unique decomposition.** With both halves'
       packings equal (via 1+2+3) and per-byte ranges (via 4),
       each `e_st.xi` is the corresponding byte slot of `r2_val`,
       i.e. `(e_st.xi : BitVec 8) = BitVec.extractLsb (8(i+1)-1) (8i) r2_val`.
    6. **Store address.** `main.pil:323`'s `addr: addr2` slot,
       with `store_ind = 1` (from `riscv2zisk_context.rs:841`),
       sets `addr2 = a_offset_imm0 + a_src_ind * a[0]` reducing
       on `a_src_reg = 1` rows (the SD case per
       `riscv2zisk_context.rs:837`) to
       `a + signExt(imm) = xreg rs1 + signExt(imm)`. So
       `e_st.ptr.toNat = r1_val.toNat + signExt(imm).toNat`.

    The axiom requires the **transpile-derived lane equalities**
    `main.b_0 = lane_lo r2_val ∧ main.b_1 = lane_hi r2_val` (and
    similarly for `a_0/a_1 ↔ r1_val`) as **caller-supplied
    hypotheses** rather than re-deriving them — keeping the trust
    surface tied to the transpile axiom rather than duplicating
    its content. The same applies to the copyb activation pins
    (`is_external_op = 0`, `op = OP_COPYB`) which the caller pins
    via `transpile_SD`'s preconditions.

    PIL citations (consolidated):
    * `state-machines/main/pil/main.pil:323` — c-side `mem_op`
      emits the store entry (`as = 2`, `mult = 1`);
    * `state-machines/main/pil/main.pil:311-312` — `store_value`
      `(c_0, c_1)` under `store_pc = 0`;
    * `state-machines/main/pil/main.pil:78` — `bits(8)` byte
      witness on the memory-bus entry lanes;
    * `state-machines/main/pil/main.pil:473` — `store_pc`
      booleanity (pinning value collapse);
    * Main constraints 9 / 16 (`internal_op1_copies_b{0,1}`)
      — copyb passthrough;
    * `core/src/riscv2zisk_context.rs:828-845` — `fn store_op`
      with `op = "copyb"`, `ind_width = 8` for SD,
      `store_ind = 1`, `src_a = reg rs1`, `src_b = reg rs2`.

    Trust class #4 (memory-bus permutation / lookup-argument
    soundness on `bus_id = 10`, packaged with byte-range bus
    `bus_id` consequences) — same class as
    `main_load_emission_bundle`, `main_sext_load_emission_bundle`,
    `main_store_pc_emission_bundle`, and
    `main_external_arith_emission_bundle`. The byte-form
    conclusion is the only difference; the lane-form (`c_i =
    memory_entry_*`) and ptr-form facts are the same as
    `main_load_emission_bundle`'s for the b-side.

    Width specialization: SD only (`ind_width = 8`, all 8 byte
    lanes meaningful). SB/SH/SW will need their own width-specialized
    bundles in `Compliance/FromTrust/Sb.lean` / etc., as their high
    byte lanes are zero-padded by the bus's `ind_width` selector. -/
axiom main_store_emission_bundle_sd
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64) (imm : BitVec 12)
    -- Activation: internal store row (copyb passthrough).
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = OP_COPYB)
    -- Bus side: e_st is the store entry (`as = 2`, `mult = 1`).
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    -- Transpile-pinned Sail-state lane equalities (from `transpile_SD`).
    (h_a_lo : main.a_0 r_main = ZiskFv.Trusted.lane_lo r1_val)
    (h_a_hi : main.a_1 r_main = ZiskFv.Trusted.lane_hi r1_val)
    (h_b_lo : main.b_0 r_main = ZiskFv.Trusted.lane_lo r2_val)
    (h_b_hi : main.b_1 r_main = ZiskFv.Trusted.lane_hi r2_val) :
    -- ptr-match: store address = xreg rs1 + signExt(imm).
    -- BitVec-sum form (matches `equiv_SD`'s `h_ptr_match`); the Sail
    -- side's `sd_state_assumptions` pins the sum below the address
    -- space size, so no wraparound at this level.
    e_st.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat
    -- 8 byte extracts: each e_st.xi is the i-th byte of r2_val.
    ∧ (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val
    ∧ (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 r2_val
    ∧ (e_st.x2 : BitVec 8) = BitVec.extractLsb 23 16 r2_val
    ∧ (e_st.x3 : BitVec 8) = BitVec.extractLsb 31 24 r2_val
    ∧ (e_st.x4 : BitVec 8) = BitVec.extractLsb 39 32 r2_val
    ∧ (e_st.x5 : BitVec 8) = BitVec.extractLsb 47 40 r2_val
    ∧ (e_st.x6 : BitVec 8) = BitVec.extractLsb 55 48 r2_val
    ∧ (e_st.x7 : BitVec 8) = BitVec.extractLsb 63 56 r2_val

/-! ## Narrow-store emission bundles — RMW high-byte preservation

For sub-doubleword stores (SB / SH / SW), Main emits the same memory-bus
entry shape as SD (`as = 2`, `mult = 1`, 8 byte cells `x0..x7`) but only
the low `N` lanes are pinned to the store-value bytes — the high `8-N`
lanes carry the **pre-existing memory contents** at those addresses,
restored by the MemAlign read-modify-write protocol
(`mem_align.pil:28-37` and `mem_align.pil:50-61` for the 2 RMW
sub-programs; `mem_align.pil:189` for the bus permutation).

The Main-side emission shape uses
`bytes: store_ind * (ind_width - 8) + 8` (`main.pil:326`) to mark the
live byte count; on the prove side the same `(ptr, x0..x7)` tuple is
matched by a MemAlign row whose RMW protocol restores the high
`8 - ind_width` bytes from the current memory word.

Each width gets its own emission-bundle axiom delivering the **byte-level
RMW promise**: ptr-match against `xreg rs1 + signExt(imm)`, low-N-byte
equalities to `BitVec.extractLsb` of `r2_val`, and high-(8-N)-byte
RMW preservations against the input Sail state's `state.mem`. The
canonical `equiv_SB / SH / SW` use a single bundled `h_mem_eq`
hypothesis; the byte-level form here lets the discharge wrapper
derive `h_mem_eq` in pure Lean using HashMap insert-equals-self
reasoning.

PIL citations (shared across the 3 axioms):
* `state-machines/main/pil/main.pil:323` — c-side `mem_op` emits
  the store entry (`as = 2`, `mult = 1`);
* `state-machines/main/pil/main.pil:311-312` — `store_value =
  (c_0, c_1)` under `store_pc = 0`;
* `state-machines/main/pil/main.pil:78` — `bits(8) x[BYTES]`
  byte-range witnesses on the memory-bus emission lanes;
* `state-machines/main/pil/main.pil:326` — `bytes: store_ind *
  (ind_width - 8) + 8` pinning the live byte count to `ind_width`
  on store rows (`store_ind = 1`);
* `state-machines/mem/pil/mem_align.pil:28-37` — single-word RMW
  write sub-program (sub-doubleword stores fall here);
* `state-machines/mem/pil/mem_align.pil:189` — MemAlign
  permutation-soundness against `bus_id = 10`;
* `core/src/riscv2zisk_context.rs:828-845` — `fn store_op`
  lowering RV64 SB/SH/SW with `op = "copyb"`, `ind_width ∈ {1, 2, 4}`,
  `store_ind = 1`, `src_a = reg rs1`, `src_b = reg rs2`.

Trust class **#4** (memory-bus permutation / lookup-argument
soundness on `bus_id = 10`) — same class as
`main_store_emission_bundle_sd` and the load-side family. The
RMW preservation clause is grounded by the **MemAlign provider**'s
write protocol (an `as = 2`, `mult = -1` consume against the same
ptr/timestamp slot that re-emits the original high bytes); this is
captured by the same permutation handshake (`bus_id = 10`) that
delivers the SD bundle's lane equalities.
-/

/-- **Main memory-bus emission bundle — store side, SB width (1 byte).**

    For every Main row in the SB store family (`is_external_op = 0`,
    `op = OP_COPYB`, `ind_width = 1`, `store_ind = 1`), the store
    memory-bus entry `e_st` (`as = 2`, `mult = 1`) carries:
    * the **low byte** `x0` of `xreg rs2` at the store address,
    * the **high 7 bytes** `x1..x7` are the **pre-existing memory
      contents** at `ptr+1..ptr+7` (restored by the MemAlign RMW
      protocol).

    Trust class #4. Width specialization: SB only. -/
axiom main_store_emission_bundle_sb
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1_val r2_val : BitVec 64) (imm : BitVec 12)
    -- Activation: internal store row (copyb passthrough).
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = OP_COPYB)
    -- Width pin: SB = 1-byte store.
    (h_ind_width : main.ind_width r_main = 1)
    -- Bus side: e_st is the store entry (`as = 2`, `mult = 1`).
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    -- Transpile-pinned Sail-state lane equalities (from `transpile_SB`).
    (h_a_lo : main.a_0 r_main = ZiskFv.Trusted.lane_lo r1_val)
    (h_a_hi : main.a_1 r_main = ZiskFv.Trusted.lane_hi r1_val)
    (h_b_lo : main.b_0 r_main = ZiskFv.Trusted.lane_lo r2_val)
    (h_b_hi : main.b_1 r_main = ZiskFv.Trusted.lane_hi r2_val) :
    -- ptr-match: store address = xreg rs1 + signExt(imm).
    e_st.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat
    -- Low byte: e_st.x0 is the low byte of r2_val.
    ∧ (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val
    -- High bytes: RMW preservation — bytes 1..7 equal pre-store memory.
    ∧ state.mem[e_st.ptr.toNat + 1]? = some (e_st.x1 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 2]? = some (e_st.x2 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 3]? = some (e_st.x3 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 4]? = some (e_st.x4 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 5]? = some (e_st.x5 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 6]? = some (e_st.x6 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 7]? = some (e_st.x7 : BitVec 8)

/-- **Main memory-bus emission bundle — store side, SH width (2 bytes).**

    SH analog of `main_store_emission_bundle_sb`: 2 low bytes match
    `r2_val`'s low 16 bits; 6 high bytes are RMW-preserved against
    `state.mem`. Trust class #4. -/
axiom main_store_emission_bundle_sh
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1_val r2_val : BitVec 64) (imm : BitVec 12)
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = OP_COPYB)
    (h_ind_width : main.ind_width r_main = 2)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_a_lo : main.a_0 r_main = ZiskFv.Trusted.lane_lo r1_val)
    (h_a_hi : main.a_1 r_main = ZiskFv.Trusted.lane_hi r1_val)
    (h_b_lo : main.b_0 r_main = ZiskFv.Trusted.lane_lo r2_val)
    (h_b_hi : main.b_1 r_main = ZiskFv.Trusted.lane_hi r2_val) :
    e_st.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat
    ∧ (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val
    ∧ (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 r2_val
    ∧ state.mem[e_st.ptr.toNat + 2]? = some (e_st.x2 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 3]? = some (e_st.x3 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 4]? = some (e_st.x4 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 5]? = some (e_st.x5 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 6]? = some (e_st.x6 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 7]? = some (e_st.x7 : BitVec 8)

/-- **Main memory-bus emission bundle — store side, SW width (4 bytes).**

    SW analog: 4 low bytes match `r2_val`'s low 32 bits; 4 high bytes
    are RMW-preserved against `state.mem`. Trust class #4. -/
axiom main_store_emission_bundle_sw
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1_val r2_val : BitVec 64) (imm : BitVec 12)
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = OP_COPYB)
    (h_ind_width : main.ind_width r_main = 4)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_a_lo : main.a_0 r_main = ZiskFv.Trusted.lane_lo r1_val)
    (h_a_hi : main.a_1 r_main = ZiskFv.Trusted.lane_hi r1_val)
    (h_b_lo : main.b_0 r_main = ZiskFv.Trusted.lane_lo r2_val)
    (h_b_hi : main.b_1 r_main = ZiskFv.Trusted.lane_hi r2_val) :
    e_st.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat
    ∧ (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val
    ∧ (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 r2_val
    ∧ (e_st.x2 : BitVec 8) = BitVec.extractLsb 23 16 r2_val
    ∧ (e_st.x3 : BitVec 8) = BitVec.extractLsb 31 24 r2_val
    ∧ state.mem[e_st.ptr.toNat + 4]? = some (e_st.x4 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 5]? = some (e_st.x5 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 6]? = some (e_st.x6 : BitVec 8)
    ∧ state.mem[e_st.ptr.toNat + 7]? = some (e_st.x7 : BitVec 8)

/-! ## Axiom audit

The bridge theorems compose `lookup_consumer_matches_provider_{load,store}`
(memory-bus permutation soundness) with structural Main-side emission
hypotheses. The Mem-row local lemmas
`mem_read_addr_change_value_{0,1}_zero` are pure consequences of
`Mem.core_every_row` and add no axioms.

`main_load_emission_bundle`, `main_sext_load_emission_bundle`,
`main_store_pc_emission_bundle`, `main_external_arith_emission_bundle`,
and `main_store_emission_bundle_sd` are narrow PIL-cited
extensions of the same trust class (memory-bus permutation /
lookup-argument soundness on `bus_id = 10`). -/

#print axioms memory_load_lanes_match_of_main_emit
#print axioms memory_load_lanes_match_of_mem_row
#print axioms mem_read_addr_change_value_0_zero
#print axioms mem_read_addr_change_value_1_zero

end ZiskFv.Airs.MemoryBus.MemBridge
