import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
ZisK memory-bus schema and Main ↔ memory-bus projections for loads/stores.

The Memory bus (identifier `MEMORY_ID = 10`, `zisk/pil/opids.pil:12`)
carries permutation entries of shape `[op, addr, mem_step, bytes, ...value]`
(`state-machines/mem/pil/mem.pil:524-527`). Main emits one entry per
source-b memory read (`main.pil:300`) and one per destination-c store
(`main.pil:323`).

This module projects the Main AIR's memory-read/write row into a
`Interaction.MemoryBusEntry` and provides the predicates used to match
against `bus_effect`'s memory branches (`BusEffect.lean:47-62`).
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteOf byteAt)


/-- The 64-bit memory value of a `MemoryBusEntry`, formed from the two
    32-bit chunks: `value_0 + value_1 * 2^32`. Matches the PIL emission
    shape (`mem.pil:436`, `...value` is a 2-element 32-bit chunk array).

    This is the field-level image of `U64.toBV` (which produces a
    `BitVec 64`). The two forms are related by the bridge lemma
    `memory_entry_toField_eq_toBV_toNat` below. -/
@[simp]
def memory_entry_toField (e : MemoryBusEntry FGL) : FGL :=
  e.value_0 + e.value_1 * 4294967296

/-- Low 32 bits (= chunk `value_0`) of a memory-bus entry, as FGL.
    Direct projection — matches PIL chunk shape. -/
@[simp]
def memory_entry_lo (e : MemoryBusEntry FGL) : FGL := e.value_0

/-- High 32 bits (= chunk `value_1`) of a memory-bus entry, as FGL.
    Direct projection — matches PIL chunk shape. -/
@[simp]
def memory_entry_hi (e : MemoryBusEntry FGL) : FGL := e.value_1

/-- The packed lane decomposition: the full 64-bit value equals
    `lo + hi * 2^32`. Trivial after the chunk-shape redesign — both
    sides reduce to `e.value_0 + e.value_1 * 2^32`. Retained for
    backwards compatibility with consumers that previously needed it
    to bridge byte-lane packs to chunk lanes. -/
lemma memory_entry_toField_lo_hi (e : MemoryBusEntry FGL) :
    memory_entry_toField e =
      memory_entry_lo e + memory_entry_hi e * 4294967296 := by
  simp only [memory_entry_toField, memory_entry_lo, memory_entry_hi]

/-- **Memory-bus entry matching.** Two `MemoryBusEntry`s match when
    every field agrees. Used in `Spec/LoadD.lean` to say: the Main
    row's memory-read projection equals the `bus_effect`-side
    memory-bus entry supplied by the caller. -/
@[simp]
def matches_memory_entry (a b : MemoryBusEntry FGL) : Prop :=
  a.multiplicity = b.multiplicity
  ∧ a.as = b.as
  ∧ a.ptr = b.ptr
  ∧ a.value_0 = b.value_0
  ∧ a.value_1 = b.value_1
  ∧ a.timestamp = b.timestamp

/-- **Memory-read lane hypotheses for LD.** The Main row's low/high `b`
    lanes (as FGL field elements) equal the low/high halves of the
    memory-bus entry's packed 8-byte value.

    This is the compositional hypothesis that the ZisK PIL memory-bus
    `permutation_assumes` discharges (`state-machines/mem/pil/mem.pil:526`):
    Main's `b[0]`/`b[1]` are the two 32-bit halves of the
    `[op=LOAD, addr, mem_step, bytes=8, ...value]` entry on the bus. -/
@[simp]
def memory_load_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.b_0 row = memory_entry_lo e
  ∧ m.b_1 row = memory_entry_hi e

/-- **Register-write-back lane hypothesis for LD.** The Main row's
    `c` lanes are what the memory-bus register-write entry carries —
    Main writes the loaded doubleword to register `rd` via `store_reg`
    (`main.pil:316-319,323-328`). -/
@[simp]
def register_write_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.c_0 row = memory_entry_lo e
  ∧ m.c_1 row = memory_entry_hi e

/-! ## Store-side (SD) projections.

These predicates are the write-side mirror of `memory_load_lanes_match`.
SD reads `b` from register rs2 (the value) and writes it to memory via
`store_ind` (`main.pil:314-321`): the *proved* memory-bus entry carries
the store value's 8 bytes at `as = 2, multiplicity = 1`.

Because constraint 9/16 still force `c = b` for `is_external_op = 0,
op = OP_COPYB = 1`, the store-side lane match is equally expressible
against `b` or `c`. We expose the `c`-side form (symmetric with LD's
`register_write_lanes_match`) so the spec theorem composes uniformly. -/

/-- **Memory-write lane hypotheses for SD.** The Main row's `c` lanes
    equal the low/high halves of the memory-bus *write* entry's packed
    8-byte store value.

    Symmetric analogue of `memory_load_lanes_match`:
    * LD reads the memory entry (`mult = -1, as = 2`) and matches it
      against `b`;
    * SD writes the memory entry (`mult = 1, as = 2`) with the same
      lane-packing, matched against `c` (equivalently `b`, via
      constraint 9/16). -/
@[simp]
def memory_store_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.c_0 row = memory_entry_lo e
  ∧ m.c_1 row = memory_entry_hi e

/-- **Register-read lane hypothesis (rs1 / a-lanes).** The Main row's
    `a` lanes equal the low/high halves of the register-read entry
    that provides the address-base register rs1 (`ptr = 4 * rs1,
    multiplicity = -1, as = 1`). This mirrors the `register_read_rs2_lanes_match`
    predicate for the `b` lanes and is the direct analogue for instructions
    (e.g. LD, SD, JALR) that read rs1 from `a[0]`/`a[1]`.

    `register_read_rs1_lanes_match_of_bus_emission` in
    `Airs/MemoryBus/LaneMatch.lean` promotes this from a hypothesis to
    a theorem derived from the structural bus-entry predicate
    `matches_memory_entry`. -/
@[simp]
def register_read_rs1_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.a_0 row = memory_entry_lo e
  ∧ m.a_1 row = memory_entry_hi e

/-- **Register-read lane hypothesis for SD (rs2 value).** The Main
    row's `b` lanes equal the low/high halves of the register-read
    entry that provides the SD store value (`ptr = 4 * rs2,
    multiplicity = -1, as = 1`). Symmetric to LD's register-read-of-rs1;
    the load fetched *memory* into `b`, the store fetches *register rs2*
    into `b`. -/
@[simp]
def register_read_rs2_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.b_0 row = memory_entry_lo e
  ∧ m.b_1 row = memory_entry_hi e

/-! ## store_pc=1 lane match (JAL / JALR / AUIPC)

For `store_pc = 1` opcodes the destination register receives `pc +
jmp_offset2` (the link register or AUIPC's `pc + imm`). The PIL
`store_value` formula at `zisk/state-machines/main/pil/main.pil:311-312`
is uniform across `store_pc`:

```
store_value[0] = store_pc * (pc + jmp_offset2 - c[0]) + c[0];
store_value[1] = (1 - store_pc) * c[1];
```

When `store_pc = 1`, this collapses to `store_value[0] = pc +
jmp_offset2` and `store_value[1] = 0`. When `store_pc = 0` it
collapses to `store_value[0] = c[0]` and `store_value[1] = c[1]`,
recovering `register_write_lanes_match`.

The two predicates `store_pc_lanes_match_lo` / `_hi` encode the
*uniform* PIL formulas — they are valid for any `store_pc ∈ {0,1}`,
and so generalize `register_write_lanes_match` rather than parallel
it. The hi-half formula `(1 - store_pc) * c[1]` is the verbatim PIL
expression — there is no separate "hi-bytes projection" for
`pc + jmp_offset2`; for `store_pc = 1`, the hi half is *zero* by PIL
construction. (PC is a 32-bit column in Main; `pc + jmp_offset2` is
a single FGL value carried entirely in the lo lane.) -/

/-- **store_pc lo-lane match.** The memory-bus entry's lo half equals
    the PIL `store_value[0]` formula `store_pc * (pc + jmp_offset2 - c_0)
    + c_0`. Uniform in `store_pc`:

    * `store_pc = 1` (JAL / JALR / AUIPC): collapses to
      `memory_entry_lo e = pc + jmp_offset2`.
    * `store_pc = 0`: collapses to `memory_entry_lo e = c_0` —
      identical to `register_write_lanes_match`'s lo conjunct (with
      sides flipped).

    Trust class: same as `register_write_lanes_match` —
    memory-bus permutation soundness. The store-side lane match for
    register writes is derived in `LaneMatch.lean` from the
    `memory_bus_register_write_perm_sound` axiom (and an extension for
    the `store_pc = 1` case, see file). -/
@[simp]
def store_pc_lanes_match_lo
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  memory_entry_lo e =
    m.store_pc row * (m.pc row + m.jmp_offset2 row - m.c_0 row) + m.c_0 row

/-- **store_pc hi-lane match.** The memory-bus entry's hi half equals
    the PIL `store_value[1]` formula `(1 - store_pc) * c_1`. Uniform
    in `store_pc`:

    * `store_pc = 1` (JAL / JALR / AUIPC): collapses to
      `memory_entry_hi e = 0`. (The high 32 bits of the link-register
      / AUIPC result are zero in ZisK because Main's `pc` is a
      `bits(32)` column and `jmp_offset2` is added at the FGL level —
      the PIL deliberately routes the entire `pc + jmp_offset2` sum
      through the lo lane; the bus-bytes byte-decomposition handles
      any boundary into the upper bytes.)
    * `store_pc = 0`: collapses to `memory_entry_hi e = c_1` —
      identical to `register_write_lanes_match`'s hi conjunct.

    The hi-half formula is the verbatim PIL expression at
    `main.pil:312` — there is no carry-decomposition because the PIL
    does not split `pc + jmp_offset2` across hi/lo bytes; the lo
    entry carries the full sum.

    Trust class: same as `store_pc_lanes_match_lo`. -/
@[simp]
def store_pc_lanes_match_hi
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  memory_entry_hi e = (1 - m.store_pc row) * m.c_1 row

/-! ## Bridge to `U64.toBV` for register-write values

`memory_entry_toField_eq_toBV_toNat` bridges from
`memory_entry_toField` (chunk-shape field value) to `U64.toBV`
(`BitVec 64` register-write value), using the chunk-pack identity
`bytes_of_chunk_packing` to decompose each chunk into 4 bytes for the
byte-addressed Sail memory model. Direct consequence of
`Channels/MemoryBusBytes.lean`'s `u64_toBV_chunks_eq_ofNat_fgl_val`. -/

/-- **Entry chunk ranges.** Each of the 2 chunks of a memory-bus entry
    has `.val < 2^32` (discharged by the PIL range-check bus, which
    enforces `value[0], value[1] ∈ [0, 2^32)` per `mem.pil`). -/
@[simp]
def memory_entry_chunks_in_range (e : MemoryBusEntry FGL) : Prop :=
  e.value_0.val < 4294967296 ∧ e.value_1.val < 4294967296

/-- **No-wraparound bound on the packed entry.** The Nat chunk-sum
    `value_0.val + value_1.val * 2^32` is below `GL_prime`.

    Under `memory_entry_chunks_in_range`, the chunk-sum is at most
    `2^64 - 1`, which *can* exceed `GL_prime = 2^64 - 2^32 + 1` in the
    "high-register" range. Callers discharge this either
    architecturally (e.g. for 32-bit ops the top chunk is zero)
    or from the concrete product range. -/
@[simp]
def memory_entry_packed_no_wrap (e : MemoryBusEntry FGL) : Prop :=
  e.value_0.val + e.value_1.val * 4294967296 < GL_prime

/-- **Bridge: `U64.toBV` of entry's byte projections equals
    `BitVec.ofNat 64 (memory_entry_toField e).val`.** Given chunk
    ranges and the no-wraparound bound, the 8 byte projections of the
    entry's two 32-bit chunks (`byteAt e 0..7`) — fed through `U64.toBV`
    (which coerces each `FGL` byte to `BitVec 8` via the `mod 256`
    instance) — produce the same `BitVec 64` as `BitVec.ofNat 64`
    applied to the chunk-pack field value's `.val`. -/
lemma memory_entry_toField_eq_toBV_toNat
    (e : MemoryBusEntry FGL)
    (h_range : memory_entry_chunks_in_range e)
    (h_no_wrap : memory_entry_packed_no_wrap e) :
    U64.toBV #v[(byteAt e 0 : BitVec 8), (byteAt e 1 : BitVec 8),
                (byteAt e 2 : BitVec 8), (byteAt e 3 : BitVec 8),
                (byteAt e 4 : BitVec 8), (byteAt e 5 : BitVec 8),
                (byteAt e 6 : BitVec 8), (byteAt e 7 : BitVec 8)]
    = BitVec.ofNat 64 (memory_entry_toField e).val := by
  obtain ⟨h_v0, h_v1⟩ := h_range
  simp only [memory_entry_packed_no_wrap] at h_no_wrap
  simp only [memory_entry_toField]
  -- Unfold byteAt for indices 0..7: 0..3 from value_0, 4..7 from value_1.
  show U64.toBV
        #v[(byteOf e.value_0 0 : BitVec 8), (byteOf e.value_0 1 : BitVec 8),
           (byteOf e.value_0 2 : BitVec 8), (byteOf e.value_0 3 : BitVec 8),
           (byteOf e.value_1 0 : BitVec 8), (byteOf e.value_1 1 : BitVec 8),
           (byteOf e.value_1 2 : BitVec 8), (byteOf e.value_1 3 : BitVec 8)]
      = BitVec.ofNat 64 (e.value_0 + e.value_1 * 4294967296 : FGL).val
  exact ZiskFv.Channels.MemoryBusBytes.u64_toBV_chunks_eq_ofNat_fgl_val
    e.value_0 e.value_1 h_v0 h_v1 h_no_wrap

end ZiskFv.Airs.MemoryBus
