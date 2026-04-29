import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main

/-!
ZisK memory-bus schema and Main ↔ memory-bus projection for loads.

The Memory bus (identifier `MEMORY_ID = 10`, `zisk/pil/opids.pil:12`)
carries permutation entries of shape `[op, addr, mem_step, bytes, ...value]`
(`state-machines/mem/pil/mem.pil:524-527`). Main emits one entry per
source-b memory read (`main.pil:300`) and one per destination-c store
(`main.pil:323`).

For the first archetype that exercises this infrastructure — LD (A3) —
we need to project the Main AIR's memory-read row into a
`Interaction.MemoryBusEntry` and match against `bus_effect`'s memory-read
branch at `BusEffect.lean:47-62`.

**Scope note.** This module is the **A3 analogue** of
`Airs/OperationBus.lean` (which handles the operation-bus match for
ADD). It is intentionally lean: only the predicates the LD spec needs.
A4 (SD) will extend it with a store-side `matches_memory_entry_store`
symmetric projection. Full permutation-argument soundness is Phase 4 scope.

**PIL-faithfulness.** The projection `memBus_row_Main_load_b` pins the
`as`/`ptr`/`bytes` fields to the values the PIL constraint forces:

* `as = 2` (memory) when `b_src_ind = 1` — per `main.pil:300-305` the
  entry goes to the memory side (`as = 2`) when `b_src_ind` is set;
* `ptr = b_offset_imm0 + b_src_ind * a[0]` — i.e. `addr1` from
  `main.pil:192`. For LD, `b_offset_imm0 = imm` and `b_src_ind = 1`,
  so `ptr = imm + a[0]`;
* `bytes = 8` when `ind_width = 8` — per `main.pil:303`,
  `bytes = b_src_ind * (ind_width - 8) + 8`. For LD's `ind_width = 8`,
  this collapses to `8`;
* `multiplicity = -1` — the read side (assume); Sail's state.mem
  provides the value, ZisK's Main row pulls it.
* Byte lanes `x0..x7` map to the Main row's `b[0]`/`b[1]` lanes via
  their 8 constituent bytes. For compositional A3 we expose both
  directly (the packed lemma in `Spec/LoadD.lean` bridges the 8-byte
  lanes to `main_b_packed = b_0 + b_1 * 2^32`).
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks
open Interaction

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The 64-bit memory value packed from a `MemoryBusEntry`'s byte lanes
    as a single `FGL` element:
    `x0 + x1 * 2^8 + x2 * 2^16 + ... + x7 * 2^56`.

    This is the field-level image of `U64.toBV` (which produces a
    `BitVec 64`). The two forms are related by the bridge lemma
    `memory_entry_toField_eq_toBV_toNat` below. -/
@[simp]
def memory_entry_toField (e : MemoryBusEntry FGL) : FGL :=
  e.x0
  + e.x1 * 256
  + e.x2 * 65536
  + e.x3 * 16777216
  + e.x4 * 4294967296
  + e.x5 * 1099511627776
  + e.x6 * 281474976710656
  + e.x7 * 72057594037927936

/-- Low 32 bits (= `x0..x3`) of a memory-bus entry, packed as FGL. -/
@[simp]
def memory_entry_lo (e : MemoryBusEntry FGL) : FGL :=
  e.x0 + e.x1 * 256 + e.x2 * 65536 + e.x3 * 16777216

/-- High 32 bits (= `x4..x7`) of a memory-bus entry, packed as FGL. -/
@[simp]
def memory_entry_hi (e : MemoryBusEntry FGL) : FGL :=
  e.x4 + e.x5 * 256 + e.x6 * 65536 + e.x7 * 16777216

/-- The packed lane decomposition: the full 64-bit value equals
    `lo + hi * 2^32`. Needed by `Spec/LoadD.lean` to bridge the
    byte-lane memory-entry representation to the Main row's
    `(b_0, b_1)` 32-bit-lane representation. -/
lemma memory_entry_toField_lo_hi (e : MemoryBusEntry FGL) :
    memory_entry_toField e =
      memory_entry_lo e + memory_entry_hi e * 4294967296 := by
  simp only [memory_entry_toField, memory_entry_lo, memory_entry_hi]
  ring

/-- **Memory-bus entry matching.** Two `MemoryBusEntry`s match when
    every field agrees. Used in `Spec/LoadD.lean` to say: the Main
    row's memory-read projection equals the `bus_effect`-side
    memory-bus entry supplied by the caller. -/
@[simp]
def matches_memory_entry (a b : MemoryBusEntry FGL) : Prop :=
  a.multiplicity = b.multiplicity
  ∧ a.as = b.as
  ∧ a.ptr = b.ptr
  ∧ a.x0 = b.x0
  ∧ a.x1 = b.x1
  ∧ a.x2 = b.x2
  ∧ a.x3 = b.x3
  ∧ a.x4 = b.x4
  ∧ a.x5 = b.x5
  ∧ a.x6 = b.x6
  ∧ a.x7 = b.x7
  ∧ a.timestamp = b.timestamp

/-- **Memory-read lane hypotheses for LD.** The Main row's low/high `b`
    lanes (as FGL field elements) equal the low/high halves of the
    memory-bus entry's packed 8-byte value.

    This is the compositional hypothesis that the ZisK PIL memory-bus
    `permutation_assumes` discharges (`state-machines/mem/pil/mem.pil:526`):
    it asserts Main's `b[0]`/`b[1]` are the two 32-bit halves of the
    `[op=LOAD, addr, mem_step, bytes=8, ...value]` entry on the bus.

    For A3 we take this as a compositional hypothesis (same stance as
    `matches_entry` for ADD in `Airs/OperationBus.lean`). Phase 4's
    audit task is to derive it from a PIL-level bus-emission spec. -/
@[simp]
def memory_load_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.b_0 row = memory_entry_lo e
  ∧ m.b_1 row = memory_entry_hi e

/-- **Register-write-back lane hypothesis for LD.** The Main row's
    `c` lanes are what the memory-bus register-write entry carries —
    i.e. Main writes the loaded doubleword to register `rd` via
    `store_reg` (`main.pil:316-319,323-328`).

    For compositional A3 we pair this with the register-read hypothesis
    from Sail (the caller supplies both ends). Phase 4 derives from the
    memory SM's permutation-proves side. -/
@[simp]
def register_write_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.c_0 row = memory_entry_lo e
  ∧ m.c_1 row = memory_entry_hi e

/-! ## Store-side (A4 SD) projections.

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

    This is the A4 symmetric analogue of `memory_load_lanes_match`:
    * LD reads the memory entry (`mult = -1, as = 2`) and matches it
      against `b`;
    * SD writes the memory entry (`mult = 1, as = 2`) with the same
      lane-packing, matched against `c` (equivalently `b`, via
      constraint 9/16).

    For compositional A4 we take this as a hypothesis — the caller
    supplies a `MemoryBusEntry` whose bytes spell the store value, and
    we verify `c`'s lanes agree. Phase 4's audit task is to derive it
    from the PIL memory-SM `permutation_proves` side. -/
@[simp]
def memory_store_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.c_0 row = memory_entry_lo e
  ∧ m.c_1 row = memory_entry_hi e

/-- **Register-read lane hypothesis (rs1 / a-lanes).** The Main row's
    `a` lanes equal the low/high halves of the register-read entry
    that provides the address-base register rs1 (`ptr = 4 * rs1,
    multiplicity = -1, as = 1`). This mirrors the `register_read_rs2_lanes_match`
    predicate for the `b` lanes and is the direct analogue for instructions
    (e.g. LD, SD, JALR) that read rs1 from `a[0]`/`a[1]`.

    For compositional proofs this is a hypothesis supplied by the Sail
    side (Sail evaluates `rX_bits rs1` giving the 8-byte bus value);
    `register_read_rs1_lanes_match_of_bus_emission` in
    `Airs/MemoryBus/LaneMatch.lean` promotes it to a theorem derived
    from the structural bus-entry predicate `matches_memory_entry`. -/
@[simp]
def register_read_rs1_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  m.a_0 row = memory_entry_lo e
  ∧ m.a_1 row = memory_entry_hi e

/-- **Register-read lane hypothesis for SD (rs2 value).** The Main
    row's `b` lanes equal the low/high halves of the register-read
    entry that provides the SD store value (`ptr = 4 * rs2,
    multiplicity = -1, as = 1`). Symmetric to LD's register-read-of-rs1;
    the load fetched *memory* into `b`, the store fetches *register rs2*
    into `b`.

    For compositional A4 this is a hypothesis supplied by the Sail
    side (Sail evaluates `rX_bits rs2` giving the same 8 bytes); Phase
    4 derives from PIL bus emission. -/
@[simp]
def register_read_rs2_lanes_match
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
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
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
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
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ)
    (e : MemoryBusEntry FGL) : Prop :=
  memory_entry_hi e = (1 - m.store_pc row) * m.c_1 row

/-! ## Bridge to `U64.toBV` for register-write values

The Phase 4.5 A-rewire requires bridging from `memory_entry_toField`
(field-level byte pack) to `U64.toBV` (`BitVec 64` register-write
value). Under per-byte range hypotheses and a no-wrap bound, this is
a direct consequence of `Fundamentals/PackedBitVec.lean`'s
`u64_toBV_eq_ofNat_fgl_val`.

Exposed here as the consumable form for A-rewire:
`memory_entry_toField_eq_toBV_toNat` reduces the entry bytes'
`U64.toBV` to `BitVec.ofNat 64 (memory_entry_toField e).val`. -/

/-- **Entry byte ranges.** Each of the 8 byte lanes of a memory-bus
    entry has `.val < 256`. Phase 4 / the PIL range-checker bus
    discharges this. -/
@[simp]
def memory_entry_bytes_in_range (e : MemoryBusEntry FGL) : Prop :=
  e.x0.val < 256 ∧ e.x1.val < 256 ∧ e.x2.val < 256 ∧ e.x3.val < 256
  ∧ e.x4.val < 256 ∧ e.x5.val < 256 ∧ e.x6.val < 256 ∧ e.x7.val < 256

/-- **No-wraparound bound on the packed entry.** The Nat byte-sum
    `x0.val + x1.val * 256 + … + x7.val * 256^7` is below `GL_prime`.

    Under `memory_entry_bytes_in_range`, the byte-sum is at most
    `2^64 - 1`, which *can* exceed `GL_prime = 2^64 - 2^32 + 1` in the
    "high-register" range. Callers discharge this either
    architecturally (e.g. for 32-bit ops the top four bytes are zero)
    or from the concrete product range. -/
@[simp]
def memory_entry_packed_no_wrap (e : MemoryBusEntry FGL) : Prop :=
  e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
  + e.x4.val * 4294967296 + e.x5.val * 1099511627776
  + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936 < GL_prime

/-- **Bridge: `U64.toBV` of entry bytes equals `BitVec.ofNat 64
    (memory_entry_toField e).val`.** Given byte ranges and the
    no-wraparound bound, the 8 memory-bus byte lanes — fed through
    `U64.toBV` (which coerces each `FGL` byte to `BitVec 8` via the
    `mod 256` instance) — produce the same `BitVec 64` as
    `BitVec.ofNat 64` applied to the field-level packed byte-sum's
    `.val`.

    This is the direct Phase 4.5 Bridge 3 application expressed at
    the memory-bus-entry level. Consumed by A-rewire. -/
lemma memory_entry_toField_eq_toBV_toNat
    (e : MemoryBusEntry FGL)
    (h_range : memory_entry_bytes_in_range e)
    (h_no_wrap : memory_entry_packed_no_wrap e) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
    = BitVec.ofNat 64 (memory_entry_toField e).val := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h_range
  simp only [memory_entry_packed_no_wrap] at h_no_wrap
  simp only [memory_entry_toField]
  exact ZiskFv.PackedBitVec.u64_toBV_eq_ofNat_fgl_val
    e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_no_wrap

end ZiskFv.Airs.MemoryBus
