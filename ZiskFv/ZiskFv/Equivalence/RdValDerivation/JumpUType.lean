import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Extensions

/-!
# RdValDerivation.JumpUType — `h_rd_val` discharge lemmas for JAL/JALR/LUI/AUIPC

**Phase 2 N-Jump-UTYPE derivation (finishing1.md).**

Each lemma in this file consumes:
* A `MemoryBusEntry FGL` holding the rd-write byte lanes `e.x0..e.x7`.
* Per-byte range bounds (`e.xᵢ.val < 256`).
* A byte-sum hypothesis tying the assembled 8-byte value to the
  opcode's pure-spec rd output.

And produces the `h_rd_val` conclusion:
```
U64.toBV #v[e.x0, ..., e.x7] = <pure_spec_rd_value>
```

exactly matching the `h_rd_val :` parameter in the corresponding
`Equivalence/<Op>.lean` metaplan theorem, so Phase 3 can inline these
calls to eliminate that parameter.

## Opcode → K3 lemma map

| Opcode | Pure-spec rd value | K3 lemma used |
|---|---|---|
| JAL  | `jal_input.PC + 4` | `pc_plus4_bv64_of_bytes` |
| JALR | `jalr_input.PC + 4` | `pc_plus4_bv64_of_bytes` |
| LUI  | `BitVec.signExtend 64 (imm ++ 0#12)` | `u64_toBV_of_imm20_lanes` |
| AUIPC| `PC + BitVec.signExtend 64 (imm ++ 0#12)` | `BitVec.eq_of_toNat_eq` + byte-sum |

## Trust surface

These lemmas trust the `h_byte_sum` hypothesis — it is the *interface
point* between the circuit-level extraction (byte-range constraints from
the PIL) and the semantic level. Phase 3 GoldenTraces fixtures supply
this hypothesis; K2 (structural form, `finishing1.md` gap) handles the
full memory-bus match.
-/

namespace ZiskFv.Equivalence.RdValDerivation.JumpUType

open Goldilocks
open Interaction
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.Extensions

/-! ## JAL: rd ← PC + 4 -/

/-- **`h_rd_val` discharge for JAL.**
    Given byte-range bounds on the rd-write bus entry's byte lanes
    and a byte-sum hypothesis `h_byte_sum` stating that the assembled
    value equals `(PC + 4).toNat`, produces:

    `U64.toBV #v[e.x0, ..., e.x7] = PC + 4`

    which matches the `h_rd_val` parameter in `Equivalence.Jal.equiv_JAL_metaplan`. -/
theorem h_rd_val_jut_jal
    (PC : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (PC + 4).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = PC + 4 :=
  pc_plus4_bv64_of_bytes PC e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## JALR: rd ← PC + 4 -/

/-- **`h_rd_val` discharge for JALR.**
    Identical shape to `h_rd_val_jut_jal` — JALR also writes `PC + 4`
    as the link value. The `PC` here is `jalr_input.PC`.

    Produces:
    `U64.toBV #v[e.x0, ..., e.x7] = PC + 4`

    which matches the `h_rd_val` parameter in `Equivalence.Jalr.equiv_JALR_metaplan`. -/
theorem h_rd_val_jut_jalr
    (PC : BitVec 64)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (PC + 4).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = PC + 4 :=
  pc_plus4_bv64_of_bytes PC e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## LUI: rd ← BitVec.signExtend 64 (imm ++ 0#12) -/

/-- **`h_rd_val` discharge for LUI.**
    Given byte-range bounds on the rd-write bus entry's byte lanes and a
    byte-sum hypothesis `h_byte_sum` stating that the assembled value equals
    `(BitVec.signExtend 64 (imm ++ 0#12)).toNat`, produces:

    `U64.toBV #v[e.x0, ..., e.x7] = BitVec.signExtend 64 (imm ++ 0#12)`

    which matches the `h_rd_val` parameter in `Equivalence.Lui.equiv_LUI_metaplan`.

    The byte-sum hypothesis is supplied by the GoldenTraces fixture (or a
    Phase 2 derivation combining the transpiler `b_0`/`b_1` pin with the
    PIL byte-range constraints on the memory-bus entry). -/
theorem h_rd_val_jut_lui
    (imm : BitVec 20)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) :=
  u64_toBV_of_imm20_lanes imm e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## AUIPC: rd ← PC + BitVec.signExtend 64 (imm ++ 0#12) -/

/-- **`h_rd_val` discharge for AUIPC.**
    Given byte-range bounds on the rd-write bus entry's byte lanes and a
    byte-sum hypothesis `h_byte_sum` stating that the assembled value equals
    `(PC + BitVec.signExtend 64 (imm ++ 0#12)).toNat`, produces:

    `U64.toBV #v[e.x0, ..., e.x7] = PC + BitVec.signExtend 64 (imm ++ 0#12)`

    which matches the `h_rd_val` parameter in `Equivalence.Auipc.equiv_AUIPC_metaplan`.

    AUIPC's rd value is `PC + sext imm`, a `BitVec 64` addition, whose
    `.toNat` wraps at 2^64 — matching how ZisK's circuit computes the value
    via `pc + jmp_offset2` in Goldilocks and stores it as two 32-bit lanes.
    The byte-sum encodes exactly this wrapped 64-bit result, so
    `BitVec.eq_of_toNat_eq` + `u64_toBV_of_bytes_toNat` close the goal. -/
theorem h_rd_val_jut_auipc
    (PC : BitVec 64)
    (imm : BitVec 20)
    (e : MemoryBusEntry FGL)
    (h0 : e.x0.val < 256) (h1 : e.x1.val < 256)
    (h2 : e.x2.val < 256) (h3 : e.x3.val < 256)
    (h4 : e.x4.val < 256) (h5 : e.x5.val < 256)
    (h6 : e.x6.val < 256) (h7 : e.x7.val < 256)
    (h_byte_sum :
      e.x0.val + e.x1.val * 256 + e.x2.val * 65536 + e.x3.val * 16777216
        + e.x4.val * 4294967296 + e.x5.val * 1099511627776
        + e.x6.val * 281474976710656 + e.x7.val * 72057594037927936
      = (PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat) :
    U64.toBV #v[(e.x0 : BitVec 8), (e.x1 : BitVec 8), (e.x2 : BitVec 8), (e.x3 : BitVec 8),
                (e.x4 : BitVec 8), (e.x5 : BitVec 8), (e.x6 : BitVec 8), (e.x7 : BitVec 8)]
      = PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat e.x0 e.x1 e.x2 e.x3 e.x4 e.x5 e.x6 e.x7
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

end ZiskFv.Equivalence.RdValDerivation.JumpUType
