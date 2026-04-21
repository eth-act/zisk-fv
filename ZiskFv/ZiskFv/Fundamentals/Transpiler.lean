import Mathlib

import ZiskFv.Fundamentals.Goldilocks

/-!
RV64 → Zisk-instruction transpilation contract (axiomatized).

Phase 1 axiomatizes the ADD case only; Phase 2+ extends with other opcodes. The
axioms mirror `vendor/zisk/core/src/riscv2zisk_context.rs::create_register_op`
at commit `48cf7ccef`. Any deviation between this file and the transpiler
implementation is a trust-model break — see `docs/fv/extractor-notes.md`.

This module is part of the **trusted** surface: proofs of per-opcode
equivalence consume the axioms here without further justification. Changes
require re-auditing against the Rust source and re-signing off on the axiom
statement.
-/

namespace ZiskFv.Trusted

open Goldilocks

/-- Subset of the Zisk-instruction row populated by a single Main-AIR row.
    Mirrors the witness columns relevant to ADD correctness:

    | field | Main AIR column (stage-1) | reference |
    |-------|---------------------------|-----------|
    | `op` | 20 | `main.pil:136` |
    | `is_external_op` | 19 | `main.pil:135` |
    | `a_lo` | 0 | `main.pil:94` (a[0]) |
    | `a_hi` | 1 | `main.pil:94` (a[1]) |
    | `b_lo` | 2 | `main.pil:95` (b[0]) |
    | `b_hi` | 3 | `main.pil:95` (b[1]) |
    | `c_lo` | 4 | `main.pil:96` (c[0]) |
    | `c_hi` | 5 | `main.pil:96` (c[1]) |
    | `flag` | 6 | `main.pil:97` |
    | `m32` | 28 | `main.pil:161` |

    Other columns (pc, src selectors, store_*) are omitted since they do not
    participate in the ADD-bus interaction. -/
structure ZiskInstructionRow where
  op : FGL
  is_external_op : FGL
  a_lo : FGL
  a_hi : FGL
  b_lo : FGL
  b_hi : FGL
  c_lo : FGL
  c_hi : FGL
  flag : FGL
  m32 : FGL

/-- Goldilocks literal for the ADD opcode. `0x0A` per `vendor/zisk/pil/opids.pil`. -/
@[simp] def OP_ADD : FGL := 10

/-- Goldilocks literal for OPERATION_BUS_ID. Per `vendor/zisk/pil/opids.pil:2`. -/
@[simp] def OPERATION_BUS_ID : FGL := 5000

/-- Abstract RV64 state, indexed access to integer registers via `Fin 32`. In
    Phase 1 this is a black-box; Phase 3 wires it to `LeanRV64D.RegFile` via
    a coercion. The `xreg` accessor returns a `BitVec 64`; splitting into two
    `BitVec 32` lanes happens in the Main AIR row. -/
structure RV64State where
  xreg : Fin 32 → BitVec 64
  pc : BitVec 64

/-- Split a `BitVec 64` into (low 32, high 32) lanes as Goldilocks elements.
    Matches how `vendor/zisk/core/src/riscv2zisk_context.rs::create_register_op`
    populates `a`/`b`/`c`. -/
def lane_lo (v : BitVec 64) : FGL :=
  ⟨(v.toNat) % 4294967296, by
    have := Nat.mod_lt v.toNat (by decide : 0 < 4294967296)
    omega⟩

def lane_hi (v : BitVec 64) : FGL :=
  ⟨(v.toNat / 4294967296) % 4294967296, by
    have := Nat.mod_lt (v.toNat / 4294967296) (by decide : 0 < 4294967296)
    omega⟩

/-- The axiomatic RV64 → Zisk row contract for ADD.

    Given RV64 state and registers `rs1`, `rs2`, `rd`, the ADD microinstruction
    emitted by `vendor/zisk/core/src/riscv2zisk_context.rs::create_register_op`
    (called from the `"add"` arm at line 100) produces exactly one Main-AIR row
    with the shape below.

    **Trust basis.** This axiom is a pure spec of the Rust transpiler's ADD
    branch — not a consequence of anything else in the Lean development. If
    ZisK's transpiler changes (new opcode encoding, different source routing),
    this axiom must change in lockstep. -/
axiom transpile_ADD :
    ∀ (rs1 rs2 _rd : Fin 32) (state : RV64State),
      ∃ (row : ZiskInstructionRow),
        row.op = OP_ADD
      ∧ row.is_external_op = 1
      ∧ row.flag = 0
      ∧ row.m32 = 0
      ∧ row.a_lo = lane_lo (state.xreg rs1)
      ∧ row.a_hi = lane_hi (state.xreg rs1)
      ∧ row.b_lo = lane_lo (state.xreg rs2)
      ∧ row.b_hi = lane_hi (state.xreg rs2)

end ZiskFv.Trusted
