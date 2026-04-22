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

/-!
Minimal `Transpiler` helper namespace for bus-effect pointer decoding.
`wrap_to_regidx` takes a 32-bit-tagged Goldilocks pointer (as emitted on
the memory bus for register reads/writes) and returns the RISC-V integer
register index `0..31`. Mirrors openvm-fv's `Fundamentals/Transpiler.lean`
definition, specialized to FGL.
-/
namespace Transpiler

  /-- Byte-tag indicator: 4 × regidx, packed into a Goldilocks element. -/
  def ind (rd : Fin 32) : FGL :=
    ⟨4 * rd.val, by omega⟩

  /-- Reverse the `ind` tag: `val / 4 mod 32`. The domain is Goldilocks
      (`FGL`); division is integer division on the representative. -/
  def wrap_to_regidx (val : FGL) : Fin 32 :=
    ⟨val.val / 4 % 32, by
      have : val.val / 4 % 32 < 32 := Nat.mod_lt _ (by decide)
      exact this⟩

end Transpiler

namespace ZiskFv.Trusted

open Goldilocks

/-- Subset of the Zisk-instruction row populated by a single Main-AIR row.
    Mirrors the witness columns relevant to ADD correctness + branch-relevant
    `jmp_offset1`/`jmp_offset2`/`set_pc` (Phase 2 archetype A1):

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
    | `set_pc` | 25 | `main.pil:150` |
    | `jmp_offset1` | 26 | `main.pil:151` |
    | `jmp_offset2` | 27 | `main.pil:152` |
    | `m32` | 28 | `main.pil:161` |
    | `store_pc` | 22 | `main.pil:142` |

    Other columns (pc, src selectors, most store_*) are omitted since they
    do not participate in the ADD / branch / JAL bus interactions. -/
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
  set_pc : FGL
  jmp_offset1 : FGL
  jmp_offset2 : FGL
  m32 : FGL
  /-- `store_pc` selector (col 22 of the Main AIR).
      `main.pil:311`: `store_value[0] = store_pc*(pc + jmp_offset2 - c[0]) + c[0]`.
      With `store_pc = 1` and `c[0] = 0`, this writes `pc + jmp_offset2` (= `pc + 4` for
      JAL) to the destination register. Pinned to 0 for ADD/BEQ; 1 for JAL. -/
  store_pc : FGL

/-- Goldilocks literal for the ADD opcode. `0x0A` per `vendor/zisk/pil/opids.pil`. -/
@[simp] def OP_ADD : FGL := 10

/-- Goldilocks literal for the EQ opcode. `0x09` per
    `vendor/zisk/core/src/zisk_ops.rs:391`. Used by RV64 branch opcodes
    (BEQ/BNE) which transpile to Zisk `eq` via `create_branch_op`
    (`riscv2zisk_context.rs:202,203`). -/
@[simp] def OP_EQ : FGL := 9

/-- Goldilocks literal for the FLAG opcode. `0x00` per
    `vendor/zisk/core/src/zisk_ops.rs:382`. Internal op whose
    `op_flag(a, b) = (0, true)` semantics give `c = 0, flag = 1`.
    Used by RV64 JAL (`riscv2zisk_context.rs:1098`, `zib.op("flag")`)
    as the microinstruction op — the actual PC+4 value written to rd
    comes from the `store_pc` selector (PIL `main.pil:311`), not the
    `op`'s return value. -/
@[simp] def OP_FLAG : FGL := 0

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
      ∧ row.set_pc = 0
      ∧ row.store_pc = 0
      ∧ row.jmp_offset1 = 4
      ∧ row.jmp_offset2 = 4
      ∧ row.a_lo = lane_lo (state.xreg rs1)
      ∧ row.a_hi = lane_hi (state.xreg rs1)
      ∧ row.b_lo = lane_lo (state.xreg rs2)
      ∧ row.b_hi = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for BEQ.

    Per `vendor/zisk/core/src/riscv2zisk_context.rs:202` an RV64 BEQ
    `rs1, rs2, imm` transpiles via `create_branch_op(instr, "eq", false, 4)`
    (line 740) to exactly one Zisk microinstruction. Concretely the emitted
    Main-AIR row has:
    * `op = OP_EQ = 9` (Binary state machine, `zisk_ops.rs:391`);
    * `is_external_op = 1` (OpType::Binary);
    * `set_pc = 0` (branches don't use `c[0]` as the next-pc source);
    * `jmp_offset1 = imm` — taken branch offset; packed as signed `i64`
      in the microinstruction. We expose it as the field element from
      sign-extending the RV64 immediate;
    * `jmp_offset2 = 4` — not-taken fall-through (4-byte instruction);
    * `m32 = 0` — EQ is the 64-bit comparison;
    * `flag` — output, determined by the Binary SM's `eq` verdict;
      not constrained by the transpiler contract (only by the bus hop).

    `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)`, same as ADD.

    **Trust basis.** Pure spec of `create_branch_op` in
    `riscv2zisk_context.rs`. BNE/BLT/BGE/BLTU/BGEU use the same helper
    with a different op-string; their transpile-axioms will mirror this
    one with `OP_EQ`/`OP_LT`/`OP_LTU` swapped and (for BNE/BGE/BGEU)
    the `neg=true` path that swaps `jmp_offset1` and `jmp_offset2`. -/
axiom transpile_BEQ :
    ∀ (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State),
      ∃ (row : ZiskInstructionRow),
        row.op = OP_EQ
      ∧ row.is_external_op = 1
      ∧ row.m32 = 0
      ∧ row.set_pc = 0
      ∧ row.store_pc = 0
      ∧ row.jmp_offset1 = imm_offset
      ∧ row.jmp_offset2 = 4
      ∧ row.a_lo = lane_lo (state.xreg rs1)
      ∧ row.a_hi = lane_hi (state.xreg rs1)
      ∧ row.b_lo = lane_lo (state.xreg rs2)
      ∧ row.b_hi = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for JAL.

    Per `vendor/zisk/core/src/riscv2zisk_context.rs:201,1098` an RV64 JAL
    `rd, imm` transpiles via `self.jal(i, 4)` to exactly one Zisk
    microinstruction emitted by `ZiskInstBuilder`:
    * `zib.src_a("imm", 0, false)` — `a` lanes are 0,
    * `zib.src_b("imm", 0, false)` — `b` lanes are 0,
    * `zib.op("flag")` — ZisK `OP_FLAG = 0`, `OpType::Internal`
      (`zisk_ops.rs:382`). `op_flag(a,b) = (0, true)` — but the
      `c`/`flag` values are constrained by Main constraints 8/15/17,
      not by the transpile contract itself;
    * `zib.store_pc("reg", rd, false)` — `store_pc = 1`, destination
      register is `rd`. The PIL `store_value[0] = store_pc*(pc+jmp_offset2-c[0])+c[0]`
      (`main.pil:311`) evaluates to `pc + jmp_offset2 = pc + 4` when
      `c[0] = 0` (forced by constraint 8);
    * `zib.j(imm, 4)` — `jmp_offset1 = imm`, `jmp_offset2 = 4`.
      **No** `set_pc()` is called, so `set_pc = 0` — the next-pc comes
      from the row handshake with `flag = 1` forcing
      `next_pc = pc + jmp_offset1 = pc + imm`;
    * `m32 = 0` — JAL is 64-bit on RV64 (no `m32` distinction for
      internal ops anyway).

    **Trust basis.** Pure spec of `fn jal` in `riscv2zisk_context.rs`
    at line 1098. -/
axiom transpile_JAL :
    ∀ (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State),
      ∃ (row : ZiskInstructionRow),
        row.op = OP_FLAG
      ∧ row.is_external_op = 0
      ∧ row.m32 = 0
      ∧ row.set_pc = 0
      ∧ row.store_pc = 1
      ∧ row.jmp_offset1 = imm_offset
      ∧ row.jmp_offset2 = 4
      ∧ row.a_lo = 0
      ∧ row.a_hi = 0
      ∧ row.b_lo = 0
      ∧ row.b_hi = 0

end ZiskFv.Trusted
