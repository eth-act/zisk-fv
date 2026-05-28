import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Main.Main

/-!
RV64 → Zisk-instruction transpilation contract (axiomatized).

The axioms mirror `zisk/core/src/riscv2zisk_context.rs::create_register_op`
(and friends). Any deviation between this file and the transpiler
implementation is a trust-model break — see `docs/fv/extractor-notes.md`.

This module is part of the **trusted** surface: proofs of per-opcode
equivalence consume the axioms here without further justification. Changes
require re-auditing against the Rust source and re-signing off on the axiom
statement.

## store_pc=1 PC bridges

The bottom of this file (after the standard `transpile_<OP>` operand /
selector axioms) carries three additional axioms — `transpile_PC_for_JAL`,
`transpile_PC_for_JALR`, and `transpile_PC_for_AUIPC` — that pin the
**runtime PC value** at the Main-AIR `pc` column for the three
`store_pc = 1` opcodes. These extend the trusted transpile contract beyond
operand / selector witnesses to the program-counter witness column itself.

They are a strict trust expansion necessary because the existing operand
axioms do not constrain the `pc` column (PIL constraint 20 ties it to
`expected_current_pc` derived from the previous row's rotation, which the
extractor does not currently surface), but downstream Spec / Equivalence
proofs of JAL / JALR / AUIPC's rd-write `pc + jmp_offset2` need to bridge
the FGL-side `m.pc r_main` to the Sail-side `state.pc`. Trust-base
entries: **TP-JAL**, **TP-JALR**, **TP-AUIPC** in
`docs/fv/trusted-base.md`.
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
open ZiskFv.Airs.Main

/-- Subset of the Zisk-instruction row populated by a single Main-AIR row.
    Mirrors the witness columns relevant to ADD correctness + branch-relevant
    `jmp_offset1`/`jmp_offset2`/`set_pc`:

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

/-- Goldilocks literal for the ADD opcode. `0x0A` per `zisk/pil/opids.pil`. -/
@[simp] def OP_ADD : FGL := 10

/-- Goldilocks literal for the EQ opcode. `0x09` per
    `zisk/core/src/zisk_ops.rs:391`. Used by RV64 branch opcodes
    (BEQ/BNE) which transpile to Zisk `eq` via `create_branch_op`
    (`riscv2zisk_context.rs:202,203`). -/
@[simp] def OP_EQ : FGL := 9

/-- Goldilocks literal for the LT opcode. `0x07` per
    `zisk/core/src/zisk_ops.rs:389`. Signed less-than comparator
    used by RV64 branch opcodes BLT / BGE via `create_branch_op`
    (`riscv2zisk_context.rs:204,205`). Dispatched to the Binary state
    machine via the operation bus (same routing as OP_EQ). -/
@[simp] def OP_LT : FGL := 7

/-- Goldilocks literal for the LTU opcode. `0x06` per
    `zisk/core/src/zisk_ops.rs:388`. Unsigned less-than
    comparator used by RV64 branch opcodes BLTU / BGEU via
    `create_branch_op` (`riscv2zisk_context.rs:206,207`). Dispatched to
    the Binary state machine via the operation bus. -/
@[simp] def OP_LTU : FGL := 6

/-- Goldilocks literal for the FLAG opcode. `0x00` per
    `zisk/core/src/zisk_ops.rs:382`. Internal op whose
    `op_flag(a, b) = (0, true)` semantics give `c = 0, flag = 1`.
    Used by RV64 JAL (`riscv2zisk_context.rs:1098`, `zib.op("flag")`)
    as the microinstruction op — the actual PC+4 value written to rd
    comes from the `store_pc` selector (PIL `main.pil:311`), not the
    `op`'s return value. -/
@[simp] def OP_FLAG : FGL := 0

/-- Goldilocks literal for the CopyB opcode. `0x01` per
    `zisk/core/src/zisk_ops.rs:383`. Used by unsigned-width RV64
    load opcodes (LD/LWU/LHU/LBU) which transpile via `load_op` with
    `op = "copyb"` (`riscv2zisk_context.rs:211-216`). `OpType::Internal`,
    so `is_external_op = 0`: Main constraint 9 forces `c = b` directly,
    no operation-bus hop. The load value flows into `b` via `b_src_ind`
    from the memory bus, then copies through to `c` (and on to `rd` via
    `store_reg`). -/
@[simp] def OP_COPYB : FGL := 1

/-- Goldilocks literal for the 32-bit shift-left-word opcode.
    `0x24` per `zisk/pil/operations.pil:62` and
    `zisk/core/src/zisk_ops.rs:416`. Used by RV64 SLLW
    (`riscv2zisk_context.rs:155`, `create_register_op(..., "sll_w", 4)`)
    and SLLIW (`riscv2zisk_context.rs:195`, `immediate_op(..., "sll_w", 4)`).
    Type `BinaryE` — handled by the `BinaryExtension` SM (not `BinaryAdd`). -/
@[simp] def OP_SLL_W : FGL := 36

/-- Goldilocks literal for the 64-bit shift-left opcode.
    `0x21` per `zisk/core/src/zisk_ops.rs:413`. Used by RV64 SLL
    (`riscv2zisk_context.rs:135`, `create_register_op(..., "sll", 4)`)
    and SLLI (`riscv2zisk_context.rs:175`, `immediate_op(..., "sll", 4)`).
    Type `BinaryE` — handled by the `BinaryExtension` SM. -/
@[simp] def OP_SLL : FGL := 33

/-- Goldilocks literal for the 64-bit shift-right-logical opcode.
    `0x22` per `zisk/core/src/zisk_ops.rs:414`. Used by RV64 SRL
    (`riscv2zisk_context.rs:139`, `create_register_op(..., "srl", 4)`)
    and SRLI (`riscv2zisk_context.rs:179`, `immediate_op(..., "srl", 4)`).
    Type `BinaryE` — handled by the `BinaryExtension` SM. -/
@[simp] def OP_SRL : FGL := 34

/-- Goldilocks literal for the 64-bit shift-right-arithmetic opcode.
    `0x23` per `zisk/core/src/zisk_ops.rs:415`. Used by RV64 SRA
    (`riscv2zisk_context.rs:140`, `create_register_op(..., "sra", 4)`)
    and SRAI (`riscv2zisk_context.rs:180`, `immediate_op(..., "sra", 4)`).
    Type `BinaryE` — handled by the `BinaryExtension` SM. -/
@[simp] def OP_SRA : FGL := 35

/-- Goldilocks literal for the 32-bit shift-right-logical-word opcode.
    `0x25` per `zisk/pil/operations.pil` and
    `zisk/core/src/zisk_ops.rs:417`. Used by RV64 SRLW
    (`riscv2zisk_context.rs:156`, `create_register_op(..., "srl_w", 4)`)
    and SRLIW (`riscv2zisk_context.rs:196`, `immediate_op(..., "srl_w", 4)`).
    Type `BinaryE` — handled by the `BinaryExtension` SM. -/
@[simp] def OP_SRL_W : FGL := 37

/-- Goldilocks literal for the 32-bit shift-right-arithmetic-word opcode.
    `0x26` per `zisk/pil/operations.pil` and
    `zisk/core/src/zisk_ops.rs:418`. Used by RV64 SRAW
    (`riscv2zisk_context.rs:157`, `create_register_op(..., "sra_w", 4)`)
    and SRAIW (`riscv2zisk_context.rs:197`, `immediate_op(..., "sra_w", 4)`).
    Type `BinaryE` — handled by the `BinaryExtension` SM. -/
@[simp] def OP_SRA_W : FGL := 38

/-- Goldilocks literal for the 32-bit add-word opcode.
    `0x1a = 26` per `zisk/core/src/zisk_ops.rs:408`
    (`(AddW, "add_w", Binary, …, 0x1a, …)`). Used by RV64 ADDW
    (`riscv2zisk_context.rs:153`, `create_register_op(..., "add_w", 4)`)
    and ADDIW (`riscv2zisk_context.rs:192`,
    `immediate_op(..., "add_w", 4)`). Type `Binary` — handled by the
    Binary SM (not `BinaryExtension`). Behaviour: `op_add_w(a, b) =
    ((a as i32) + (b as i32)) as u64` with flag `false`
    (`zisk_ops.rs:572`). -/
@[simp] def OP_ADD_W : FGL := 26

/-- Goldilocks literal for the 32-bit sub-word opcode.
    `0x1b = 27` per `zisk/core/src/zisk_ops.rs:409`
    (`(SubW, "sub_w", Binary, …, 0x1b, …)`). Used by RV64 SUBW
    (`riscv2zisk_context.rs:154`, `create_register_op(..., "sub_w", 4)`).
    Type `Binary`. Behaviour: `op_sub_w(a, b) =
    ((a as i32) - (b as i32)) as u64` with flag `false`
    (`zisk_ops.rs:596`). -/
@[simp] def OP_SUB_W : FGL := 27


/-- Goldilocks literal for OPERATION_BUS_ID. Per `zisk/pil/opids.pil:2`. -/
@[simp] def OPERATION_BUS_ID : FGL := 5000

/-- Abstract RV64 state, indexed access to integer registers via `Fin 32`.
    The `xreg` accessor returns a `BitVec 64`; splitting into two
    `BitVec 32` lanes happens in the Main AIR row. -/
structure RV64State where
  xreg : Fin 32 → BitVec 64
  pc : BitVec 64

/-- Split a `BitVec 64` into (low 32, high 32) lanes as Goldilocks elements.
    Matches how `zisk/core/src/riscv2zisk_context.rs::create_register_op`
    populates `a`/`b`/`c`. -/
def lane_lo (v : BitVec 64) : FGL :=
  ⟨(v.toNat) % 4294967296, by
    have := Nat.mod_lt v.toNat (by decide : 0 < 4294967296)
    omega⟩

def lane_hi (v : BitVec 64) : FGL :=
  ⟨(v.toNat / 4294967296) % 4294967296, by
    have := Nat.mod_lt (v.toNat / 4294967296) (by decide : 0 < 4294967296)
    omega⟩

/-- The axiomatic RV64 → Zisk row contract for ADD, in `Valid_Main`-row form.

    Given a Main AIR instance, a row index, RV64 state, and source registers,
    whenever the row is an active ADD row (`is_external_op = 1`, `op = OP_ADD`),
    the Main row's `a`/`b` lanes equal the split lanes of `state.xreg rs1` and
    `state.xreg rs2`, and the mode selectors (`m32`, `set_pc`, `store_pc`,
    `jmp_offset1/2`) take the values emitted by the Rust transpiler's ADD arm
    at `zisk/core/src/riscv2zisk_context.rs::create_register_op`
    (called from the `"add"` arm at line 100).

    **Trust basis.** Pure spec of the Rust transpiler's ADD branch: the
    axiom pins the named columns of the Main AIR at index `r_main`. If
    ZisK's transpiler changes (new opcode encoding, different source
    routing), this axiom must change in lockstep. -/
axiom transpile_ADD :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (state : RV64State)
      (rs1 rs2 : Fin 32),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_ADD →
      m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4

/-- The axiomatic RV64 → Zisk row contract for JAL.

    Per `zisk/core/src/riscv2zisk_context.rs:201,1098` an RV64 JAL
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
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_FLAG →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 1
      ∧ m.jmp_offset1 r_main = imm_offset
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = 0
      ∧ m.a_1 r_main = 0
      ∧ m.b_0 r_main = 0
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for JALR (jump-and-link-register).

    Per `zisk/core/src/riscv2zisk_context.rs:200,1025` an RV64 JALR
    `rd, rs1, imm12` transpiles via `self.jalr(i, 4)`. The archetype-
    validation contract below captures the simplified "internal-copyb"
    shape the `JumpArchetype.jalr_archetype_*` lemmas consume:
    * `op = OP_COPYB = 1` — internal op 1 (c = b via constraint 9);
    * `is_external_op = 0` — no operation-bus hop;
    * `set_pc = 1` — next-pc comes from `c_0 + jmp_offset1 = b_0 +
      jmp_offset1 = rs1_lo + imm12`. Constraint 19
      (`flag * set_pc = 0`) forces `flag = 0`, consistent with
      constraint 18 under `op = 1`;
    * `store_pc = 1` — rd receives `pc + jmp_offset2 = pc + 4` via the
      store_value expression with `c_0 = b_0` (rs1) canceling;
    * `jmp_offset1 = imm_offset` — the register-relative offset;
    * `jmp_offset2 = 4` — link-address offset;
    * `b` lanes carry `xreg(rs1)`; the transpile axiom does **not** pin
      `a`/`c` because they don't participate in the JALR
      archetype theorems (`a` is an immediate mask in the live Rust
      code, and `c` is constrained by the copyb rule).

    **Note on the live ZisK transpiler.** The actual Rust `jalr`
    function (line 1055-1092) emits a Binary `and` microinstruction
    (external op), and for misaligned immediates a two-instruction
    `add`+`and` sequence. Both paths ultimately produce the same
    architectural behavior (`rd ← pc + 4`, `nextPC ← (rs1 + imm) &
    mask`). We model JALR here as internal-copyb for archetype-macro
    validation; closing the full Rust contract (with the Binary-SM
    bus hop) requires the `equiv_AND_circuit`/`equiv_ADD_IMM` external-op
    infrastructure.

    **Trust basis.** Simplified spec of `fn jalr` in
    `riscv2zisk_context.rs:1025`, targeting the Main AIR row observables
    the `JumpArchetype` macro depends on. -/
axiom transpile_JALR :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_offset : FGL) (state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 1
      ∧ m.store_pc r_main = 1
      ∧ m.jmp_offset1 r_main = imm_offset
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.b_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs1)

/-- The axiomatic RV64 → Zisk row contract for SD (store doubleword).

    Per `zisk/core/src/riscv2zisk_context.rs:223` an RV64 SD
    `rs2, imm(rs1)` transpiles via `self.store_op(i, "copyb", 8, 4)`
    (line 828) to exactly one Zisk microinstruction emitted by
    `ZiskInstBuilder`:
    * `zib.src_a("reg", rs1, false)` — `a` lanes carry `xreg(rs1)`
      (the base address register);
    * `zib.src_b("reg", rs2, false)` — `b` lanes carry `xreg(rs2)`
      (the store *value*). **This is the key departure from LD:**
      LD has `src_b = "ind"` (memory read), SD has `src_b = "reg"`
      (register read of the value);
    * `zib.op("copyb")` — ZisK `OP_COPYB = 1`, `OpType::Internal`.
      Same as LD. Constraint 9 still forces `c = b`, so `c` equals
      the store value;
    * `zib.ind_width(8)` — memory-write width is 8 bytes;
    * `zib.store("ind", imm, false, false)` — `store_ind = 1`,
      `store_offset = imm`. PIL writes `store_value` (= `c` since
      `store_pc = 0`) to memory at `addr2 = a + imm` (per
      `main.pil:314-321`). No register write, so this is a pure
      memory side-effect;
    * `zib.j(4, 4)` — `jmp_offset1 = jmp_offset2 = 4`. No
      `set_pc()`, no `store_pc()`, so `set_pc = 0`, `store_pc = 0`.
      With `flag = 0` (forced by constraint 18), the PC handshake
      yields `next_pc = pc + 4`;
    * `m32 = 0` — SD is a 64-bit store (no `m32` distinction for
      internal ops anyway).

    **Trust basis.** Pure spec of `fn store_op` in
    `riscv2zisk_context.rs:828`. SB/SH/SW use the same helper with
    different `w` (1/2/4); their transpile-axioms will mirror this one
    with the `ind_width` fact adjusted (and a byte-zeroing hypothesis
    on the memory-bus-write entry's high lanes). A4 scope is SD only. -/
axiom transpile_SD :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SW (store word).

    Per `zisk/core/src/riscv2zisk_context.rs:222` an RV64 SW
    `rs2, imm(rs1)` transpiles via `self.store_op(i, "copyb", 4, 4)`
    (line 828) to exactly one Zisk microinstruction emitted by
    `ZiskInstBuilder`:
    * `zib.src_a("reg", rs1, false)` — `a` lanes carry `xreg(rs1)`
      (the base address register);
    * `zib.src_b("reg", rs2, false)` — `b` lanes carry `xreg(rs2)`
      (the store value). Identical to SD on the operand side.
    * `zib.op("copyb")` — ZisK `OP_COPYB = 1`, `OpType::Internal`.
      **Shared across the entire integer store family** (SB/SH/SW/SD
      all use `copyb`, see `riscv2zisk_context.rs:220-223`);
    * `zib.ind_width(4)` — memory-write width is **4 bytes** (the
      sole substantive difference from SD's `ind_width(8)`).
      `ind_width` is *not* a field of the `ZiskInstructionRow` Lean
      structure — it surfaces only on the memory-bus entry (as the
      count of live byte lanes). At the Main-row contract level
      captured by this axiom, SW's row is therefore structurally
      identical to SD's; the 4-vs-8 byte split manifests solely via
      a high-byte-zeroing hypothesis on the memory-bus write entry
      supplied by the caller (SW zeros `entry.x4..x7`).
    * `zib.store("ind", imm, false, false)` — `store_ind = 1`,
      `store_offset = imm`. Pure memory side-effect, no register
      write;
    * `zib.j(4, 4)` — `jmp_offset1 = jmp_offset2 = 4`, so `set_pc = 0`
      and `store_pc = 0`, and with `flag = 0` (constraint 18) the PC
      handshake yields `next_pc = pc + 4`;
    * `m32 = 0` — the `m32` selector is unused for internal ops.

    **Trust basis.** Pure spec of `fn store_op` in
    `riscv2zisk_context.rs:828` with `op = "copyb"`, `w = 4`,
    `inst_size = 4`. The row shape is identical to `transpile_SD` by
    design — the store archetype covers both uniformly. SB/SH will
    mirror this with their own width-zeroing witnesses. -/
axiom transpile_SW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- Goldilocks literal for the MUL opcode. `0xb4 = 180` per
    `zisk/core/src/zisk_ops.rs:427`. Signed × signed multiplication,
    low 64 bits (`result_part = Low`). Dispatched to the Arith state
    machine via the operation bus. Used by RV64 MUL
    (`riscv2zisk_context.rs:243`, `create_register_op(..., "mul", 4)`). -/
@[simp] def OP_MUL : FGL := 180

/-- Goldilocks literal for the MULU opcode. `0xb0 = 176` — unsigned ×
    unsigned, low 64 bits. `zisk_ops.rs:424`. Arith "primary = mulu,
    secondary = muluh" (both share the same row, disambiguated by the
    result-lane selector). Note: RV64 does not have a distinct MULU;
    plain MUL covers the low-64 case for both signed/unsigned since
    the low bits agree. -/
@[simp] def OP_MULU : FGL := 176

/-- Goldilocks literal for the MULUH opcode. `0xb1 = 177` — unsigned ×
    unsigned, high 64 bits. `zisk_ops.rs:425`. Maps to RV64 MULHU via
    the transpiler rename at `riscv2zisk_context.rs:246`
    (`"mulhu" → "muluh"`). -/
@[simp] def OP_MULUH : FGL := 177

/-- Goldilocks literal for the MULSUH opcode. `0xb3 = 179` — signed ×
    unsigned, high 64 bits. `zisk_ops.rs:426`. Maps to RV64 MULHSU via
    the transpiler rename at `riscv2zisk_context.rs:245`
    (`"mulhsu" → "mulsuh"`). -/
@[simp] def OP_MULSUH : FGL := 179

/-- Goldilocks literal for the MULH opcode. `0xb5 = 181` — signed ×
    signed, high 64 bits. `zisk_ops.rs:428`. Used by RV64 MULH
    (`riscv2zisk_context.rs:244`). -/
@[simp] def OP_MULH : FGL := 181

/-- Goldilocks literal for the MUL_W opcode. `0xb6 = 182` — the RV64 MULW
    32-bit variant. `zisk_ops.rs:429`. Maps to RV64 MULW via
    `riscv2zisk_context.rs:247`. `m32 = 1` on the Main row. -/
@[simp] def OP_MUL_W : FGL := 182

/-- Transpile contract for RV64M MULW.
    Mirrors `transpile_MUL` modulo opcode = `OP_MUL_W` and `m32 = 1`.
    `riscv2zisk_context.rs:247` routes MULW through
    `create_register_op(..., "mul_w", 4)`, whose `_w` suffix sets the
    Main-row `m32` selector. -/
axiom transpile_MULW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_MUL_W →
        m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for MUL.

    Per `zisk/core/src/riscv2zisk_context.rs:243` an RV64 MUL
    `rd, rs1, rs2` transpiles via `create_register_op(..., "mul", 4)`
    (line 631) — the exact helper ADD uses. One Main-AIR row with:
    * `op = OP_MUL = 180`;
    * `is_external_op = 1` — type `ArithAm32` dispatches to the Arith
      state machine via the operation bus;
    * `set_pc = 0`, `store_pc = 0` — MUL does not touch PC or write
      PC-derived values; default register write via `store_reg`;
    * `jmp_offset1 = jmp_offset2 = 4` — `zib.j(4, 4)` regardless of
      the flag output (MUL's bus flag is `div_by_zero`, fixed to 0 for
      multiplications);
    * `m32 = 0` — MUL is the 64-bit operand form; MULW (`OP_MUL_W`)
      sets `m32 = 1` instead;
    * `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)` same as ADD;
    * `flag` is left as an output (populated by the Arith bus-pop with
      `div_by_zero = 0`). Not constrained by the transpile contract.

    **Trust basis.** Pure spec of the `"mul"` arm in
    `riscv2zisk_context.rs:243`, which is `create_register_op(i, "mul", 4)`
    — the identical call shape to ADD's, modulo the `op` string. MULH,
    MULHU, MULHSU, MULW share this shape with only `op` (and `m32` for
    MULW) changing; their transpile-axioms will mirror this one with
    the `OP_*` literal swapped and, for MULW, `m32 = 1`. -/
axiom transpile_MUL :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_MUL →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SLLW.

    Per `zisk/core/src/riscv2zisk_context.rs:155` an RV64 SLLW
    `rd, rs1, rs2` transpiles via `create_register_op(instr, "sll_w", 4)`
    (line 631) to exactly one Zisk microinstruction:
    * `op = OP_SLL_W = 0x24 = 36` (`zisk_ops.rs:416`, type `BinaryE`);
    * `is_external_op = 1` — `BinaryE ≠ Internal | Fcall`
      (`zisk_inst_builder.rs:203`); the bus hop goes to the
      `BinaryExtension` SM, not `BinaryAdd`;
    * `m32 = 1` — `"sll_w".contains("_w")` is `true`
      (`zisk_inst_builder.rs:206`). Exercises the `(1 - m32) * x`
      bus-zeroing path on the operation bus;
    * `set_pc = 0`, `store_pc = 0` — register-op, not PC-mutating;
    * `jmp_offset1 = jmp_offset2 = 4` — no branch, fall-through advance;
    * `flag = 0` — `op_sll_w`'s `flag` return is always `false`
      (`zisk_ops.rs:624`).

    `a` / `b` lanes carry the full 64-bit `xreg(rs1)` / `xreg(rs2)`
    values. `m32 = 1` signals downstream (via the PIL
    `a = [a[0], (1 - m32) * a[1]]` bus-emission) that the high lanes
    are zeroed on the bus, so only the low 32 bits reach the
    `BinaryExtension` SM.

    **Trust basis.** Pure spec of the `"sllw"` arm of the
    `create_register_op` dispatch in `riscv2zisk_context.rs:155`.
    SRLW / SRAW mirror this with `op = OP_SRL_W = 37` /
    `op = OP_SRA_W = 38` and the same `m32 = 1` path. SLL / SRL /
    SRA (64-bit siblings) keep `m32 = 0`. -/
axiom transpile_SLLW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SLL_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SH (store halfword).

    Per `zisk/core/src/riscv2zisk_context.rs:221` an RV64 SH
    `rs2, imm(rs1)` transpiles via `self.store_op(i, "copyb", 2, 4)`
    (line 828) to exactly one Zisk microinstruction. The row shape is
    identical to `transpile_SW` / `transpile_SD` at the Main-AIR columns
    modelled by `ZiskInstructionRow` — the `ind_width` width (2 vs 4
    vs 8) is *not* a Main-AIR column; it surfaces only on the
    memory-bus entry as the count of live byte lanes.

    * `op = OP_COPYB = 1` — shared across the entire integer store
      family (SB/SH/SW/SD all use `copyb` per
      `riscv2zisk_context.rs:220-223`);
    * `is_external_op = 0` — OpType::Internal; constraint 9 forces
      `c = b`, no operation-bus hop;
    * `m32 = 0` — the `m32` selector is unused for internal ops;
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
    * `a` lanes carry `xreg(rs1)` (base address);
    * `b` lanes carry `xreg(rs2)` (store value).

    The 2-vs-4/8 byte distinction manifests on the memory-bus write
    entry as a high-byte-zeroing hypothesis on `entry.x2..x7` supplied
    by the caller (SH zeros six lanes; SW zeros four; SD zeros none).

    **Trust basis.** Pure spec of `fn store_op` in
    `riscv2zisk_context.rs:828` specialized to `w = 2`. Direct
    transposition of `transpile_SW`. -/
axiom transpile_SH :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SB (store byte).

    Per `zisk/core/src/riscv2zisk_context.rs:220` an RV64 SB
    `rs2, imm(rs1)` transpiles via `self.store_op(i, "copyb", 1, 4)`
    (line 828) to exactly one Zisk microinstruction. Main-AIR row shape
    identical to SH/SW/SD modulo the `ind_width = 1` fact that surfaces
    only on the memory-bus entry.

    * `op = OP_COPYB = 1` — shared store-family opcode;
    * `is_external_op = 0` — OpType::Internal;
    * `m32 = 0`, `set_pc = 0`, `store_pc = 0`;
    * `jmp_offset1 = jmp_offset2 = 4`;
    * `a` lanes = `xreg(rs1)`; `b` lanes = `xreg(rs2)`.

    SB's high-byte-zeroing witness covers `entry.x1..x7` (seven lanes,
    vs SH's six and SW's four).

    **Trust basis.** Pure spec of `fn store_op` in
    `riscv2zisk_context.rs:828` specialized to `w = 1`. Direct
    transposition of `transpile_SW`. -/
axiom transpile_SB :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SLL.

    Per `zisk/core/src/riscv2zisk_context.rs:135` an RV64 SLL
    `rd, rs1, rs2` transpiles via `create_register_op(instr, "sll", 4)`
    (line 631) to exactly one Zisk microinstruction:
    * `op = OP_SLL = 0x21 = 33` (`zisk_ops.rs:413`, type `BinaryE`);
    * `is_external_op = 1` — bus hop to `BinaryExtension` SM;
    * `m32 = 0` — SLL is the full 64-bit shift (vs SLLW's 32-bit);
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
    * `flag = 0`.

    `a` / `b` lanes carry the full 64-bit `xreg(rs1)` / `xreg(rs2)`.

    **Trust basis.** Direct transposition of `transpile_SLLW` with
    `OP_SLL_W → OP_SLL` and `m32 = 1 → m32 = 0`. SRL/SRA mirror this
    with `OP_SRL`/`OP_SRA`. -/
axiom transpile_SLL :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SLL →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SRL.

    Per `zisk/core/src/riscv2zisk_context.rs:139` an RV64 SRL
    transpiles via `create_register_op(instr, "srl", 4)`. Emitted row
    mirrors SLL with `op = OP_SRL = 0x22 = 34` (`zisk_ops.rs:414`).
    The direction of the shift (logical-right) is dispatched inside the
    `BinaryExtension` SM based on the `op` field.

    **Trust basis.** Direct transposition of `transpile_SLL` with
    `OP_SLL → OP_SRL`. -/
axiom transpile_SRL :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRL →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SRA.

    Per `zisk/core/src/riscv2zisk_context.rs:140` an RV64 SRA
    transpiles via `create_register_op(instr, "sra", 4)`. Emitted row
    mirrors SLL with `op = OP_SRA = 0x23 = 35` (`zisk_ops.rs:415`).
    The direction of the shift (arithmetic-right) is dispatched inside
    the `BinaryExtension` SM based on the `op` field.

    **Trust basis.** Direct transposition of `transpile_SLL` with
    `OP_SLL → OP_SRA`. -/
axiom transpile_SRA :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRA →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- Zisk-side representation of a 6-bit shift-amount immediate.

    The transpiler helper `immediate_op` at
    `zisk/core/src/riscv2zisk_context.rs:853-864` emits
    `zib.src_b("imm", i.imm as u64, false)`. For SLLI/SRLI/SRAI
    `i.imm` is the 6-bit shamt (RV64 shift amounts are `log2(XLEN) = 6`
    bits); as a u64 this is just `shamt.toNat` with zero high bits.

    In the Main row this is split into two 32-bit lanes:
    * `b_lo = shamt.toNat` (always fits — shamt < 64);
    * `b_hi = 0` (the u64 of a 6-bit value has zero high half). -/
def shamt_b_lo (shamt : BitVec 6) : FGL :=
  ⟨shamt.toNat, by
    have : shamt.toNat < 64 := shamt.isLt
    omega⟩

/-- The axiomatic RV64 → Zisk row contract for SLLI.

    Per `zisk/core/src/riscv2zisk_context.rs:175` an RV64 SLLI
    `rd, rs1, shamt` transpiles via `immediate_op(instr, "sll", 4)`
    (line 853) to exactly one Zisk microinstruction:
    * `op = OP_SLL = 33` — **same op-string as SLL** (the
      `BinaryExtension` SM cannot distinguish SLL from SLLI; they share
      the same Zisk opcode literal);
    * `is_external_op = 1`, `flag = 0`, `m32 = 0`;
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
    * `a_lo = lane_lo (xreg rs1)`, `a_hi = lane_hi (xreg rs1)`;
    * `b_lo = shamt.toNat` (the 6-bit immediate as a field element),
      `b_hi = 0` (the u64-extended shamt has no high lane).

    The only structural difference from `transpile_SLL` is the `b`
    source: `immediate_op` uses `"imm"`/`i.imm as u64` whereas
    `create_register_op` uses `"reg"`/`i.rs2`. The Main-AIR bus
    emission is identical (b-source-agnostic — the Main row treats
    `b_lo`/`b_hi` as data regardless of how they got there).

    **Trust basis.** Pure spec of the `"slli"` arm of the ITYPE
    dispatch in `riscv2zisk_context.rs:175`. SRLI / SRAI mirror this
    with `OP_SRL` / `OP_SRA`. -/
axiom transpile_SLLI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SLL →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = shamt_b_lo shamt
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for SRLI.

    Per `zisk/core/src/riscv2zisk_context.rs:179`. Same shape
    as `transpile_SLLI` with `OP_SLL → OP_SRL`. -/
axiom transpile_SRLI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRL →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = shamt_b_lo shamt
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for SRAI.

    Per `zisk/core/src/riscv2zisk_context.rs:180`. Same shape
    as `transpile_SLLI` with `OP_SLL → OP_SRA`. -/
axiom transpile_SRAI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRA →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = shamt_b_lo shamt
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for SRLW
    (`ShiftArchetype` sibling of SLLW, register variant).

    Per `zisk/core/src/riscv2zisk_context.rs:156` an RV64 SRLW
    `rd, rs1, rs2` transpiles via `create_register_op(instr, "srl_w", 4)`.
    Emitted row mirrors SLLW with `op = OP_SRL_W = 37` (`zisk_ops.rs:417`).
    The direction of the shift (logical-right) is dispatched inside the
    `BinaryExtension` SM based on the `op` field.

    **Trust basis.** Direct transposition of `transpile_SLLW` with
    `OP_SLL_W → OP_SRL_W`. SRAW mirrors with `OP_SRA_W`. -/
axiom transpile_SRLW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRL_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SRAW
    (`ShiftArchetype` sibling of SLLW/SRLW, register variant).

    Per `zisk/core/src/riscv2zisk_context.rs:157` an RV64 SRAW
    `rd, rs1, rs2` transpiles via `create_register_op(instr, "sra_w", 4)`.
    Emitted row mirrors SLLW/SRLW with `op = OP_SRA_W = 38`
    (`zisk_ops.rs:418`). The direction of the shift
    (arithmetic-right, signed) is dispatched inside the
    `BinaryExtension` SM based on the `op` field. `m32 = 1` zeroes the
    bus's high lanes so only the low 32 bits reach the SM.

    **Trust basis.** Direct transposition of `transpile_SLLW` with
    `OP_SLL_W → OP_SRA_W`. -/
axiom transpile_SRAW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRA_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- Zisk-side representation of a 5-bit W-variant shift-amount immediate.

    The transpiler helper `immediate_op` at
    `zisk/core/src/riscv2zisk_context.rs:853-864` emits
    `zib.src_b("imm", i.imm as u64, false)` — the `imm` field of the
    RISC-V I-type encoding is parsed as a `u64`. For the W-variant
    immediate shifts (SLLIW, SRLIW, SRAIW) the shift amount is a
    5-bit field (per the RV32/RV64 spec; funct7 = 0 for the non-sign
    variants, 0x20 for SRAIW; `i.imm` isolates the 5-bit shamt).
    As a u64 this is just `shamt.toNat` with zero high bits.

    In the Main row this is split into two 32-bit lanes:
    * `b_lo = shamt.toNat` (always fits — shamt < 32);
    * `b_hi = 0`. -/
def shamt_w_b_lo (shamt : BitVec 5) : FGL :=
  ⟨shamt.toNat, by
    have : shamt.toNat < 32 := shamt.isLt
    omega⟩

/-- The axiomatic RV64 → Zisk row contract for SLLIW
    (`ShiftArchetype` sibling, W-variant immediate).

    Per `zisk/core/src/riscv2zisk_context.rs:195` an RV64 SLLIW
    `rd, rs1, shamt` transpiles via `immediate_op(instr, "sll_w", 4)`
    (line 853) to exactly one Zisk microinstruction:
    * `op = OP_SLL_W = 36` (type `BinaryE`);
    * `is_external_op = 1`;
    * `m32 = 1` — the `"_w"` suffix enables the 32-bit bus-zeroing;
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
    * `flag = 0`;
    * `zib.src_a("reg", rs1, false)` — `a` lanes carry `xreg(rs1)`;
    * `zib.src_b("imm", i.imm as u64, false)` — `b_lo` carries the
      5-bit shamt zero-extended to u64; `b_hi = 0`.

    **Trust basis.** Pure spec of the `"slliw"` arm of the ITYPEW
    dispatch in `riscv2zisk_context.rs:195`. SRLIW / SRAIW mirror this
    with `OP_SRL_W` / `OP_SRA_W` — same bus shape, different
    secondary-SM opcode. -/
axiom transpile_SLLIW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SLL_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = shamt_w_b_lo shamt
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for SRLIW.

    Per `zisk/core/src/riscv2zisk_context.rs:196`. Same shape as
    `transpile_SLLIW` with `OP_SLL_W → OP_SRL_W`. -/
axiom transpile_SRLIW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRL_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = shamt_w_b_lo shamt
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for SRAIW.

    Per `zisk/core/src/riscv2zisk_context.rs:197`. Same shape as
    `transpile_SLLIW` with `OP_SLL_W → OP_SRA_W`. -/
axiom transpile_SRAIW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SRA_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = shamt_w_b_lo shamt
      ∧ m.b_1 r_main = 0

/-- The axiomatic RV64 → Zisk row contract for MULHU.

    Per `zisk/core/src/riscv2zisk_context.rs:246` an RV64 MULHU
    `rd, rs1, rs2` transpiles via
    `create_register_op(..., "muluh", 4)` — note the string rename
    (`"mulhu" → "muluh"`). Differs from the former MULH transpile contract
    only in the opcode literal (181 → 177). One Main-AIR row with:

    * `op = OP_MULUH = 177`;
    * `is_external_op = 1` — dispatch to Arith SM over the operation bus;
    * `set_pc = 0`, `store_pc = 0` — MULHU does not touch PC;
    * `jmp_offset1 = jmp_offset2 = 4` — fall-through advance;
    * `m32 = 0` — 64-bit operand form (the `"muluh"` op string has no
      `_w` suffix);
    * `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)` same as MUL;
    * `flag` is populated by the Arith bus-pop with `div_by_zero = 0`.

    **Trust basis.** Pure spec of the `"mulhu"` arm in
    `riscv2zisk_context.rs:246`. Differs from the former MULH contract only
    in the opcode literal (181 → 177). -/
axiom transpile_MULHU :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_MULUH →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for LUI (load-upper-immediate).

    Per `zisk/core/src/riscv2zisk_context.rs:1009` an RV64 LUI
    `rd, imm` transpiles via `self.lui(i, 4)` to exactly one Zisk
    microinstruction emitted by `ZiskInstBuilder`:
    * `zib.src_a("imm", 0, false)` — `a` lanes are 0;
    * `zib.src_b("imm", i.imm as u64, false)` — `b_src_imm = 1`,
      `b_offset_imm0 = imm`. Main constraint `b_src_imm * (b - b_imm) = 0`
      (`main.pil:390`) forces `b = imm`;
    * `zib.op("copyb")` — ZisK `OP_COPYB = 1`, `OpType::Internal`. With
      `is_external_op = 0` + `op = 1`, Main constraints 9/16 force
      `c = b`, no operation-bus hop;
    * `zib.store("reg", rd, false, false)` — `store_reg = 1`, `store_pc = 0`.
      PIL `store_value[0] = store_pc * (pc + jmp_offset2 - c[0]) + c[0] = c[0]`
      when `store_pc = 0`, so rd receives `c = b = imm` verbatim;
    * `zib.j(4, 4)` — `jmp_offset1 = jmp_offset2 = 4`. No `set_pc()` call,
      so `set_pc = 0`. With `flag = 0` (forced by constraint 18 under
      internal-op-1) and `set_pc = 0`, the PC handshake yields
      `next_pc = pc + jmp_offset2 = pc + 4`;
    * `m32 = 0` — LUI is a 64-bit operation (though `copyb` has no `_w`
      variant anyway).

    **Trust basis.** Pure spec of `fn lui` in `riscv2zisk_context.rs:1009`.
    The Sail-side semantics write `signExtend 64 (imm ++ 0#12)` to rd;
    the circuit writes `b` with `b_lo = imm[11:0] ++ 0#12` (low 32 bits)
    and `b_hi = signExtend(imm[19:12])` (high 32 bits). The lane-level
    transpile axiom pins only the `b_lo`/`b_hi` decomposition; the
    sign-extension identity between Goldilocks lanes and the BitVec 64
    target is discharged in `Equivalence.Lui`. -/
axiom transpile_LUI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_lo imm_hi : FGL) (_state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = 0
      ∧ m.a_1 r_main = 0
      ∧ m.b_0 r_main = imm_lo
      ∧ m.b_1 r_main = imm_hi

/-- The axiomatic RV64 → Zisk row contract for AUIPC (add-upper-immediate-PC).

    Per `zisk/core/src/riscv2zisk_context.rs:907` an RV64 AUIPC
    `rd, imm` transpiles via `self.auipc(i)` to exactly one Zisk
    microinstruction emitted by `ZiskInstBuilder`:
    * `zib.src_a("imm", 0, false)` — `a` lanes are 0;
    * `zib.src_b("imm", 0, false)` — `b` lanes are 0;
    * `zib.op("flag")` — ZisK `OP_FLAG = 0`, `OpType::Internal`. With
      `is_external_op = 0` + `op = 0`, Main constraints 8/15 force
      `c = 0` and constraint 17 forces `flag = 1`;
    * `zib.store_pc("reg", i.rd as i64, false)` — `store_pc = 1`,
      `store_reg = 1`. PIL `store_value[0] = 1*(pc + jmp_offset2 - c[0]) + c[0]
      = pc + jmp_offset2` when `c[0] = 0`;
    * `zib.j(4, i.imm as i64)` — **`jmp_offset1 = 4`,
      `jmp_offset2 = imm`**. AUIPC uniquely uses `jmp_offset2` for the
      AUIPC immediate since that's the "default" (not-taken / no-flag)
      offset, and for AUIPC the rd store path uses `jmp_offset2`. The
      PC handshake at `set_pc = 0, flag = 1` is
      `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)
              = pc + imm + (4 - imm) = pc + 4`;
    * No `set_pc()` call, so `set_pc = 0`;
    * `m32 = 0` — AUIPC is 64-bit.

    **Trust basis.** Pure spec of `fn auipc` in
    `riscv2zisk_context.rs:907`. The Sail-side semantics write
    `pc + signExtend 64 (imm ++ 0#12)` to rd; the circuit writes
    `pc + jmp_offset2` where `jmp_offset2` is the sign-extended
    20-bit-immediate-shifted-left-by-12 value. The lane-level
    transpile axiom pins `jmp_offset2 = imm_offset` (the
    caller-supplied Goldilocks representative of the 32-bit-signed
    AUIPC offset). -/
axiom transpile_AUIPC :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_FLAG →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 1
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = imm_offset
      ∧ m.a_0 r_main = 0
      ∧ m.a_1 r_main = 0
      ∧ m.b_0 r_main = 0
      ∧ m.b_1 r_main = 0

/-! ## ALU RTYPE opcodes

    Six transpile axioms for the ALU-RTYPE fan-out: SUB, AND, OR, XOR,
    SLT, SLTU. All six route through `create_register_op`
    (`riscv2zisk_context.rs:134-152`), so the row shape is identical to
    `transpile_ADD` modulo the Zisk opcode literal. SLT / SLTU
    additionally leave `flag` unconstrained because the Binary SM's
    `flag` output carries the comparison verdict. -/

/-- Goldilocks literal for the SUB opcode. `0x0b = 11` per
    `zisk/core/src/zisk_ops.rs:393` (`"sub"`, Binary type).
    Used by RV64 SUB (`riscv2zisk_context.rs:134`,
    `create_register_op(..., "sub", 4)`). -/
@[simp] def OP_SUB : FGL := 11

-- `OP_LT` and `OP_LTU` are defined earlier in this file (BLT / BGE /
-- BLTU / BGEU branches share them). SLT / SLTU reuse those literals.

/-- Goldilocks literal for the AND opcode. `0x0e = 14` per
    `zisk/core/src/zisk_ops.rs:396` (`"and"`, Binary type).
    Used by RV64 AND (`riscv2zisk_context.rs:152`,
    `create_register_op(..., "and", 4)`) and ANDI (line 182). -/
@[simp] def OP_AND : FGL := 14

/-- Goldilocks literal for the OR opcode. `0x0f = 15` per
    `zisk/core/src/zisk_ops.rs:397` (`"or"`, Binary type).
    Used by RV64 OR (`riscv2zisk_context.rs:149`,
    `create_register_op(..., "or", 4)` — inside the `"or"` arm's
    enclosing block at lines 141-150, whose terminal statement is
    this `create_register_op`) and ORI (line 181). -/
@[simp] def OP_OR : FGL := 15

/-- Goldilocks literal for the XOR opcode. `0x10 = 16` per
    `zisk/core/src/zisk_ops.rs:398` (`"xor"`, Binary type).
    Used by RV64 XOR (`riscv2zisk_context.rs:138`,
    `create_register_op(..., "xor", 4)`) and XORI (line 178). -/
@[simp] def OP_XOR : FGL := 16

/-- The axiomatic RV64 → Zisk row contract for SUB.

    Per `zisk/core/src/riscv2zisk_context.rs:134` an RV64 SUB
    `rd, rs1, rs2` transpiles via `create_register_op(..., "sub", 4)`
    — the identical helper ADD uses. Row shape mirrors
    `transpile_ADD` with the opcode literal changed:

    * `op = OP_SUB = 11` (Binary type, `zisk_ops.rs:393`);
    * `is_external_op = 1` — dispatch to Binary SM via operation bus;
    * `m32 = 0` — 64-bit; the 32-bit SUBW uses `OP_SUB_W` (separate
      axiom);
    * `flag = 0` — `op_sub` returns `(_, false)`
      (`zisk_ops.rs:585`); Binary SM emits flag = 0 on the bus;
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`
      — `zib.j(4, 4)` fall-through;
    * `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)`.

    **Trust basis.** Pure spec of the `"sub"` arm in
    `riscv2zisk_context.rs:134`. -/
axiom transpile_SUB :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SUB →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for AND.

    Per `zisk/core/src/riscv2zisk_context.rs:152` an RV64 AND
    `rd, rs1, rs2` transpiles via `create_register_op(..., "and", 4)`.
    Shape identical to `transpile_SUB` modulo opcode literal.

    * `op = OP_AND = 14`;
    * `flag = 0` — `op_and` returns `(_, false)`
      (`zisk_ops.rs:861`);
    * all other columns identical to `transpile_SUB`.

    **Trust basis.** Pure spec of the `"and"` arm. -/
axiom transpile_AND :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_AND →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for OR.

    Per `zisk/core/src/riscv2zisk_context.rs:141-150` an RV64 OR
    `rd, rs1, rs2` transpiles via `create_register_op(..., "or", 4)`.
    The `"or"` arm in Rust has an outer block that is purely
    organizational; the terminal microinstruction emission (line 149)
    is the same plain `create_register_op` SUB / AND / XOR use.

    * `op = OP_OR = 15`;
    * `flag = 0` — `op_or` returns `(_, false)`
      (`zisk_ops.rs:873`);
    * all other columns identical to `transpile_SUB`.

    **Trust basis.** Pure spec of the `"or"` arm. -/
axiom transpile_OR :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_OR →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for XOR.

    Per `zisk/core/src/riscv2zisk_context.rs:138` an RV64 XOR
    `rd, rs1, rs2` transpiles via `create_register_op(..., "xor", 4)`.
    Shape identical to `transpile_SUB` modulo opcode literal.

    * `op = OP_XOR = 16`;
    * `flag = 0` — `op_xor` returns `(_, false)`
      (`zisk_ops.rs:885`);
    * all other columns identical to `transpile_SUB`.

    **Trust basis.** Pure spec of the `"xor"` arm. -/
axiom transpile_XOR :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_XOR →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SLT.

    Per `zisk/core/src/riscv2zisk_context.rs:136` an RV64 SLT
    `rd, rs1, rs2` transpiles via `create_register_op(..., "lt", 4)`
    — the Rust string `"lt"` routes through the shared `OP_LT = 7`
    opcode (`zisk_ops.rs:389`), the **same** opcode used by BLT / BGE.
    The distinction: SLT reads the Binary-SM's `flag` output as the
    boolean result written to `c`; BLT / BGE use the same flag purely
    for PC dispatch.

    * `op = OP_LT = 7`;
    * `is_external_op = 1`;
    * `m32 = 0`;
    * **`flag` is left unconstrained** — `op_lt` returns `(1, true)`
      when `a < b` and `(0, false)` otherwise (`zisk_ops.rs:741`), so
      the flag is an *output* the Binary SM writes via the bus;
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
    * `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)`.

    **Trust basis.** Pure spec of the `"slt"` arm in
    `riscv2zisk_context.rs:136`. -/
axiom transpile_SLT :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_LT →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SLTU.

    Per `zisk/core/src/riscv2zisk_context.rs:137` an RV64 SLTU
    `rd, rs1, rs2` transpiles via `create_register_op(..., "ltu", 4)`.
    Shape identical to `transpile_SLT` modulo opcode literal
    (`OP_LT → OP_LTU`).

    * `op = OP_LTU = 6`;
    * **`flag` is unconstrained** — output of the Binary SM
      (`op_ltu`, `zisk_ops.rs:724`).

    **Trust basis.** Pure spec of the `"sltu"` arm. -/
axiom transpile_SLTU :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_LTU →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-! ## ALU ITYPE opcodes

    Six transpile axioms for the ALU-ITYPE fan-out: ADDI,
    ANDI, ORI, XORI, SLTI, SLTIU. All six route through either
    `immediate_op` (SLLI-style) or `immediate_op_or_x0_copyb` (ADDI,
    XORI, ORI — which collapse to `copyb` when `rs1 = x0`). The
    non-`copyb` emission path is identical in shape to the R-type
    siblings except:

    * `a` lanes carry `xreg(rs1)` — same as RTYPE;
    * `b` lanes carry the sign-extended 12-bit immediate packed into
      `(imm_b_lo, imm_b_hi)`. The Rust code reads `i.imm as u64` where
      `i.imm : i32` — so the RV64 ITYPE 12-bit immediate is first
      sign-extended to `i32`, then zero-extended (bit-for-bit as u64)
      before splitting into 32-bit lanes. Matching the Sail side
      (`BitVec.signExtend 64 input.imm`) happens at the bus / bus-entry
      match level in downstream `Equivalence/*` modules; the transpile
      axiom itself leaves `imm_b_lo` and `imm_b_hi` as free parameters
      the caller supplies (mirroring the `imm_lo` / `imm_hi` treatment
      in `transpile_LUI`).

    **Scope note.** These axioms cover only the non-degenerate
    (`rs1 ≠ x0`) path of `immediate_op_or_x0_copyb`. The `rs1 = x0`
    path rewrites to `copyb` and changes the emitted opcode; we do not
    exercise it since the Sail pure specs for ADDI / ORI / XORI unify
    it via the same arithmetic identity on `x0`. If needed, a distinct
    `transpile_ADDI_x0` axiom would mirror `transpile_LUI`. -/

/-- The axiomatic RV64 → Zisk row contract for ADDI.

    Per `zisk/core/src/riscv2zisk_context.rs:160-174` an RV64
    ADDI `rd, rs1, imm` transpiles (on the non-degenerate path,
    `rd ≠ 0 ∧ ¬(imm = 0 ∧ rs1 ≠ 0)`) via
    `immediate_op_or_x0_copyb(..., "add", 4)` — reusing **`OP_ADD`**
    (`zisk_ops.rs`) since the Binary-SM cannot distinguish ADD from
    ADDI; they share the same Zisk opcode literal.

    * `op = OP_ADD = 10`;
    * `is_external_op = 1` — dispatch to Binary SM via operation bus;
    * `flag = 0` — `op_add` always returns `(_, false)`;
    * `m32 = 0` — 64-bit ADD (ADDIW uses `OP_ADD_W`, separate axiom);
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
    * `a_lo = lane_lo (xreg rs1)`, `a_hi = lane_hi (xreg rs1)`;
    * `b_lo = imm_b_lo`, `b_hi = imm_b_hi` — caller-supplied
      Goldilocks representatives of the sign-extended 12-bit ITYPE
      immediate's 32-bit lanes.

    **Trust basis.** Pure spec of the `"addi"` arm of
    `riscv2zisk_context.rs:160`. ANDI, ORI, XORI mirror this with
    `OP_ADD → OP_{AND,OR,XOR}`; SLTI / SLTIU with `OP_ADD → OP_{LT,LTU}`
    and `flag` left unconstrained (the Binary-SM writes the verdict).

    **Piggyback note.** ADDI and ADD share `OP_ADD`; the distinction is
    transpiler-internal (`create_register_op` vs.
    `immediate_op_or_x0_copyb`). The bus shape is agnostic — Main's
    row simply carries whatever `(b_lo, b_hi)` values the transpiler
    emits, registered or immediate. -/
axiom transpile_ADDI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_ADD →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_b_lo
      ∧ m.b_1 r_main = imm_b_hi

/-- The axiomatic RV64 → Zisk row contract for ANDI.

    Per `zisk/core/src/riscv2zisk_context.rs:182` an RV64 ANDI
    `rd, rs1, imm` transpiles via `immediate_op(..., "and", 4)` —
    reusing `OP_AND = 14` (shared with AND). Shape identical to
    `transpile_ADDI` modulo opcode literal.

    * `op = OP_AND = 14`;
    * `flag = 0` — `op_and` returns `(_, false)`;
    * all other columns identical to `transpile_ADDI`.

    **Trust basis.** Pure spec of the `"andi"` arm. -/
axiom transpile_ANDI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_AND →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_b_lo
      ∧ m.b_1 r_main = imm_b_hi

/-- The axiomatic RV64 → Zisk row contract for ORI.

    Per `zisk/core/src/riscv2zisk_context.rs:181` an RV64 ORI
    `rd, rs1, imm` transpiles via
    `immediate_op_or_x0_copyb(..., "or", 4)` — reusing `OP_OR = 15`
    (shared with OR). Shape identical to `transpile_ADDI` modulo
    opcode literal.

    * `op = OP_OR = 15`;
    * `flag = 0` — `op_or` returns `(_, false)`;
    * all other columns identical to `transpile_ADDI`.

    **Trust basis.** Pure spec of the `"ori"` arm. -/
axiom transpile_ORI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_OR →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_b_lo
      ∧ m.b_1 r_main = imm_b_hi

/-- The axiomatic RV64 → Zisk row contract for XORI.

    Per `zisk/core/src/riscv2zisk_context.rs:178` an RV64 XORI
    `rd, rs1, imm` transpiles via
    `immediate_op_or_x0_copyb(..., "xor", 4)` — reusing `OP_XOR = 16`
    (shared with XOR). Shape identical to `transpile_ADDI` modulo
    opcode literal.

    * `op = OP_XOR = 16`;
    * `flag = 0` — `op_xor` returns `(_, false)`;
    * all other columns identical to `transpile_ADDI`.

    **Trust basis.** Pure spec of the `"xori"` arm. -/
axiom transpile_XORI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_XOR →
        m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_b_lo
      ∧ m.b_1 r_main = imm_b_hi

/-- The axiomatic RV64 → Zisk row contract for SLTI.

    Per `zisk/core/src/riscv2zisk_context.rs:176` an RV64 SLTI
    `rd, rs1, imm` transpiles via `immediate_op(..., "lt", 4)` —
    reusing `OP_LT = 7` (shared with BLT / BGE / SLT). Like SLT, the
    Binary-SM's `flag` output carries the signed comparison verdict
    and is written to `c`; the transpile axiom leaves `flag`
    unconstrained.

    * `op = OP_LT = 7`;
    * `is_external_op = 1`;
    * **`flag` left unconstrained** — Binary-SM output;
    * `m32 = 0`, `set_pc = 0`, `store_pc = 0`,
      `jmp_offset1 = jmp_offset2 = 4`;
    * `a` lanes = `xreg(rs1)`; `b` lanes = sign-extended immediate.

    **Trust basis.** Pure spec of the `"slti"` arm. -/
axiom transpile_SLTI :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_LT →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_b_lo
      ∧ m.b_1 r_main = imm_b_hi

/-- The axiomatic RV64 → Zisk row contract for SLTIU.

    Per `zisk/core/src/riscv2zisk_context.rs:177` an RV64 SLTIU
    `rd, rs1, imm` transpiles via `immediate_op(..., "ltu", 4)` —
    reusing `OP_LTU = 6` (shared with BLTU / BGEU / SLTU). Shape
    identical to `transpile_SLTI` modulo `OP_LT → OP_LTU`. Note that
    SLTIU's immediate is **still sign-extended** to 64 bits (per the
    RV64I spec), then compared as unsigned — the immediate encoding
    on the bus is identical to SLTI; only the Binary-SM's comparator
    is unsigned.

    **Trust basis.** Pure spec of the `"sltiu"` arm. -/
axiom transpile_SLTIU :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_LTU →
        m.m32 r_main = 0
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_b_lo
      ∧ m.b_1 r_main = imm_b_hi

/-! ## RTYPEW / ADDIW transpile axioms

Three transpile axioms for the 32-bit-word ALU opcodes ADDW, SUBW,
and ADDIW. All three mirror the `m32 = 1` path taken by the shift
archetype (SLLW / SRLW / SRAW), except they dispatch to the
**Binary** SM (not `BinaryExtension`) with distinct `OP_ADD_W` /
`OP_SUB_W` literals. ADDIW shares the row shape with ADDW modulo the
immediate-vs-register b-source (immediate form — `b_lo`/`b_hi` carry
the sign-extended 12-bit immediate lanes).

**ADDIW routing finding.** `zisk/core/src/riscv2zisk_context.rs:184-194`:
the `"addiw"` arm calls `immediate_op(..., "add_w", 4)` (line 192) —
i.e. **OP_ADD_W + m32 = 1**, *not* `OP_ADD` with `m32 = 1`. (The
preceding `if rd == 0 && rs1 == 0 && imm == 0` branch emits a nop;
that degenerate instance is outside the per-opcode axiom's scope —
`transpile_ADDIW` quantifies over the nominal register/imm shape.) -/

/-- The axiomatic RV64 → Zisk row contract for ADDW.

    Per `zisk/core/src/riscv2zisk_context.rs:153` an RV64 ADDW
    `rd, rs1, rs2` transpiles via `create_register_op(..., "add_w", 4)`
    — the identical helper ADD / SUB use. Row shape mirrors
    `transpile_ADD` / `transpile_SUB` with:

    * `op = OP_ADD_W = 26` (Binary type, `zisk_ops.rs:408`);
    * `is_external_op = 1` — dispatch to Binary SM via operation bus;
    * `m32 = 1` — `"add_w".contains("_w")` is `true`
      (`zisk_inst_builder.rs:206`). Zeroes the high-lane bus hops per
      PIL `a = [a[0], (1 - m32) * a[1]]`;
    * `flag = 0` — `op_add_w` returns `(_, false)`
      (`zisk_ops.rs:572`); Binary SM emits flag = 0 on the bus;
    * `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`
      — `zib.j(4, 4)` fall-through;
    * `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)` (the full 64-bit
      value; the `m32 = 1` bit signals bus-zeroing of high lanes
      downstream).

    **Trust basis.** Pure spec of the `"addw"` arm in
    `riscv2zisk_context.rs:153`. -/
axiom transpile_ADDW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_ADD_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for SUBW.

    Per `zisk/core/src/riscv2zisk_context.rs:154` an RV64 SUBW
    `rd, rs1, rs2` transpiles via `create_register_op(..., "sub_w", 4)`.
    Row shape mirrors `transpile_ADDW` with the opcode literal
    changed:

    * `op = OP_SUB_W = 27` (Binary type, `zisk_ops.rs:409`);
    * `flag = 0` — `op_sub_w` returns `(_, false)`
      (`zisk_ops.rs:596`);
    * all other fields identical to `transpile_ADDW`.

    **Trust basis.** Pure spec of the `"subw"` arm in
    `riscv2zisk_context.rs:154`. -/
axiom transpile_SUBW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_SUB_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = lane_lo (state.xreg rs2)
      ∧ m.b_1 r_main = lane_hi (state.xreg rs2)

/-- The axiomatic RV64 → Zisk row contract for ADDIW.

    Per `zisk/core/src/riscv2zisk_context.rs:184-194` an RV64
    ADDIW `rd, rs1, imm` transpiles via `immediate_op(..., "add_w", 4)`
    (line 192) — **OP_ADD_W with m32 = 1**, distinct from ADDI's
    OP_ADD-with-m32=0 routing. The degenerate `rd=0, rs1=0, imm=0`
    case emits a nop (line 190); that sub-case is outside the nominal
    row shape this axiom pins.

    The emitted row:
    * `op = OP_ADD_W = 26`;
    * `is_external_op = 1`, type `Binary`;
    * `m32 = 1` — 32-bit add then sign-extend to 64;
    * `flag = 0`; `set_pc = 0`, `store_pc = 0`;
    * `jmp_offset1 = jmp_offset2 = 4`;
    * `zib.src_a("reg", rs1, false)` — `a` lanes carry
      `xreg(rs1)`;
    * `zib.src_b("imm", i.imm as u64, false)` — `b` lanes carry the
      RISC-V I-type 12-bit immediate sign-extended to 64 bits (via
      `i32 → i64 → u64`). Caller supplies `imm_lo`/`imm_hi` as the
      32-bit lane decomposition of this sign-extended value.

    **Trust basis.** Pure spec of the `"addiw"` arm in
    `riscv2zisk_context.rs:184-194`. Shape mirrors SLLIW
    (`transpile_SLLIW`) in the `immediate_op` pattern, diverges in
    the `b_lo`/`b_hi` decomposition (12-bit signed imm vs. 5-bit
    unsigned shamt). The correspondence between `(imm_lo, imm_hi)`
    and the Sail-side `BitVec.signExtend 64 imm` is discharged by
    the Sail-level proof (`equiv_ADDIW_sail`), not by this
    axiom. -/
axiom transpile_ADDIW :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_lo imm_hi : FGL) (state : RV64State),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_ADD_W →
        m.flag r_main = 0
      ∧ m.m32 r_main = 1
      ∧ m.set_pc r_main = 0
      ∧ m.store_pc r_main = 0
      ∧ m.jmp_offset1 r_main = 4
      ∧ m.jmp_offset2 r_main = 4
      ∧ m.a_0 r_main = lane_lo (state.xreg rs1)
      ∧ m.a_1 r_main = lane_hi (state.xreg rs1)
      ∧ m.b_0 r_main = imm_lo
      ∧ m.b_1 r_main = imm_hi

/-- Zisk `signextend_b` opcode (0x27 = 39). `BinaryE` external op
    (`zisk/core/src/zisk_ops.rs:419`). Routes through the
    BinaryExtension SM via the operation bus; populates `c` with
    `sign_extend 8 → 64` of the low byte of `b`. Consumed by LB and
    (out-of-scope here) the sign-extend step of AMO byte-ops. -/
@[simp] def OP_SIGNEXTEND_B : FGL := 39

/-- Zisk `signextend_h` opcode (0x28 = 40). Same SM / bus shape as
    `OP_SIGNEXTEND_B`, with the sign-extension source width bumped to
    16 bits (`zisk/core/src/zisk_ops.rs:420`). Consumed by LH. -/
@[simp] def OP_SIGNEXTEND_H : FGL := 40

/-- Zisk `signextend_w` opcode (0x29 = 41). Same SM / bus shape as
    `OP_SIGNEXTEND_B` / `OP_SIGNEXTEND_H` with the source width at
    32 bits (`zisk/core/src/zisk_ops.rs:421`). Consumed by LW
    (and, out of scope, several atomic-memory ops). -/
@[simp] def OP_SIGNEXTEND_W : FGL := 41

/- ============================================================
   DIV / REM family
   ============================================================

   The DIV subfamily (DIV, DIVU, REM, REMU) all dispatch through the
   Arith state machine via the operation bus, sharing the Zisk
   microinstruction shape `create_register_op(..., <op_str>, 4)` at
   `zisk/core/src/riscv2zisk_context.rs:248-253`:

     "div"  → create_register_op(i, "div",  4)  -- line 248
     "divu" → create_register_op(i, "divu", 4)  -- line 249
     "rem"  → create_register_op(i, "rem",  4)  -- line 252
     "remu" → create_register_op(i, "remu", 4)  -- line 253

   Opcode literals from `zisk/core/src/zisk_ops.rs:430-433`.
-/

/-- Goldilocks literal for the DIVU opcode. `0xb8 = 184` per
    `zisk/core/src/zisk_ops.rs:430`. Unsigned integer division,
    64-bit operands, quotient output (low 64 bits). Dispatched to the
    Arith state machine via the operation bus as the **primary**
    result on a DIV-family Arith row (`main_div = 1`). Used by RV64
    DIVU (`riscv2zisk_context.rs:249`, `create_register_op(...,
    "divu", 4)`). -/
@[simp] def OP_DIVU : FGL := 184

/-- Goldilocks literal for the REMU opcode. `0xb9 = 185` per
    `zisk_ops.rs:431`. Unsigned integer remainder, 64-bit operands,
    remainder output (low 64 bits). Dispatched to the Arith SM as the
    **secondary** result on the same DIV-family Arith row that handles
    DIVU (`main_mul = main_div = 0`, `secondary = 1`). Used by RV64
    REMU (`riscv2zisk_context.rs:253`). -/
@[simp] def OP_REMU : FGL := 185

/-- Goldilocks literal for the DIV opcode. `0xba = 186` per
    `zisk_ops.rs:432`. Signed integer division, 64-bit operands.
    Dispatched to the Arith SM as the **primary** on a signed-DIV row.
    Used by RV64 DIV (`riscv2zisk_context.rs:248`). -/
@[simp] def OP_DIV : FGL := 186

/-- Goldilocks literal for the REM opcode. `0xbb = 187` per
    `zisk_ops.rs:433`. Signed integer remainder, 64-bit operands.
    Dispatched to the Arith SM as the **secondary** on the signed-DIV
    row. Used by RV64 REM (`riscv2zisk_context.rs:252`). -/
@[simp] def OP_REM : FGL := 187

/-- Goldilocks literal for the unsigned 32-bit divide opcode.
    `0xbc = 188` per `zisk/core/src/zisk_ops.rs:434`. Used by
    RV64 DIVUW (`riscv2zisk_context.rs:251`,
    `create_register_op(..., "divu_w", 4)`). Type `ArithA32` — handled
    by the Arith state machine with `m32 = 1`. -/
@[simp] def OP_DIVU_W : FGL := 188

/-- Goldilocks literal for the unsigned 32-bit remainder opcode.
    `0xbd = 189` per `zisk/core/src/zisk_ops.rs:435`. Used by
    RV64 REMUW (`riscv2zisk_context.rs:255`). Type `ArithA32`,
    secondary lane on the same Arith row that produces the quotient. -/
@[simp] def OP_REMU_W : FGL := 189

/-- Goldilocks literal for the signed 32-bit divide opcode.
    `0xbe = 190` per `zisk/core/src/zisk_ops.rs:436`. Used by
    RV64 DIVW (`riscv2zisk_context.rs:250`,
    `create_register_op(..., "div_w", 4)`). Type `ArithA32` — handled
    by the Arith state machine with `m32 = 1, sa = sb = 1`. -/
@[simp] def OP_DIV_W : FGL := 190

/-- Goldilocks literal for the signed 32-bit remainder opcode.
    `0xbf = 191` per `zisk/core/src/zisk_ops.rs:437`. Used by
    RV64 REMW (`riscv2zisk_context.rs:254`). Type `ArithA32`,
    secondary lane on the same Arith row that produces the
    quotient. -/
@[simp] def OP_REM_W : FGL := 191

/-! ## store_pc=1 PC bridges

    The three axioms below — `transpile_PC_for_JAL`,
    `transpile_PC_for_JALR`, and `transpile_PC_for_AUIPC` — extend the
    transpiler's trusted surface to expose the **runtime PC value**
    pinned at the Main-AIR row, supporting the `store_pc = 1` archetype.

    ### Why they are trust-class items

    The existing `transpile_<OP>` axioms (e.g. `transpile_JAL`,
    `transpile_AUIPC`) pin the *operand and selector* columns of the
    Main row (`a`, `b`, `op`, `is_external_op`, `m32`, `set_pc`,
    `store_pc`, `jmp_offset1/2`). They do **not** pin the value of the
    `pc` column itself — `pc` is a witness column whose value is
    determined per row by ZisK's ROM/segment infrastructure (PIL
    constraint 20 — `(1 - SEGMENT_L1) * (pc - expected_current_pc) === 0`,
    `main.pil:410`) and the Main AIR's continuation handshake from the
    previous segment, neither of which is currently extracted.

    For the `store_pc = 1` opcodes (JAL, JALR, AUIPC) the rd-write
    formula at `main.pil:311`:

    ```
      store_value[0] = store_pc * (pc + jmp_offset2 - c[0]) + c[0]
    ```

    collapses to `pc + jmp_offset2`. To prove the rd-write equals the
    Sail-side pure-spec output (`PC + 4` for JAL/JALR;
    `PC + signExtend 64 (imm ++ 0#12)` for AUIPC), downstream Spec /
    Equivalence proofs need to bridge `m.pc r_main` (an `FGL`) to
    `PC` (a `BitVec 64`) — this PC value is *not* recoverable from the
    operand or selector columns the existing transpile axioms cover.

    The bridge belongs in the trusted surface for the same reason the
    operand bridges (`m.a_0 r_main = lane_lo (state.xreg rs1)`,
    etc.) do: it asserts that ZisK's Rust transpiler, when emitting a
    Main row for a Sail-state at PC `P`, sets the `pc` column to a
    representative encoding `P`. Improving these to theorems would
    require:

    1. A formal model of ZisK's ROM (which assigns `pc` per row) and
    2. A bridge between the ROM's per-row `pc` and the Sail-state's
       `state.pc` carried through the program-counter handshake chain.

    Both are tractable and are open avenues for trust reduction; for
    now they are accepted as axioms.

    ### What they assert

    Each axiom takes a `Valid_Main` instance, a row index, the
    Sail-side `PC : BitVec 64`, and the same mode witnesses
    (`is_external_op` + `op` literal) used by the corresponding
    `transpile_<OP>` axiom. It concludes:

    ```
    (m.pc r_main).val = PC.toNat
    ```

    where `m.pc r_main : FGL` and `PC : BitVec 64`. Note that this
    formulation accommodates a **wide PC** — it does not assume `PC <
    2^32` even though ZisK's PIL declares `pc : bits(32)` (a residue of
    ZisK's RV32 origin). Downstream,
    `Fundamentals/PackedBitVec/WidePCNoWrap.lean` handles the FGL-side
    arithmetic to derive the lo / hi half decompositions consumed by
    `JumpUType.lean`.

    ### Discriminating JAL / AUIPC

    JAL and AUIPC share the same opcode-witness pair
    `(is_external_op = 0, op = OP_FLAG)` so the premises of
    `transpile_PC_for_JAL` and `transpile_PC_for_AUIPC` are identical
    on those columns — the axioms are statements about *how the
    transpiler-emitted row encodes PC under each context*, where the
    context is established by the broader proof environment (e.g. the
    JAL-shape `transpile_JAL` already pins `jmp_offset2 = 4` while
    AUIPC's `transpile_AUIPC` pins `jmp_offset2 = imm_offset`). This is
    the same convention the existing `transpile_<OP>` axioms follow:
    they over-specify the row in the context of *one particular Sail
    opcode*, and the caller's surrounding proof determines which
    context applies.
-/

/-- JAL PC bridge.

    Asserts that on a JAL row (`is_external_op = 0`, `op = OP_FLAG`,
    transpile-context per `riscv2zisk_context.rs:201,1098`), the
    Main-AIR `pc` column at row `r_main` carries the Sail-side
    program counter `PC`. Mirrors the operand bridges in
    `transpile_JAL` (which pin `a_0 = state.xreg rs1` etc.) extending
    them to the runtime PC value.

    Together with `transpile_JAL`, this drives the JAL rd-write
    `pc + 4` at the FGL level (lo half of the rd-write 8-byte
    memory-bus entry) under the existing JumpUType discharge chain.

    **Trust class.** Sail-PC ↔ ZisK Main-pc-column contract — the
    transpiler-emits-row faithfulness for the PC witness column.
    Closure path: model ZisK's ROM-based `pc` assignment + the
    cross-segment handshake formally, derive this equality from the
    in-tree pieces. See `docs/fv/trusted-base.md` entry **TP-JAL**. -/
axiom transpile_PC_for_JAL :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (PC : BitVec 64),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_FLAG →
      (m.pc r_main).val = PC.toNat

/-- JALR PC bridge.

    Asserts that on a JALR row (`is_external_op = 0`,
    `op = OP_COPYB`, transpile-context per
    `riscv2zisk_context.rs:200,1025`), the Main-AIR `pc` column at row
    `r_main` carries the Sail-side program counter `PC`.

    JALR transpiles via the simplified internal-copyb shape (with
    `set_pc = 1` so next-pc comes from `c_0 + jmp_offset1 = rs1 + imm`)
    that `transpile_JALR` and the `JumpArchetype` validation lemmas
    consume. The PC bridge composes with that to drive the rd-write
    `pc + 4` derivation in JumpUType.

    **Trust class.** Same as `transpile_PC_for_JAL`. See
    `docs/fv/trusted-base.md` entry **TP-JALR**. -/
axiom transpile_PC_for_JALR :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (PC : BitVec 64),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_COPYB →
      (m.pc r_main).val = PC.toNat

/-- AUIPC PC bridge.

    Asserts that on an AUIPC row (`is_external_op = 0`,
    `op = OP_FLAG`, transpile-context per
    `riscv2zisk_context.rs:907`), the Main-AIR `pc` column at row
    `r_main` carries the Sail-side program counter `PC`.

    AUIPC's rd-write `pc + (imm << 12 sign-extended)` (per
    `main.pil:311` evaluating to `pc + jmp_offset2` with `c_0 = 0`)
    composes this PC bridge with `transpile_AUIPC`'s `jmp_offset2 =
    imm_offset` pin and the wide-PC arithmetic in
    `Fundamentals/PackedBitVec/WidePCNoWrap.lean` to derive the
    rd-write equality at the FGL level.

    Note JAL and AUIPC share the `(is_external_op = 0, op = OP_FLAG)`
    selector pair; this is the same context-overlap convention used by
    `transpile_JAL` / `transpile_AUIPC`. The discriminator is the
    surrounding proof's `transpile_<OP>` axiom invocation, which pins
    `jmp_offset1` / `jmp_offset2` differently for the two opcodes.

    **Trust class.** Same as `transpile_PC_for_JAL`. See
    `docs/fv/trusted-base.md` entry **TP-AUIPC**. -/
axiom transpile_PC_for_AUIPC :
    ∀ (m : Valid_Main FGL FGL) (r_main : ℕ) (PC : BitVec 64),
      m.is_external_op r_main = 0 →
      m.op r_main = OP_FLAG →
      (m.pc r_main).val = PC.toNat

end ZiskFv.Trusted
