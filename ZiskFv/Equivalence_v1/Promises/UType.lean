import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `UTypePromises` — structural promise bundle for U-TYPE opcodes (LUI, AUIPC)

Bundles the eleven structurally-uniform binders that every U-TYPE
canonical `equiv_<OP>` theorem accepts as a single record. Per
`docs/fv/promise-bundles-design.md`.

Marked `@[reducible]` so the V2 trust gate's `whnfR`-driven
`forbidden-types.txt` binder walk continues to see the field types
directly (rather than the opaque `UTypePromises` wrapper) — see the
"design tension" note in the design doc.

## Audit shape

A `UTypePromises` term is constructible iff each of the following
holds (eleven fields, in trust classes the V2 binder walk recognises):

- **Sail-state input bridges** (3): `input_imm_eq`, `input_rd_eq`,
  `input_pc_eq` — pin the U-TYPE input record's `imm`, `rd`, `PC`
  to the Sail-spec values consumed by `execute_instruction`.
- **Execution-bus shape** (4): `exec_len` + multiplicity / `nextPC_matches`.
- **Rd-write memory-bus shape** (2): `rd_mult`, `rd_as`.
- **Pure-spec ↔ bus PC handshake** (1): `nextPC_eq`.
- **Rd-write entry ↔ register-index alignment** (1): `rd_idx`.

Trust class of every field: `CIRCUIT-CONSTRAINT` or `TRANSPILE-BRIDGE`.
None of these are OUTPUT-EQ-class binders (forbidden by
`trust/forbidden-param-shapes.txt`).
-/

namespace ZiskFv.Equivalence_v1.Promises

open ZiskFv.Trusted

/-- Structural promise bundle for U-TYPE opcodes (LUI, AUIPC).

    Note: Lean 4 does not allow `@[reducible]` on `structure`. The V2
    trust gate's binder walk sees this binder as `UTypePromises ...`
    (opaque); the bundle's audit happens once on this file's
    declaration rather than per-opcode-theorem. -/
structure UTypePromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_imm : BitVec 20) (input_rd : Fin 32) (input_pc : BitVec 64)
    (input_nextPC : BitVec 64)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64) where
  /-- The opcode's input record's `imm` field equals the AST's `imm`. -/
  input_imm_eq : input_imm = imm
  /-- The opcode's input record's `rd` field equals the AST's `rd`
      coerced to `Fin 32`. -/
  input_rd_eq : input_rd = regidx_to_fin rd
  /-- The Sail state's PC register equals the input record's `PC`. -/
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  /-- The execution bus has exactly two entries (consumer + producer). -/
  exec_len : exec_row.length = 2
  /-- The first execution-bus entry is a consumer (`multiplicity = -1`). -/
  e0_mult : exec_row[0]!.multiplicity = -1
  /-- The second execution-bus entry is a producer (`multiplicity = 1`). -/
  e1_mult : exec_row[1]!.multiplicity = 1
  /-- The producer entry's PC field equals the AST-side `nextPC_val`. -/
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = nextPC_val
  /-- The rd-write memory-bus entry is a producer. -/
  rd_mult : e_rd.multiplicity = 1
  /-- The rd-write memory-bus entry targets the register address space. -/
  rd_as : e_rd.as.val = 1
  /-- The pure-spec's `nextPC` agrees with the AST-side `nextPC_val`. -/
  nextPC_eq : input_nextPC = nextPC_val
  /-- The input's `rd` agrees with the rd-write entry's `wrap_to_regidx`. -/
  rd_idx : input_rd = Transpiler.wrap_to_regidx e_rd.ptr

end ZiskFv.Equivalence_v1.Promises
