/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction.lean  (eth-act/zisk-fv#111)

Aggregator: discharges the per-opcode STATIC decode / row-mode pins of all 63
RV64IM opcodes from the REAL Aeneas-extracted ZisK lowerer
(`trust/aeneas/ProductionM2.lean`, the `ProductionM2` lean_lib), kernel-soundly
(NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`).

There are TWO layers of per-opcode pins:

  * BUILDER ENTRY-POINT pins (`<op>_static_pins` / `<op>_extracted_rowMode_pins`):
    proven about the builder entry the opcode lowers through
    (`create_register_op_typed`, `immediate_op_typed`, `load_op_typed`, `lui`, …).
    These are the reusable CORE.
  * DISPATCHER-LEVEL pins (`<op>_dispatch_static_pins` /
    `<op>_dispatch_extracted_rowMode_pins`, in `Extraction.Dispatch`): proven
    about the TOP-LEVEL lowerer
    `riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input`,
    stating the EXACT side condition(s) under which it routes the opcode to its
    entry point and then REDUCING to the entry-point lemma.  This addresses the
    external-review finding that the headline "all 63 from the real lowerer" must
    go through the dispatcher, not merely the builder entry points.

The proofs are split, by lowering entry point, across `Extraction/`:

| module                  | entry point(s)                          | opcodes |
|-------------------------|-----------------------------------------|---------|
| `Extraction.Helpers`    | projection + shared frame/store/op_zisk | —       |
| `Extraction.ControlUType` | lui / auipc / jal / jalr / nop        | LUI AUIPC JAL JALR FENCE |
| `Extraction.Branch`     | create_branch_op_typed                  | BEQ BNE BLT BGE BLTU BGEU |
| `Extraction.RegisterOp` | create_register_op_typed                | ADD…REMUW (28 R/W/M ops) |
| `Extraction.Immediate`  | immediate_op_typed / …_x0_copyb_typed   | SLLI…SRAIW, ADDI XORI ORI |
| `Extraction.LoadStore`  | load_op_typed / store_op_typed / copyb  | LB…LD, SB…SD |
| `Extraction.Precompiled`| create_precompiled_op_typed (audit)     | shift/sign-ext (DMA path) |
| `Extraction.Dispatch`   | lower_rv64im_single_row_input (all 63)  | dispatcher-level, all 63 |

Every opcode gets a `<op>_extracted_rowMode_pins` bridge onto
`mainExtractedRowOfZiskInst` (the `@[reducible]` projection in
`Extraction.Helpers`); per-op `<op>_static_pins` are provided alongside, and a
`<op>_dispatch_{static,extracted_rowMode}_pins` pair through the dispatcher.  All
declarations live in namespace `ZiskFv.Compliance.Extraction`.

Honest side-conditions on the DISPATCHER-level theorems (verbatim from the
lowerer's branch guards — see `Extraction.Dispatch` for the full table):
  * Most opcodes route UNCONDITIONALLY (register ALU/M ops, branches, the plain
    immediates SLLI/SRLI/SRAI/SLTI/SLTIU/ANDI/SLLIW/SRLIW/SRAIW, all loads and
    stores, and the LUI/AUIPC/JAL/JALR/FENCE static pins).
  * ADD needs `input_precompile = none`, `rd ≠ 0`, `rs1 ≠ 0`, `rs2 ≠ 0` (the
    DMA-precompile and copyb degeneracies); OR needs `rs1 ≠ 0`, `rs2 ≠ 0`;
    ADDI needs `rd ≠ 0`, `imm ≠ 0`, `rs1 ≠ 0`; ADDIW needs `rd ≠ 0`;
    XORI / ORI need `rs1 ≠ 0`.
  * AUIPC / JAL / JALR `store_pc = true` (row-mode) requires a nonzero
    destination register (the `store_reg` `offset = 0 ⇒ ok self` early-return);
    ADDI / XORI / ORI op/external/m32 pins require `i.rs1 ≠ 0#u32`
    (`immediate_op_or_x0_copyb_typed` emits CopyB when rs1 = 0).
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.ControlUType
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Branch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.RegisterOp
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Immediate
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.LoadStore
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Precompiled
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Dispatch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.DynamicFields
