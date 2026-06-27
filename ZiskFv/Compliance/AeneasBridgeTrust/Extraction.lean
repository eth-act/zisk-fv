/-
ZiskFv/Compliance/AeneasBridgeTrust/Extraction.lean  (eth-act/zisk-fv#111)

Aggregator: discharges the per-opcode STATIC decode / row-mode pins of all 63
RV64IM opcodes from the REAL Aeneas-extracted ZisK lowerer
(`trust/aeneas/ProductionM2.lean`, the `ProductionM2` lean_lib), kernel-soundly
(NO native_decide / bv_decide / ofReduceBool / trustCompiler / `sorry`).

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

Every opcode gets a `<op>_extracted_rowMode_pins` bridge onto
`mainExtractedRowOfZiskInst` (the `@[reducible]` projection in
`Extraction.Helpers`); per-op `<op>_static_pins` are provided alongside.  All
declarations live in namespace `ZiskFv.Compliance.Extraction`.

Honest side-conditions (preserved, matching the lowerer's branch guards):
  * AUIPC / JAL / JALR `store_pc = true` requires a nonzero destination register
    (the `store_reg` `offset = 0 ⇒ ok self` early-return);
  * ADDI / XORI / ORI op/external/m32 pins require `i.rs1 ≠ 0#u32`
    (`immediate_op_or_x0_copyb_typed` emits CopyB when rs1 = 0).
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.ControlUType
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Branch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.RegisterOp
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Immediate
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.LoadStore
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Precompiled
