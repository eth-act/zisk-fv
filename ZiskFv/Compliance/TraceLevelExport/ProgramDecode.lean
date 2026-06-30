import ZiskFv.Compliance.TraceLevelExport.Dispatcher
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps

/-!
# Committed-program row-decode dispatch (issue #159, BLOCK 1 wiring, IN PLACE)

This module wires block 1's per-op `Decode_<op>_of_program`
(`RomDecodeBinding`/`RomDecodeBindingOps`) into the headline `root_soundness`
endpoint (`ZiskFv/Soundness.lean`) by repackaging, per row, exactly the inputs
those derivations consume that are NOT themselves derivable:

* the program-level ROM-decode facts about the COMMITTED program
  `trace.program` (the `∀ j at pc(i)` decodes-as-<op> premise `h_prog`, plus the
  packed flag-bit values `bits` / `h_bits_*`);
* the op's non-ROM operand witnesses (signed-load `BinaryExtension`, shift
  `h_b_lo_t`, the M-ext arith witnesses, JALR / LUI / FENCE pins) — the SAME
  ones block 1 already carried; and
* the structural next-row bound `h_idx`.

`ProgramDecode ziskTrace i zs` is the 63-arm dispatch (mirroring `RowDecode` in
`Dispatcher.lean`) to the per-op bundle `ProgramDecode_<op>`.
`rowDecode_of_programDecode` rebuilds block 1's `RowDecode` for one row by
applying the matching `Decode_<op>_of_program`, so `root_soundness` can take the
committed-program decode bundle and DERIVE the witness-row decode columns.

The ROM-backed decode columns (`op` / flags / `jmp_offset` / `ind_width`) are no
longer assumed on the witness row: they are derived from `trace.program` via the
in-circuit ROM lookup, exactly as block 1 established.

Sound: NO `sorry` / new axiom / `native_decide`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`), inherited from block 1.
-/

namespace ZiskFv.Compliance.RomDecodeBinding

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Trusted
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.Main (romMessage RomFlagBits packFlags romFlags)

set_option maxHeartbeats 1600000

/-- Per-row committed-program decode bundle for `sub`: exactly the inputs
    `Decode_sub_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sub {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sub trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SUB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `and`: exactly the inputs
    `Decode_and_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_and {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_and trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `or`: exactly the inputs
    `Decode_or_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_or {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_or trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `xor`: exactly the inputs
    `Decode_xor_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_xor {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_xor trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `slt`: exactly the inputs
    `Decode_slt_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_slt {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slt trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sltu`: exactly the inputs
    `Decode_sltu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sltu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sltu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `andi`: exactly the inputs
    `Decode_andi_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_andi {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_andi trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `ori`: exactly the inputs
    `Decode_ori_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_ori {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_ori trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_OR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `xori`: exactly the inputs
    `Decode_xori_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_xori {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_xori trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_XOR
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `slti`: exactly the inputs
    `Decode_slti_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_slti {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slti trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sltiu`: exactly the inputs
    `Decode_sltiu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sltiu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sltiu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sll`: exactly the inputs
    `Decode_sll_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sll {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sll trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `srl`: exactly the inputs
    `Decode_srl_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_srl {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srl trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sra`: exactly the inputs
    `Decode_sra_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sra {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sra trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `slli`: exactly the inputs
    `Decode_slli_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_slli {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slli trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `srli`: exactly the inputs
    `Decode_srli_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_srli {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srli trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `srai`: exactly the inputs
    `Decode_srai_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_srai {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srai trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `add`: exactly the inputs
    `Decode_add_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_add {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_add trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `addi`: exactly the inputs
    `Decode_addi_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_addi {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_addi trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `subw`: exactly the inputs
    `Decode_subw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_subw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_subw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SUB_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `addw`: exactly the inputs
    `Decode_addw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_addw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_addw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `addiw`: exactly the inputs
    `Decode_addiw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_addiw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_addiw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_b_src_imm : bits.b_src_imm = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ BitVec.signExtend 64 c.imm
            = BitVec.ofNat 64
                ((trace.program j).b_offset_imm0.val
                  + (trace.program j).b_imm1.val * 4294967296)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sllw`: exactly the inputs
    `Decode_sllw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sllw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sllw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `srlw`: exactly the inputs
    `Decode_srlw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_srlw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srlw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sraw`: exactly the inputs
    `Decode_sraw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sraw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sraw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `slliw`: exactly the inputs
    `Decode_slliw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_slliw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_slliw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SLL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `srliw`: exactly the inputs
    `Decode_srliw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_srliw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_srliw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sraiw`: exactly the inputs
    `Decode_sraiw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sraiw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sraiw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SRA_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `mul`: exactly the inputs
    `Decode_mul_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_mul {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mul trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MUL
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `mulh`: exactly the inputs
    `Decode_mulh_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_mulh {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulh trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `mulhsu`: exactly the inputs
    `Decode_mulhsu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_mulhsu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulhsu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULSUH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `mulw`: exactly the inputs
    `Decode_mulw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_mulw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MUL_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `mulhu`: exactly the inputs
    `Decode_mulhu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_mulhu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_mulhu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_MULUH
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `div`: exactly the inputs
    `Decode_div_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_div {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_div trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIV
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `rem`: exactly the inputs
    `Decode_rem_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_rem {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_rem trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REM
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `divw`: exactly the inputs
    `Decode_divw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_divw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_divw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIV_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `remw`: exactly the inputs
    `Decode_remw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_remw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_remw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  arith_mem :
    ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REM_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `divu`: exactly the inputs
    `Decode_divu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_divu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_divu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIVU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `divuw`: exactly the inputs
    `Decode_divuw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_divuw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_divuw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_DIVU_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `remu`: exactly the inputs
    `Decode_remu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_remu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_remu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REMU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `remuw`: exactly the inputs
    `Decode_remuw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_remuw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_remuw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds :
    ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_REMU_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `beq`: exactly the inputs
    `Decode_beq_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_beq {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_beq trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_EQ
        ∧ ((trace.program j).jmp_offset1).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `bne`: exactly the inputs
    `Decode_bne_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_bne {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bne trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_EQ
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ ((trace.program j).jmp_offset2).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `blt`: exactly the inputs
    `Decode_blt_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_blt {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_blt trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ ((trace.program j).jmp_offset1).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `bge`: exactly the inputs
    `Decode_bge_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_bge {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bge trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LT
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ ((trace.program j).jmp_offset2).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `bltu`: exactly the inputs
    `Decode_bltu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_bltu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bltu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ ((trace.program j).jmp_offset1).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `bgeu`: exactly the inputs
    `Decode_bgeu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_bgeu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_bgeu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_LTU
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ ((trace.program j).jmp_offset2).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lui`: exactly the inputs
    `Decode_lui_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lui {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lui trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (c.imm ++ (0 : BitVec 12)).toNat
  h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat / 4294967296
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `auipc`: exactly the inputs
    `Decode_auipc_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_auipc {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_auipc trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = true
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ ((trace.program j).jmp_offset2).val =
          (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `jal`: exactly the inputs
    `Decode_jal_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_jal {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_jal trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = true
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ ((trace.program j).jmp_offset1).val = (BitVec.signExtend 64 c.imm).toNat
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `jalr`: exactly the inputs
    `Decode_jalr_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_jalr {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_flag :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).flag
      i.val = 0
  h_a_mask_lo :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0
      i.val = 4294967294
  h_a_mask_hi :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1
      i.val = 4294967295
  h_c1_zero :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_1
      i.val = 0
  h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
        i.val).val = c.offset_bv.toNat
  h_offset_even :
    c.offset_bv &&& 1#64 = 0#64
  h_no_fgl_wrap :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0 i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
          i.val).val < GL_prime
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_m32 : bits.m32 = false
  h_bits_set_pc : bits.set_pc = true
  h_bits_store_pc : bits.store_pc = true
  h_bits_store_ind : bits.store_ind = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_AND
        ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sb`: exactly the inputs
    `Decode_sb_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sb {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sb trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 1
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sb_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sh`: exactly the inputs
    `Decode_sh_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sh {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sh trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 2
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sh_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sw`: exactly the inputs
    `Decode_sw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = 4
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sw_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `sd`: exactly the inputs
    `Decode_sd_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_sd {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_sd trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).store_offset =
            ((BitVec.signExtend 64 c.sd_input.imm).toInt : FGL)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `ld`: exactly the inputs
    `Decode_ld_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_ld {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_ld trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (8 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.ld_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.ld_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lbu`: exactly the inputs
    `Decode_lbu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lbu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lbu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lbu_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lbu_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lhu`: exactly the inputs
    `Decode_lhu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lhu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lhu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lhu_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lhu_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lwu`: exactly the inputs
    `Decode_lwu_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lwu {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lwu trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_COPYB
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lwu_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lwu_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lb`: exactly the inputs
    `Decode_lb_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lb {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lb trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  v :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary :
    ℕ
  offset :
    ℕ
  env :
    Environment FGL
  h_static :
    ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_B
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (1 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lb_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lb_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lh`: exactly the inputs
    `Decode_lh_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lh {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lh trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  v :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary :
    ℕ
  offset :
    ℕ
  env :
    Environment FGL
  h_static :
    ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_H
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (2 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lh_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lh_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `lw`: exactly the inputs
    `Decode_lw_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_lw {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_lw trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  v :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary :
    ℕ
  offset :
    ℕ
  env :
    Environment FGL
  h_static :
    ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = true
  h_bits_set_pc : bits.set_pc = false
  h_bits_store_pc : bits.store_pc = false
  h_bits_store_ind : bits.store_ind = false
  h_bits_store_reg : bits.store_reg = true
  h_bits_b_src_ind : bits.b_src_ind = true
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_SIGNEXTEND_W
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).ind_width = (4 : FGL)
        ∧ (trace.program j).b_offset_imm0 =
            ((BitVec.signExtend 64 c.lw_input.imm).toNat : FGL)
        ∧ (trace.program j).store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lw_input.rd)
        ∧ (trace.program j).flags = packFlags bits

/-- Per-row committed-program decode bundle for `fence`: exactly the inputs
    `Decode_fence_of_program` consumes besides `trace`/`i`/`c`. -/
structure ProgramDecode_fence {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_fence trace i) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_fm_zero :
    c.fm = 0#4
  h_rs_x0 :
    ZiskFv.Compliance.Defects.IsX0Reg c.rs
  h_rd_x0 :
    ZiskFv.Compliance.Defects.IsX0Reg c.rd
  bits : RomFlagBits
  h_bits_ieo : bits.is_external_op = false
  h_bits_set_pc : bits.set_pc = false
  h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_FLAG
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits

end ZiskFv.Compliance.RomDecodeBinding

namespace ZiskFv.Compliance

/-- Per-row committed-program decode bundle, dispatched on the row's `ZiskStep`
    (mirror of `RowDecode` in `Dispatcher.lean`).  Each arm is the per-op
    `ProgramDecode_<op>` record bundling the program-level decode facts, the op's
    non-ROM operand witnesses, and `h_idx`. -/
def ProgramDecode (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Type
  | .sub c => RomDecodeBinding.ProgramDecode_sub ziskTrace i c
  | .and c => RomDecodeBinding.ProgramDecode_and ziskTrace i c
  | .or c => RomDecodeBinding.ProgramDecode_or ziskTrace i c
  | .xor c => RomDecodeBinding.ProgramDecode_xor ziskTrace i c
  | .slt c => RomDecodeBinding.ProgramDecode_slt ziskTrace i c
  | .sltu c => RomDecodeBinding.ProgramDecode_sltu ziskTrace i c
  | .andi c => RomDecodeBinding.ProgramDecode_andi ziskTrace i c
  | .ori c => RomDecodeBinding.ProgramDecode_ori ziskTrace i c
  | .xori c => RomDecodeBinding.ProgramDecode_xori ziskTrace i c
  | .slti c => RomDecodeBinding.ProgramDecode_slti ziskTrace i c
  | .sltiu c => RomDecodeBinding.ProgramDecode_sltiu ziskTrace i c
  | .sll c => RomDecodeBinding.ProgramDecode_sll ziskTrace i c
  | .srl c => RomDecodeBinding.ProgramDecode_srl ziskTrace i c
  | .sra c => RomDecodeBinding.ProgramDecode_sra ziskTrace i c
  | .slli c => RomDecodeBinding.ProgramDecode_slli ziskTrace i c
  | .srli c => RomDecodeBinding.ProgramDecode_srli ziskTrace i c
  | .srai c => RomDecodeBinding.ProgramDecode_srai ziskTrace i c
  | .add c => RomDecodeBinding.ProgramDecode_add ziskTrace i c
  | .addi c => RomDecodeBinding.ProgramDecode_addi ziskTrace i c
  | .subw c => RomDecodeBinding.ProgramDecode_subw ziskTrace i c
  | .addw c => RomDecodeBinding.ProgramDecode_addw ziskTrace i c
  | .addiw c => RomDecodeBinding.ProgramDecode_addiw ziskTrace i c
  | .sllw c => RomDecodeBinding.ProgramDecode_sllw ziskTrace i c
  | .srlw c => RomDecodeBinding.ProgramDecode_srlw ziskTrace i c
  | .sraw c => RomDecodeBinding.ProgramDecode_sraw ziskTrace i c
  | .slliw c => RomDecodeBinding.ProgramDecode_slliw ziskTrace i c
  | .srliw c => RomDecodeBinding.ProgramDecode_srliw ziskTrace i c
  | .sraiw c => RomDecodeBinding.ProgramDecode_sraiw ziskTrace i c
  | .mul c => RomDecodeBinding.ProgramDecode_mul ziskTrace i c
  | .mulh c => RomDecodeBinding.ProgramDecode_mulh ziskTrace i c
  | .mulhsu c => RomDecodeBinding.ProgramDecode_mulhsu ziskTrace i c
  | .mulw c => RomDecodeBinding.ProgramDecode_mulw ziskTrace i c
  | .mulhu c => RomDecodeBinding.ProgramDecode_mulhu ziskTrace i c
  | .div c => RomDecodeBinding.ProgramDecode_div ziskTrace i c
  | .rem c => RomDecodeBinding.ProgramDecode_rem ziskTrace i c
  | .divw c => RomDecodeBinding.ProgramDecode_divw ziskTrace i c
  | .remw c => RomDecodeBinding.ProgramDecode_remw ziskTrace i c
  | .divu c => RomDecodeBinding.ProgramDecode_divu ziskTrace i c
  | .divuw c => RomDecodeBinding.ProgramDecode_divuw ziskTrace i c
  | .remu c => RomDecodeBinding.ProgramDecode_remu ziskTrace i c
  | .remuw c => RomDecodeBinding.ProgramDecode_remuw ziskTrace i c
  | .beq c => RomDecodeBinding.ProgramDecode_beq ziskTrace i c
  | .bne c => RomDecodeBinding.ProgramDecode_bne ziskTrace i c
  | .blt c => RomDecodeBinding.ProgramDecode_blt ziskTrace i c
  | .bge c => RomDecodeBinding.ProgramDecode_bge ziskTrace i c
  | .bltu c => RomDecodeBinding.ProgramDecode_bltu ziskTrace i c
  | .bgeu c => RomDecodeBinding.ProgramDecode_bgeu ziskTrace i c
  | .lui c => RomDecodeBinding.ProgramDecode_lui ziskTrace i c
  | .auipc c => RomDecodeBinding.ProgramDecode_auipc ziskTrace i c
  | .jal c => RomDecodeBinding.ProgramDecode_jal ziskTrace i c
  | .jalr c => RomDecodeBinding.ProgramDecode_jalr ziskTrace i c
  | .sb c => RomDecodeBinding.ProgramDecode_sb ziskTrace i c
  | .sh c => RomDecodeBinding.ProgramDecode_sh ziskTrace i c
  | .sw c => RomDecodeBinding.ProgramDecode_sw ziskTrace i c
  | .sd c => RomDecodeBinding.ProgramDecode_sd ziskTrace i c
  | .ld c => RomDecodeBinding.ProgramDecode_ld ziskTrace i c
  | .lbu c => RomDecodeBinding.ProgramDecode_lbu ziskTrace i c
  | .lhu c => RomDecodeBinding.ProgramDecode_lhu ziskTrace i c
  | .lwu c => RomDecodeBinding.ProgramDecode_lwu ziskTrace i c
  | .lb c => RomDecodeBinding.ProgramDecode_lb ziskTrace i c
  | .lh c => RomDecodeBinding.ProgramDecode_lh ziskTrace i c
  | .lw c => RomDecodeBinding.ProgramDecode_lw ziskTrace i c
  | .fence c => RomDecodeBinding.ProgramDecode_fence ziskTrace i c

/-- Rebuild block 1's `RowDecode` for one row from its committed-program
    `ProgramDecode` bundle, by applying the matching per-op
    `Decode_<op>_of_program`. -/
noncomputable def rowDecode_of_programDecode (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {zs : ZiskStep ziskTrace i}
    (pd : ProgramDecode ziskTrace i zs) : RowDecode ziskTrace i zs := by
  cases zs with
  | sub c => exact RomDecodeBinding.Decode_sub_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | and c => exact RomDecodeBinding.Decode_and_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | or c => exact RomDecodeBinding.Decode_or_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | xor c => exact RomDecodeBinding.Decode_xor_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | slt c => exact RomDecodeBinding.Decode_slt_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sltu c => exact RomDecodeBinding.Decode_sltu_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | andi c => exact RomDecodeBinding.Decode_andi_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | ori c => exact RomDecodeBinding.Decode_ori_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | xori c => exact RomDecodeBinding.Decode_xori_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | slti c => exact RomDecodeBinding.Decode_slti_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | sltiu c => exact RomDecodeBinding.Decode_sltiu_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | sll c => exact RomDecodeBinding.Decode_sll_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | srl c => exact RomDecodeBinding.Decode_srl_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sra c => exact RomDecodeBinding.Decode_sra_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | slli c => exact RomDecodeBinding.Decode_slli_of_program ziskTrace i c pd.h_idx pd.h_b_lo_t pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | srli c => exact RomDecodeBinding.Decode_srli_of_program ziskTrace i c pd.h_idx pd.h_b_lo_t pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | srai c => exact RomDecodeBinding.Decode_srai_of_program ziskTrace i c pd.h_idx pd.h_b_lo_t pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | add c => exact RomDecodeBinding.Decode_add_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | addi c => exact RomDecodeBinding.Decode_addi_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | subw c => exact RomDecodeBinding.Decode_subw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | addw c => exact RomDecodeBinding.Decode_addw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | addiw c => exact RomDecodeBinding.Decode_addiw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_b_src_imm pd.h_prog
  | sllw c => exact RomDecodeBinding.Decode_sllw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | srlw c => exact RomDecodeBinding.Decode_srlw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sraw c => exact RomDecodeBinding.Decode_sraw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | slliw c => exact RomDecodeBinding.Decode_slliw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | srliw c => exact RomDecodeBinding.Decode_srliw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sraiw c => exact RomDecodeBinding.Decode_sraiw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | mul c => exact RomDecodeBinding.Decode_mul_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | mulh c => exact RomDecodeBinding.Decode_mulh_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | mulhsu c => exact RomDecodeBinding.Decode_mulhsu_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | mulw c => exact RomDecodeBinding.Decode_mulw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | mulhu c => exact RomDecodeBinding.Decode_mulhu_of_program ziskTrace i c pd.h_idx pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | div c => exact RomDecodeBinding.Decode_div_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | rem c => exact RomDecodeBinding.Decode_rem_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | divw c => exact RomDecodeBinding.Decode_divw_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | remw c => exact RomDecodeBinding.Decode_remw_of_program ziskTrace i c pd.h_idx pd.arith_mem pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | divu c => exact RomDecodeBinding.Decode_divu_of_program ziskTrace i c pd.h_idx pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | divuw c => exact RomDecodeBinding.Decode_divuw_of_program ziskTrace i c pd.h_idx pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | remu c => exact RomDecodeBinding.Decode_remu_of_program ziskTrace i c pd.h_idx pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | remuw c => exact RomDecodeBinding.Decode_remuw_of_program ziskTrace i c pd.h_idx pd.bounds pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | beq c => exact RomDecodeBinding.Decode_beq_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_prog
  | bne c => exact RomDecodeBinding.Decode_bne_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_prog
  | blt c => exact RomDecodeBinding.Decode_blt_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_prog
  | bge c => exact RomDecodeBinding.Decode_bge_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_prog
  | bltu c => exact RomDecodeBinding.Decode_bltu_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_prog
  | bgeu c => exact RomDecodeBinding.Decode_bgeu_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_prog
  | lui c => exact RomDecodeBinding.Decode_lui_of_program ziskTrace i c pd.h_idx pd.h_imm_lo_nat pd.h_imm_hi_nat pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | auipc c => exact RomDecodeBinding.Decode_auipc_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | jal c => exact RomDecodeBinding.Decode_jal_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | jalr c => exact RomDecodeBinding.Decode_jalr_of_program ziskTrace i c pd.h_idx pd.h_flag pd.h_a_mask_lo pd.h_a_mask_hi pd.h_c1_zero pd.h_offset_bridge pd.h_offset_even pd.h_no_fgl_wrap pd.bits pd.h_bits_ieo pd.h_bits_m32 pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sb c => exact RomDecodeBinding.Decode_sb_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sh c => exact RomDecodeBinding.Decode_sh_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sw c => exact RomDecodeBinding.Decode_sw_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | sd c => exact RomDecodeBinding.Decode_sd_of_program ziskTrace i c pd.h_idx pd.bits pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind pd.h_prog
  | ld c =>
      exact RomDecodeBinding.Decode_ld_of_program ziskTrace i c pd.h_idx pd.bits
        pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind
        pd.h_bits_store_reg pd.h_bits_b_src_ind pd.h_prog
  | lbu c =>
      exact RomDecodeBinding.Decode_lbu_of_program ziskTrace i c pd.h_idx pd.bits
        pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind
        pd.h_bits_store_reg pd.h_bits_b_src_ind pd.h_prog
  | lhu c =>
      exact RomDecodeBinding.Decode_lhu_of_program ziskTrace i c pd.h_idx pd.bits
        pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind
        pd.h_bits_store_reg pd.h_bits_b_src_ind pd.h_prog
  | lwu c =>
      exact RomDecodeBinding.Decode_lwu_of_program ziskTrace i c pd.h_idx pd.bits
        pd.h_bits_ieo pd.h_bits_set_pc pd.h_bits_store_pc pd.h_bits_store_ind
        pd.h_bits_store_reg pd.h_bits_b_src_ind pd.h_prog
  | lb c =>
      exact RomDecodeBinding.Decode_lb_of_program ziskTrace i c pd.h_idx pd.v pd.r_binary
        pd.offset pd.env pd.h_static pd.h_match pd.bits pd.h_bits_ieo pd.h_bits_set_pc
        pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_store_reg pd.h_bits_b_src_ind
        pd.h_prog
  | lh c =>
      exact RomDecodeBinding.Decode_lh_of_program ziskTrace i c pd.h_idx pd.v pd.r_binary
        pd.offset pd.env pd.h_static pd.h_match pd.bits pd.h_bits_ieo pd.h_bits_set_pc
        pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_store_reg pd.h_bits_b_src_ind
        pd.h_prog
  | lw c =>
      exact RomDecodeBinding.Decode_lw_of_program ziskTrace i c pd.h_idx pd.v pd.r_binary
        pd.offset pd.env pd.h_static pd.h_match pd.bits pd.h_bits_ieo pd.h_bits_set_pc
        pd.h_bits_store_pc pd.h_bits_store_ind pd.h_bits_store_reg pd.h_bits_b_src_ind
        pd.h_prog
  | fence c => exact RomDecodeBinding.Decode_fence_of_program ziskTrace i c pd.h_idx pd.h_fm_zero pd.h_rs_x0 pd.h_rd_x0 pd.bits pd.h_bits_ieo pd.h_bits_set_pc pd.h_prog

/-- Lift `rowDecode_of_programDecode` over every instruction: given a per-row
    `ProgramDecode`, produce the full `rowDecodes` family `root_soundness`
    consumes. -/
noncomputable def rowDecodes_of_programDecodes (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (programDecodes : ∀ i : Fin numInstructions, ProgramDecode ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions, RowDecode ziskTrace i (ziskStep i) :=
  fun i => rowDecode_of_programDecode ziskTrace i (programDecodes i)

end ZiskFv.Compliance
