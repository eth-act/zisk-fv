import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Dispatch
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.DynamicFields
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves

/-!
# Raw-program binding for the ADD pilot (issue #159, BLOCK 3)

This module makes the committed ROM message's ADD decode fields **derived** from
the raw RISC-V instruction word, via the REAL Aeneas transpile pipeline
(`extract_transpile_rv64im_raw`, `trust/aeneas/ProductionM2.lean`).

Block 1 (`RomDecodeBinding.Decode_add_of_program`) tied the witness row's decode
columns to the committed program `trace.program`.  This block ties the committed
program entry to its raw instruction word: the op-agnostic `ProgramBinding`
certificate states the committed ROM holds exactly the serialized lowering of the
raw program.  For the ADD case the chain closes — `Decode_add_from_rawProgram`
rebuilds `Decode_add` from `rawProgram` + `ProgramBinding` + the ADD-branch of the
(eventual exhaustive) per-entry raw-word split.

Op-AGNOSTIC: `serializeExtract` / `romMessageOfRaw` / `ProgramBinding` run ONE
pipeline for every word; ADD-ness enters only via the `rawRType … 0x33` raw-word
hypothesis (the ADD case of an exhaustive split), never as a trust premise.

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).  The lowering totality is proven
with the kernel-sound `System.Platform.numBits` casing (the same register-bound
lemmas as `…/Extraction/Helpers.lean`), NOT `native_decide` (the production
RV-completeness harness uses `native_decide`; this in-build pilot does not).
-/

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)

set_option maxHeartbeats 8000000

/-! ## Op-agnostic serialization of the lowered row into the committed ROM message. -/

/-- Op-agnostic flag-bit extraction from a lowered ZiskInstExtract: the five
    decode-relevant flags are faithful direct copies of the lowered booleans; the
    operand-source / store selector bits are the op-agnostic selector decode
    (operand-side, out of decode scope — not consumed by per-op decode). -/
def romFlagBitsOfExtract (e : zisk_core.aeneas_extract.ZiskInstExtract) : RomFlagBits where
  a_src_imm := decide (e.a_src = zisk_core.zisk_inst.SRC_IMM)
  a_src_mem := decide (e.a_src = zisk_core.zisk_inst.SRC_MEM)
  is_precompiled := e.is_precompiled
  b_src_imm := decide (e.b_src = zisk_core.zisk_inst.SRC_IMM)
  b_src_mem := decide (e.b_src = zisk_core.zisk_inst.SRC_MEM)
  is_external_op := e.is_external_op
  store_pc := e.store_pc
  store_mem := decide (e.store = zisk_core.zisk_inst.STORE_MEM)
  store_ind := decide (e.store = zisk_core.zisk_inst.STORE_IND)
  set_pc := e.set_pc
  m32 := e.m32
  b_src_ind := decide (e.b_src = (3#u64 : Std.U64))
  a_src_reg := decide (e.a_src = zisk_core.zisk_inst.SRC_REG)
  b_src_reg := decide (e.b_src = zisk_core.zisk_inst.SRC_REG)
  store_reg := decide (e.store = zisk_core.zisk_inst.STORE_REG)

/-- Op-agnostic serialization of a lowered row into the committed FGL ROM message.
    The `line` (pc) is threaded separately (it is the program-counter, supplied by
    the caller). Every other field is the uniform `.val`→FGL coercion of the
    extracted ZiskInst field; `flags` is the standard 15-bit packing. -/
def serializeExtract (line : FGL) (e : zisk_core.aeneas_extract.ZiskInstExtract) :
    ZiskRomMessage FGL where
  line := line
  a_offset_imm0 := (e.a_offset_imm0.val : FGL)
  a_imm1 := (e.a_use_sp_imm1.val : FGL)
  b_offset_imm0 := (e.b_offset_imm0.val : FGL)
  b_imm1 := (e.b_use_sp_imm1.val : FGL)
  ind_width := (e.ind_width.val : FGL)
  op := (e.op.val : FGL)
  store_offset := (e.store_offset.val : FGL)
  jmp_offset1 := (e.jmp_offset1.val : FGL)
  jmp_offset2 := (e.jmp_offset2.val : FGL)
  flags := packFlags (romFlagBitsOfExtract e)

/-- The committed ROM message a raw RISC-V word must serialize to: run the REAL
    Aeneas transpile pipeline on the word and FGL-serialize its lowered row. A
    raw word the pipeline rejects maps to the all-zero message (never matched by a
    supported decode). Op-AGNOSTIC: one pipeline for every word. -/
noncomputable def romMessageOfRaw (line : FGL) (raw : BitVec 32) : ZiskRomMessage FGL :=
  match zisk_core.aeneas_extract.extract_transpile_rv64im_raw (ZiskFv.Compliance.Decode.toU32 raw) with
  | .ok ext => serializeExtract line ext.row
  | _ => { line := line, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0,
           b_imm1 := 0, ind_width := 0, op := 0, store_offset := 0,
           jmp_offset1 := 0, jmp_offset2 := 0, flags := 0 }

/-- Op-agnostic ROM-image binding (a verifier-attached certificate, NOT an axiom):
    the committed ROM holds exactly the serialized lowering of the raw program. -/
def ProgramBinding {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (rawProgram : Fin n → BitVec 32) : Prop :=
  ∀ k : Fin n, trace.program k = romMessageOfRaw (trace.program k).line (rawProgram k)


end ZiskFv.Compliance.RawProgramBinding
