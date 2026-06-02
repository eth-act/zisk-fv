import ZiskFv.Transpiler.Static
import ZiskFv.SailSpec.Auxiliaries

/-!
# Raw FENCE coverage for the static transpiler model

This file is intentionally small and explicit. `Transpiler.Static` starts
after instruction classification; here we add the raw 32-bit FENCE
classification slice needed to state the current coverage claim.

The modeled ZisK route covers `.fence` once the checked-out ZisK
interpreter classifies a raw instruction as `"fence"`.

This file deliberately does **not** define a new decoder. The acceptance
predicate below mirrors the checked-out implementation gate at
`zisk/riscv/src/riscv_interpreter.rs`, where generic FENCE is classified as
`"reserved"` when `(inst & 0xF00F8F80) != 0`.
-/

namespace ZiskFv.Transpiler.FenceCoverage

open ZiskFv.Transpiler.Static

/-- The exact raw word that Sail decodes through its separate `FENCE_TSO`
    constructor before the generic `FENCE` branch. -/
def fenceTsoWord : BitVec 32 := 0x8330000F#32

def fenceOpcode (inst : BitVec 32) : BitVec 7 :=
  Sail.BitVec.extractLsb inst 6 0

def fenceFunct3 (inst : BitVec 32) : BitVec 3 :=
  Sail.BitVec.extractLsb inst 14 12

def fenceRd (inst : BitVec 32) : BitVec 5 :=
  Sail.BitVec.extractLsb inst 11 7

def fenceRs1 (inst : BitVec 32) : BitVec 5 :=
  Sail.BitVec.extractLsb inst 19 15

def fenceFm (inst : BitVec 32) : BitVec 4 :=
  Sail.BitVec.extractLsb inst 31 28

def fencePred (inst : BitVec 32) : BitVec 4 :=
  Sail.BitVec.extractLsb inst 27 24

def fenceSucc (inst : BitVec 32) : BitVec 4 :=
  Sail.BitVec.extractLsb inst 23 20

/-- Sail's generic FENCE decoder branch, as a raw bit predicate.

The generated decoder also checks that `rs1` and `rd` decode as registers;
for 5-bit register indices this is total, so the static coverage predicate
records the discriminating bits: opcode, funct3, and not the prior
`FENCE_TSO` exact-match branch. -/
def SailGenericFenceEncoding (inst : BitVec 32) : Prop :=
  inst ≠ fenceTsoWord ∧
  fenceOpcode inst = (0b0001111#7) ∧
  fenceFunct3 inst = (0b000#3)

/-- Every raw word Sail decodes as a FENCE-family instruction in this
    profile: either the exact `FENCE_TSO` word or the generic `FENCE`
    branch. -/
def SailFenceEncoding (inst : BitVec 32) : Prop :=
  inst = fenceTsoWord ∨ SailGenericFenceEncoding inst

/-- Mask used by the checked-out ZisK interpreter to reject generic FENCE
    encodings as `"reserved"`.

Source: `zisk/riscv/src/riscv_interpreter.rs`, FENCE branch:
`if (inst & 0xF00F8F80) != 0 { i.inst = "reserved" }`.
It covers nonzero `fm`, `rs1`, and `rd`. -/
def ziskCurrentFenceReservedMask : BitVec 32 := 0xF00F8F80#32

/-- Current checked-out ZisK generic-FENCE acceptance predicate.

This is not a replacement decoder. It is the small source-linked acceptance
gate copied from `zisk/riscv/src/riscv_interpreter.rs`; after this predicate
holds, `zisk/core/src/riscv2zisk_context.rs` maps mnemonic `"fence"` to
`self.nop(riscv_instruction, 4)`. -/
def CurrentZiskAcceptsGenericFence (inst : BitVec 32) : Prop :=
  fenceOpcode inst = (0b0001111#7) ∧
  fenceFunct3 inst = (0b000#3) ∧
  inst &&& ziskCurrentFenceReservedMask = (0#32)

/-- The static `Rv64Inst` produced once a supported raw FENCE word is
    classified. FENCE ignores `rd`/`rs1` semantically in the current route,
    but we retain them so the raw fields are not erased. `fm`, `pred`, and
    `succ` are architectural ordering fields; in this zkVM concurrency model
    they do not affect the emitted row. -/
def rawFenceInst (inst : BitVec 32) : Rv64Inst :=
  { op := .fence
    rd := (fenceRd inst).toNat
    rs1 := (fenceRs1 inst).toNat
    instSize := 4 }

/-- The concrete ZisK static route for a raw FENCE word: one internal
    OP_FLAG row, no sources, no store, and PC advances by 4. -/
def ZiskRoutesAsFence (inst : BitVec 32) : Prop :=
  transpile (rawFenceInst inst) =
    [row 0 Const.opFlag (sourceImm 0) (sourceImm 0)
      (Const.storeNone, 0, false) false 0 4 4 false]

/-- Once accepted by the raw FENCE decoder, the static transpiler emits the
    expected no-op/PC+4 ZisK row. -/
theorem zisk_routes_raw_fence :
    ZiskRoutesAsFence inst := by
  rfl

/-- Current checked-out ZisK coverage statement for generic FENCE: when the
    implementation interpreter accepts a raw generic FENCE instruction, the
    linked static transpiler model routes it to the FENCE no-op row. -/
theorem zisk_routes_currently_accepted_generic_fence
    {inst : BitVec 32}
    (_h_zisk : CurrentZiskAcceptsGenericFence inst) :
    ZiskRoutesAsFence inst := by
  exact zisk_routes_raw_fence

/-- A concrete Sail-valid generic FENCE word rejected by the checked-out ZisK
    interpreter gate because `fm = 1`.

This is the experiment's guardrail: without the upstream decoder fix, full
generic FENCE ISA coverage is false for the linked implementation. -/
theorem sail_generic_fence_with_nonzero_fm :
    SailGenericFenceEncoding (0x1000000F#32) := by
  simp [SailGenericFenceEncoding, fenceTsoWord, fenceOpcode, fenceFunct3]

theorem current_zisk_rejects_fence_with_nonzero_fm :
    ¬ CurrentZiskAcceptsGenericFence (0x1000000F#32) := by
  intro h
  simp [CurrentZiskAcceptsGenericFence, ziskCurrentFenceReservedMask] at h

end ZiskFv.Transpiler.FenceCoverage
