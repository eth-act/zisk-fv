import ZiskFv.Transpiler.Static
import ZiskFv.SailSpec.Auxiliaries

/-!
# Raw FENCE coverage for the static transpiler model

This file is intentionally small and explicit. `Transpiler.Static` starts
after instruction classification; here we add the raw 32-bit FENCE
classification slice needed to state the current coverage claim.

The current modeled ZisK route covers Sail's generic FENCE encodings only
outside the ledgered FENCE bug region:

* `FENCE_TSO` (`0x8330000F`) is separate in the generated Sail decoder.
* Generic `FENCE` encodings with `fm ≠ 0` are excluded until the accepted
  encoding set is pinned down.
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

/-- Sail's generic FENCE decoder branch, as a raw bit predicate.

The generated decoder also checks that `rs1` and `rd` decode as registers;
for 5-bit register indices this is total, so the static coverage predicate
records the discriminating bits: opcode, funct3, and not the prior
`FENCE_TSO` exact-match branch. -/
def SailGenericFenceEncoding (inst : BitVec 32) : Prop :=
  inst ≠ fenceTsoWord ∧
  fenceOpcode inst = (0b0001111#7) ∧
  fenceFunct3 inst = (0b000#3)

/-- Current coverage bug region for raw FENCE words. -/
def UnsupportedFenceEncoding (inst : BitVec 32) : Prop :=
  inst = fenceTsoWord ∨ fenceFm inst ≠ (0#4)

/-- The static `Rv64Inst` produced once a supported raw FENCE word is
    classified. FENCE ignores `rd`/`rs1` semantically in the current route,
    but we retain them so the raw fields are not erased. -/
def rawFenceInst (inst : BitVec 32) : Rv64Inst :=
  { op := .fence
    rd := (fenceRd inst).toNat
    rs1 := (fenceRs1 inst).toNat
    instSize := 4 }

/-- Current raw FENCE decoder model: reject the known bug region, otherwise
    accept Sail's generic FENCE bit shape. -/
noncomputable def decodeSupportedFence (inst : BitVec 32) : Option Rv64Inst := by
  classical
  exact
    if UnsupportedFenceEncoding inst then
      none
    else if SailGenericFenceEncoding inst then
      some (rawFenceInst inst)
    else
      none

/-- The concrete ZisK static route for a raw FENCE word: one internal
    OP_FLAG row, no sources, no store, and PC advances by 4. -/
def ZiskRoutesAsFence (inst : BitVec 32) : Prop :=
  transpile (rawFenceInst inst) =
    [row 0 Const.opFlag (sourceImm 0) (sourceImm 0)
      (Const.storeNone, 0, false) false 0 4 4 false]

theorem decode_supported_fence_rejects_unsupported
    {inst : BitVec 32}
    (h_unsupported : UnsupportedFenceEncoding inst) :
    decodeSupportedFence inst = none := by
  simp [decodeSupportedFence, h_unsupported]

/-- Completeness under the current FENCE bug assumption: every raw word in
    Sail's generic FENCE branch, outside the unsupported region, is accepted
    by the modeled ZisK FENCE decoder. -/
theorem decode_supported_fence_complete_under_bug_assumption
    {inst : BitVec 32}
    (h_sail : SailGenericFenceEncoding inst)
    (h_not_unsupported : ¬ UnsupportedFenceEncoding inst) :
    decodeSupportedFence inst = some (rawFenceInst inst) := by
  simp [decodeSupportedFence, h_sail, h_not_unsupported]

/-- Once accepted by the raw FENCE decoder, the static transpiler emits the
    expected no-op/PC+4 ZisK row. -/
theorem zisk_routes_raw_fence :
    ZiskRoutesAsFence inst := by
  rfl

/-- End-to-end static coverage statement for FENCE under the current bug
    assumption. This is the theorem that would fail without excluding
    `UnsupportedFenceEncoding`: the decoder rejects those cases by
    `decode_supported_fence_rejects_unsupported`. -/
theorem zisk_covers_sail_generic_fence_under_bug_assumption
    {inst : BitVec 32}
    (h_sail : SailGenericFenceEncoding inst)
    (h_not_unsupported : ¬ UnsupportedFenceEncoding inst) :
    decodeSupportedFence inst = some (rawFenceInst inst) ∧
      ZiskRoutesAsFence inst := by
  exact ⟨decode_supported_fence_complete_under_bug_assumption
      h_sail h_not_unsupported, zisk_routes_raw_fence⟩

end ZiskFv.Transpiler.FenceCoverage
