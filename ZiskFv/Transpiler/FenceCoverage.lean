import ZiskFv.Transpiler.Static
import ZiskFv.SailSpec.Auxiliaries

/-!
# Raw FENCE coverage for the static transpiler model

This file is intentionally small and explicit. `Transpiler.Static` starts
after instruction classification; here we add the raw 32-bit FENCE
classification slice needed to state the current coverage claim.

The modeled ZisK route covers both Sail FENCE decode branches:

* `FENCE_TSO` (`0x8330000F`), which Sail decodes before generic FENCE.
* Generic `FENCE` encodings with opcode `0001111` and funct3 `000`,
  for every `fm`, `pred`, and `succ`.
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

/-- Raw FENCE decoder model for the static transpiler slice. -/
noncomputable def decodeFence (inst : BitVec 32) : Option Rv64Inst := by
  classical
  exact
    if SailFenceEncoding inst then
      some (rawFenceInst inst)
    else
      none

/-- The concrete ZisK static route for a raw FENCE word: one internal
    OP_FLAG row, no sources, no store, and PC advances by 4. -/
def ZiskRoutesAsFence (inst : BitVec 32) : Prop :=
  transpile (rawFenceInst inst) =
    [row 0 Const.opFlag (sourceImm 0) (sourceImm 0)
      (Const.storeNone, 0, false) false 0 4 4 false]

theorem decode_fence_rejects_non_fence
    {inst : BitVec 32}
    (h_not_fence : ¬ SailFenceEncoding inst) :
    decodeFence inst = none := by
  simp [decodeFence, h_not_fence]

/-- Generic FENCE coverage: every raw word in Sail's generic FENCE branch is
    accepted by the modeled ZisK FENCE decoder, for every `fm`. -/
theorem decode_fence_complete_generic
    {inst : BitVec 32}
    (h_sail : SailGenericFenceEncoding inst) :
    decodeFence inst = some (rawFenceInst inst) := by
  simp [decodeFence, SailFenceEncoding, h_sail]

/-- `FENCE_TSO` coverage: Sail's exact TSO word is accepted by the same
    modeled ZisK FENCE route. -/
theorem decode_fence_complete_tso
    {inst : BitVec 32}
    (h_tso : inst = fenceTsoWord) :
    decodeFence inst = some (rawFenceInst inst) := by
  simp [decodeFence, SailFenceEncoding, h_tso]

/-- Raw FENCE-family coverage: every raw word Sail decodes as generic
    `FENCE` or exact `FENCE_TSO` is accepted by the modeled ZisK FENCE
    decoder. -/
theorem decode_fence_complete
    {inst : BitVec 32}
    (h_sail : SailFenceEncoding inst) :
    decodeFence inst = some (rawFenceInst inst) := by
  simp [decodeFence, h_sail]

/-- Once accepted by the raw FENCE decoder, the static transpiler emits the
    expected no-op/PC+4 ZisK row. -/
theorem zisk_routes_raw_fence :
    ZiskRoutesAsFence inst := by
  rfl

/-- End-to-end static coverage statement for Sail's generic FENCE branch. -/
theorem zisk_covers_sail_generic_fence
    {inst : BitVec 32}
    (h_sail : SailGenericFenceEncoding inst) :
    decodeFence inst = some (rawFenceInst inst) ∧
      ZiskRoutesAsFence inst := by
  exact ⟨decode_fence_complete_generic h_sail, zisk_routes_raw_fence⟩

/-- End-to-end static coverage statement for Sail's exact `FENCE_TSO`
    branch. -/
theorem zisk_covers_sail_fence_tso
    {inst : BitVec 32}
    (h_tso : inst = fenceTsoWord) :
    decodeFence inst = some (rawFenceInst inst) ∧
      ZiskRoutesAsFence inst := by
  exact ⟨decode_fence_complete_tso h_tso, zisk_routes_raw_fence⟩

/-- End-to-end static coverage statement for all Sail FENCE-family raw
    encodings in this profile. -/
theorem zisk_covers_sail_fence
    {inst : BitVec 32}
    (h_sail : SailFenceEncoding inst) :
    decodeFence inst = some (rawFenceInst inst) ∧
      ZiskRoutesAsFence inst := by
  exact ⟨decode_fence_complete h_sail, zisk_routes_raw_fence⟩

end ZiskFv.Transpiler.FenceCoverage
