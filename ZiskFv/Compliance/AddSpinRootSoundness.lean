import ZiskFv.Compliance.AddSpinWitness
import ZiskFv.Soundness

/-!
# Concrete `root_soundness` instantiation for the ADD + spin-loop trace (#220)

This file applies the public `root_soundness` theorem to the concrete
`addSpinAcceptedTrace` witness from `AddSpinWitness.lean`.
-/

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.AddSpinRootSoundness

def x0 : regidx := regidx.Regidx (0#5)

def x1 : regidx := regidx.Regidx (1#5)

def addSpinAddIndex : Fin 2 := ⟨0, by decide⟩

def addSpinJalIndex : Fin 2 := ⟨1, by decide⟩

def addSpinAddClaim : Claim_add addSpinAcceptedTrace addSpinAddIndex where
  r1 := x1
  r2 := x1
  rd := x1

def addSpinJalClaim : Claim_jal addSpinAcceptedTrace addSpinJalIndex where
  imm := 0#21
  rd := x0

def addSpinZiskStep : ∀ i : Fin 2, ZiskStep addSpinAcceptedTrace i
  | ⟨0, _⟩ => .add addSpinAddClaim
  | ⟨1, _⟩ => .jal addSpinJalClaim

def addSpinMisa : RegisterType Register.misa := 0#64

def addSpinRegs (pc : BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.misa addSpinMisa
  regs2.insert (reg_of_fin (regidx_to_fin x1)) (0#64)

def addSpinState (pc : BitVec 64) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := addSpinRegs pc
    mem := {} }

def addSpinSailTrace : SailTrace 2
  | ⟨0, _⟩ => addSpinState (0#64)
  | ⟨1, _⟩ => addSpinState (4#64)

theorem addSpinRowsOf_empty_readSound :
    MemoryBusRowsPrefixReadSound
      ({} : Std.ExtHashMap Nat (BitVec 8))
      ((List.range addSpinAcceptedTrace.numInstructions).flatMap (fun _ => [])) := by
  change MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8)) []
  intro priorRows entry laterRows h_split h_selected
  simp at h_split

def addSpinBootSeed :
    BootSegmentMemorySeed addSpinAcceptedTrace addSpinSailTrace addSpinZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by
    intro h
    rfl
  step := by
    intro j h
    change j + 1 < 2 at h
    have hj : j = 0 := by omega
    subst j
    simp [addSpinSailTrace, addSpinState, replayMemoryAfterBusRows]
  readSound := addSpinRowsOf_empty_readSound
  placement := by
    intro i
    fin_cases i <;> trivial

end ZiskFv.Compliance.AddSpinRootSoundness
