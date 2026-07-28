import ZiskFv.Compliance.DivSpinWitness
import ZiskFv.Soundness

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-!
# Concrete `root_soundness` instantiation for signed DIV

The four executed rows initialize x1 and x2, compute `6 / 2 = 3`, and finish
at the self-looping JAL.  The DIV input is reconstructed from the accepted
Main and selected physical Arith row.
-/

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.AirsClean.Main
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.DivSpinRootSoundness

def x0 : regidx := regidx.Regidx (0#5)
def x1 : regidx := regidx.Regidx (1#5)
def x2 : regidx := regidx.Regidx (2#5)
def x3 : regidx := regidx.Regidx (3#5)

def divSpinAddiX1Index : Fin 4 := ⟨0, by decide⟩
def divSpinAddiX2Index : Fin 4 := ⟨1, by decide⟩
def divSpinDivIndex : Fin 4 := ⟨2, by decide⟩
def divSpinJalIndex : Fin 4 := ⟨3, by decide⟩

def divSpinAddiX1Claim : Claim_addi divSpinAcceptedTrace divSpinAddiX1Index where
  r1 := x0
  rd := x1
  imm := 6#12

def divSpinAddiX2Claim : Claim_addi divSpinAcceptedTrace divSpinAddiX2Index where
  r1 := x0
  rd := x2
  imm := 2#12

def divSpinDivClaim : Claim_div divSpinAcceptedTrace divSpinDivIndex where
  r1 := x1
  r2 := x2
  rd := x3

def divSpinJalClaim : Claim_jal divSpinAcceptedTrace divSpinJalIndex where
  imm := 0#21
  rd := x0

def divSpinZiskStep : ∀ i : Fin 4, ZiskStep divSpinAcceptedTrace i
  | ⟨0, _⟩ => .addi divSpinAddiX1Claim
  | ⟨1, _⟩ => .addi divSpinAddiX2Claim
  | ⟨2, _⟩ => .div divSpinDivClaim
  | ⟨3, _⟩ => .jal divSpinJalClaim

def divSpinMisa : RegisterType Register.misa := 0#64

def divSpinRegs (pc x1Value x2Value x3Value : BitVec 64) :
    Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.misa divSpinMisa
  let regs3 := regs2.insert (reg_of_fin (regidx_to_fin x1)) x1Value
  let regs4 := regs3.insert (reg_of_fin (regidx_to_fin x2)) x2Value
  regs4.insert (reg_of_fin (regidx_to_fin x3)) x3Value

def divSpinState (pc x1Value x2Value x3Value : BitVec 64) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := divSpinRegs pc x1Value x2Value x3Value
    mem := {} }

def divSpinSailTrace : SailTrace 4
  | ⟨0, _⟩ => divSpinState (0#64) (0#64) (0#64) (0#64)
  | ⟨1, _⟩ => divSpinState (4#64) (6#64) (0#64) (0#64)
  | ⟨2, _⟩ => divSpinState (8#64) (6#64) (2#64) (0#64)
  | ⟨3, _⟩ => divSpinState (12#64) (6#64) (2#64) (3#64)

theorem divSpinRowsOf_empty_readSound :
    MemoryBusRowsPrefixReadSound
      ({} : Std.ExtHashMap Nat (BitVec 8))
      ((List.range divSpinAcceptedTrace.numInstructions).flatMap (fun _ => [])) := by
  change MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8)) []
  intro priorRows entry laterRows h_split h_selected
  simp at h_split

def divSpinBootSeed :
    BootSegmentMemorySeed divSpinAcceptedTrace divSpinSailTrace divSpinZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by intro _; rfl
  step := by
    intro j h
    change j + 1 < 4 at h
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl <;>
      simp [divSpinSailTrace, divSpinState, replayMemoryAfterBusRows]
  readSoundInputs := fun h => absurd h divSpinWitness_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_nonempty
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_nonempty
  placement := by
    intro i
    fin_cases i <;> simp [MemoryOpPlacement, divSpinZiskStep]

end ZiskFv.Compliance.DivSpinRootSoundness
