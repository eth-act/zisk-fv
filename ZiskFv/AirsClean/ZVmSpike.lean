import ZiskFv.Channels.OperationBus
import Clean.Air.Vm

/-!
# C0f — Z-VM spike: cross-row state handshake via `addVm`

A minimal `VmTables` — a verifier that pulls one op-bus message and pushes
it back (an identity cross-row handshake), `tables := []` — assembled onto
a `SoundEnsemble` via `addVm`. Confirms the cross-row mechanism composes
with our FGL / `OpBusChannel` setup.
-/

namespace ZiskFv.AirsClean.ZVmSpike

open Goldilocks
open ZiskFv.Channels.OperationBus
open Air.Flat

/-- Toy VM verifier: pulls one op-bus message and pushes it back — a
    minimal cross-row identity handshake. -/
def vmVerifier : GeneralFormalCircuit FGL OpBusMessage unit where
  name := "z-vm-spike-verifier"
  main msg := do
    OpBusChannel.pull msg
    OpBusChannel.push msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [OpBusChannel.toRaw]
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels msg _ := expose OpBusChannel [pulled msg, pushed msg]
  channelsLawful := by simp only [circuit_norm, OpBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [OpBusChannel]
  completeness := by circuit_proof_start [OpBusChannel]

/-- Goldilocks characteristic is the prime, not 2 — needed by `addVm`. -/
instance : Fact (ringChar FGL ≠ 2) :=
  ⟨by have h : ringChar FGL = GL_prime := ZMod.ringChar_zmod_n GL_prime; omega⟩

/-- The toy VM: the identity-handshake verifier, no tables. -/
def toyVm : VmTables FGL OpBusMessage where
  channel := OpBusChannel
  tables := []
  verifier := vmVerifier
  verifier_length_zero := by intro pi; simp [circuit_norm, vmVerifier]
  tables_channel := by simp
  verifier_channel := by
    simp only [circuit_norm, vmVerifier, OpBusChannel]
    exact ⟨_, _, rfl⟩
  verifier_requirements := by
    intro env _
    simp only [circuit_norm, vmVerifier, OpBusChannel]

/-- The toy VM assembled onto an empty `SoundEnsemble` via `addVm` — the
    C0f GO criterion: the cross-row assembly API composes. -/
def toyVmEnsemble : SoundVmEnsemble FGL OpBusMessage :=
  SoundEnsemble.empty FGL OpBusMessage
    |>.addVm toyVm
        (by simp [circuit_norm, toyVm, vmVerifier, OpBusChannel])
        (by simp [circuit_norm, toyVm, vmVerifier, OpBusChannel])
        (by simp [circuit_norm, toyVm, vmVerifier, OpBusChannel])

end ZiskFv.AirsClean.ZVmSpike
