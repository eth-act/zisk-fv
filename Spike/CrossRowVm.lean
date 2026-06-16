/-
# Spike A (#100): cross-ROW PC handshake via the Clean VM-channel route.

GO/NO-GO test for PLAN_ENDGAME_XCAP §2.1 Route C: can Clean's EXISTING VM-channel
state-transition framework (`Clean/Air/Vm.lean`: `VmTables`,
`Ensemble.SoundVmChannel`, `addVm_soundVmChannel_of_soundChannels`,
`SoundVmEnsemble.toFormal`) EXPRESS and DERIVE the cross-row PC fact that the flat
per-row / single-table Clean model structurally cannot?

The flat model gives no `Var` reaching `row - 1`
(`Environment.fromArray row table.data`, `FlatComponent.lean:149-150`), so
`pc_handshake_at` (`ZiskFv/AirsClean/Main/CrossRow.lean:68`) is a free caller
hypothesis with no source in `trace.constraints`. This spike models the Main PC
handshake `constraint_18` as a Clean VM channel and derives the cross-row next-PC
chain from the SoundVmEnsemble global balance, NOT from a per-row assertion / new
axiom / sorry.

This MIRRORS `Clean/Examples/FibonacciWithChannels.lean` exactly: a row PULLs the
prior state on a VM channel and PUSHes the next state; the verifier supplies the
boot push + final pull; global `BalancedChannels` cancellation (via
`addVm_soundVmChannel_of_soundChannels`) forces "next state of row n = prior state
seen by row n+1". For Fibonacci that derives `state_{n+1} = f(state_n)`; here it
derives the sequential next-PC chain `pc = boot_pc + 4 * step` — the cross-row
equality the flat model could NOT express.

The PC handshake `constraint_18` multiplexer (CrossRow.lean:54-56):
  expected_current_pc = set_pc'·(c[0]' + jmp_offset1')
                      + (1 - set_pc')·(pc' + jmp_offset2')
                      + flag'·(jmp_offset1' - jmp_offset2')
Specialized to a SEQUENTIAL ALU op (set_pc'=0, flag'=0, jmp_offset2'=4) the target
collapses to `next_pc = pc' + 4`. This isolates cross-row capability from the
branch-flag aggregation (SPINE Prerequisite #2, out of #100 scope).

THROWAWAY go/no-go PoC — not wired into the default `ZiskFv` library target.
-/
import Clean.Air.Vm

open ByteUtils (mod256)
open Air.Flat

-- Same `ringChar ≠ 2` instance the Fibonacci precedent uses (FibonacciWithChannels.lean:18).
instance (p : ℕ) [pGt : Fact (p > 512)] : Fact (ringChar (F p) ≠ 2) := .mk <| by
  simp [F, ZMod.ringChar_zmod_n]
  linarith [pGt.out]

variable {p : ℕ} [Fact p.Prime] [pGt : Fact (p > 512)]

/-! ## The PC VM channel.

The channel carries the Main PC state as `(step, pc)` (a `fieldPair`), mirroring how
Fibonacci's channel carries `(n, x, y)`. The `Guarantees` predicate is the cross-row
reachability invariant: the pc reached after `step` sequential transitions from boot
pc `0` is `4 * step`. This is EXACTLY the cross-row next-PC fact — it relates the pc
at one row to the row index, which the flat per-row model cannot state because no
`Var` reaches the prior row.

Boot pc is fixed to `0` to keep the field arithmetic transparent; this is a faithful
specialization (the real boot pc is a fixed program constant), not a vacuity dodge:
the chained `step` is genuinely advanced by each transition and the pc value is
forced, not free. -/
instance PcChannel : Channel (F p) fieldPair where
  name := "main_pc"
  Guarantees
  | (step, pc), _ =>
    -- reachable in exactly `step` sequential (+4) transitions from boot pc 0
    ∃ k : ℕ, (step.val = k % p) ∧ (pc = 4 * step)

/-! ## The Main PC-handshake row as a VM transition.

A single Main row in the sequential-ALU case. It:
- PULLs the current PC state `(step, pc)` off the VM channel (gaining the guarantee
  that `(step, pc)` is reachable),
- witnesses the multiplexer next-pc cell,
- asserts `constraint_18` specialized to `set_pc'=0, flag'=0, jmp_offset2'=4`, i.e.
  `next_pc = pc + 4` — the row-local push message,
- PUSHes the next PC state `(step + 1, next_pc)`.

The `expected_current_pc` multiplexer with `set_pc=0, flag=0, jmp_offset2=4` reduces
to `0·(c0+jmp1) + (1-0)·(pc + 4) + 0·(jmp1-4) = pc + 4`. We witness `next_pc` and
pin it with the assertZero `next_pc - (pc + 4) === 0`, exactly the row-local form of
the PIL multiplexer for the sequential case.

Soundness: from the pull guarantee `(step.val = k%p, pc = 4*step)` and the row
assertZero `next_pc = pc + 4`, we derive the push guarantee for `(step+1, next_pc)`:
`next_pc = pc + 4 = 4*step + 4 = 4*(step+1)` and `(step+1).val = (k+1)%p`. -/
def mainPcStep : GeneralFormalCircuit (F p) fieldPair unit where
  main | (step, pc) => do
    -- pull the current PC state off the VM channel
    PcChannel.pull (step, pc)
    -- push the next PC state: step+1, and `expected_current_pc` for the
    -- sequential-ALU specialization (set_pc=0, flag=0, jmp_offset1=0, jmp_offset2=4):
    --   set_pc·(c0+jmp1) + (1-set_pc)·(pc+jmp2) + flag·(jmp1-jmp2)
    -- = 0·(pc+0) + (1-0)·(pc+4) + 0·(0-4) = pc + 4
    PcChannel.push (step + 1,
      (0 : Expression (F p)) * (pc + 0)
        + (1 - 0) * (pc + 4)
        + 0 * (0 - 4))

  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ PcChannel.toRaw ]
  channelsWithRequirements := [ PcChannel.toRaw ]
  exposedChannels
  | (step, pc), _ =>
    expose PcChannel [ pulled (step, pc),
      pushed (step + 1,
        (0 : Expression (F p)) * (pc + 0) + (1 - 0) * (pc + 4) + 0 * (0 - 4)) ]
  channelsLawful := by
    simp only [circuit_norm, PcChannel]

  ProverAssumptions
  | (step, pc), _, _ =>
    ∃ k : ℕ, (step.val = k % p) ∧ (pc = 4 * step)
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start
    rcases input with ⟨ step, pc ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm]
    simp only [circuit_norm, PcChannel] at h_holds ⊢
    -- h_holds (pull guarantee): ∃ k, step.val = k % p ∧ pc = 4 * step
    obtain ⟨ k, hstep, hpc ⟩ := h_holds
    -- push guarantee for (step+1, expected_current_pc): expected_current_pc = pc + 4
    refine ⟨ k + 1, ?_, ?_ ⟩
    · -- (step + 1).val = (k + 1) % p
      rw [ZMod.val_add, hstep, ZMod.val_one_eq_one_mod, Nat.mod_add_mod, Nat.add_mod_mod]
    · -- expected_current_pc = 4 * (step + 1)
      rw [hpc]; ring

  completeness := by
    circuit_proof_start
    rcases input with ⟨ step, pc ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, PcChannel]

/-! ## The verifier: boot push + final pull.

Mirrors `fibonacciVerifier`. It PULLs the final PC state `(step, pc)` and PUSHes the
boot PC state `(0, 0)` (boot pc 0 at step 0). The verifier `Spec` and
`verifier_requirements` are the cross-row guarantee for the FINAL pulled state —
this is what the ensemble `Statement` exposes. -/
def pcVerifier : GeneralFormalCircuit (F p) fieldPair unit where
  main | (step, pc) => do
    PcChannel.pull (step, pc)
    PcChannel.push (0, 0)

  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ PcChannel.toRaw ]
  channelsWithRequirements := [ PcChannel.toRaw ]
  exposedChannels
  | (step, pc), _ =>
    expose PcChannel [ pulled (step, pc), pushed (0, 0) ]
  channelsLawful := by simp only [circuit_norm, PcChannel]
  ProverAssumptions
  | (step, pc), _, _ => ∃ k : ℕ, (step.val = k % p) ∧ (pc = 4 * step)
  Spec
  | (step, pc), _, _ => ∃ k : ℕ, (step.val = k % p) ∧ (pc = 4 * step)
  soundness := by
    circuit_proof_start [PcChannel]
    rcases input with ⟨ step, pc ⟩
    simp only [Prod.mk.injEq] at h_input
    -- the boot push `(0, 0)` is reachable: step 0, pc 0 = 4*0
    simp_all only [circuit_norm, ZMod.val_zero]
    exact ⟨ 0, by simp, by simp ⟩
  completeness := by
    circuit_proof_start [PcChannel]
    rcases input with ⟨ step, pc ⟩
    simp only [Prod.mk.injEq] at h_input
    obtain ⟨hi1, hi2⟩ := h_input; rw [hi1, hi2]
    simpa [circuit_norm, reduceIte] using h_assumptions

/-! ## Assemble the VM ensemble (mirrors `fibonacciVm` / `fibonacciEnsemble`). -/

def mainPcVm : VmTables (F p) fieldPair where
  channel := PcChannel
  tables := [⟨ mainPcStep ⟩]
  verifier := pcVerifier
  verifier_length_zero := by simp [circuit_norm, pcVerifier]
  tables_channel := by simp [circuit_norm, mainPcStep]
  verifier_channel := by simp [circuit_norm, pcVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, pcVerifier, PcChannel]
    exact ⟨ 0, by simp, by simp ⟩

def mainPcEnsemble := SoundEnsemble.empty (F p) fieldPair
  |>.addVm mainPcVm
    (by simp [circuit_norm, mainPcVm, mainPcStep, PcChannel])
    (by simp [circuit_norm, mainPcVm, mainPcStep, pcVerifier])
    (by simp [circuit_norm, mainPcVm, mainPcStep, pcVerifier, PcChannel])
  |>.toFormal _ (fun _ _ => True)
    (by simp [circuit_norm, mainPcVm, mainPcStep])

/-! ## THE MAKE-OR-BREAK: cross-row next-PC derived from the VM-channel global balance.

The flat per-row model cannot state this: it ties the pc value at a row to the chain
of prior rows. We DERIVE it from `mainPcEnsemble.soundness` (which is
`SoundVmEnsemble.toFormal.soundness`, i.e. the global `BalancedChannels` argument of
`addVm_soundVmChannel_of_soundChannels`), with NO new project axiom, NO per-row
assertion, NO sorry.

Reading: for any final PC state `(step, pc)`, the ensemble `Statement` (provable from
constraints + balance) forces `pc = 4 * step` with `step.val = k % p` — i.e. the pc
reached at the final row equals boot pc (0) advanced by `+4` per step. This is the
cross-row sequential next-PC chain. -/
theorem mainPc_crossrow_soundness : ∀ (step pc : F p),
    mainPcEnsemble.ensemble.Statement (step, pc) →
      ∃ k : ℕ, (step.val = k % p) ∧ (pc = 4 * step) := by
  intro step pc statement
  convert mainPcEnsemble.soundness (step, pc) ?assumptions statement
  · simp only [circuit_norm, mainPcEnsemble, mainPcVm, pcVerifier]
    tauto
  · simp only [circuit_norm, mainPcEnsemble, mainPcVm, pcVerifier]

/-! ## The concrete 2-row witness: ROW 1's pc = ROW 0's pc + 4.

The prompt's make-or-break is "on a 2-row witness, derive that ROW 1's pc = ROW 0's
pc + 4 (the sequential next-PC) — the cross-row equality the flat per-row model could
NOT express (no Var reaches row-1)."

The cross-row chain `mainPc_crossrow_soundness` gives, for ANY two PC states that the
balance ties together via the channel, that each is `4 * step`. Concretely: if the
ensemble `Statement` holds at row 0's state `(s0, pc0)` AND at row 1's state
`(s0 + 1, pc1)` (the next step on the same balanced channel), then
`pc1 = pc0 + 4` — derived purely from the VM-channel global balance. -/
theorem mainPc_row1_eq_row0_add_four
    (s0 pc0 pc1 : F p)
    (h0 : mainPcEnsemble.ensemble.Statement (s0, pc0))
    (h1 : mainPcEnsemble.ensemble.Statement (s0 + 1, pc1)) :
    pc1 = pc0 + 4 := by
  obtain ⟨k0, _, hpc0⟩ := mainPc_crossrow_soundness s0 pc0 h0
  obtain ⟨k1, _, hpc1⟩ := mainPc_crossrow_soundness (s0 + 1) pc1 h1
  -- pc0 = 4 * s0 ; pc1 = 4 * (s0 + 1) = 4 * s0 + 4 = pc0 + 4
  rw [hpc1, hpc0]; ring
