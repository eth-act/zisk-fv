import ZiskFv.Compliance.TraceLevelExport.MappedSourceSailChain
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement

/-!
# Register agreement along actual source starts

The bounded register recurrence executes exactly the channel writes of the real
architectural steps. Auxiliary physical rows do not introduce a Sail action.
Soundness of a prefix uses only soundness of strictly preceding source steps.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows
open Goldilocks

/-- The register-file action of a channel's actual write entry, including its
actual byte-lane value. This is also useful for no-write physical transport. -/
noncomputable def mappedRegWriteAction (out : ZiskFv.Channels.ChannelEnsembleOutput)
    (regs : Fin 32 → BitVec 64) (k : Fin 32) : BitVec 64 :=
  match stepRegWrite out with
  | some e => if Transpiler.wrap_to_regidx e.ptr = k then entryRegValue e else regs k
  | none => regs k

theorem mappedRegWriteAction_of_none (out : ZiskFv.Channels.ChannelEnsembleOutput)
    (regs : Fin 32 → BitVec 64) (h : stepRegWrite out = none) :
    mappedRegWriteAction out regs = regs := by
  funext k
  simp [mappedRegWriteAction, h]

variable {m : Nat} {words : Fin m → BitVec 32}
variable (L : ∀ i, SuccessfulRowLowering (words i))
variable {trace : AcceptedZiskTrace (sourceEnd L)}
variable (steps : ∀ i : Fin m, ZiskStep trace (physicalStart L i))
variable (decoded : ∀ i : Fin m, RowDecode trace (physicalStart L i) (steps i))

/-- Zero boot followed by exactly the actual writes at computed physical starts.
The bound rules out any out-of-range or default step. -/
noncomputable def mappedZiskRegFile : (j : Nat) → j ≤ m → Fin 32 → BitVec 64
  | 0, _ => fun _ => 0
  | j + 1, _ => mappedRegWriteAction
      (stepChannelOutput (physicalStart L ⟨j, by omega⟩)
        (steps ⟨j, by omega⟩) (decoded ⟨j, by omega⟩))
      (mappedZiskRegFile j (by omega))

@[simp] theorem mappedZiskRegFile_zero (h : 0 ≤ m) (k : Fin 32) :
    mappedZiskRegFile L steps decoded 0 h k = 0 := rfl

theorem mappedZiskRegFile_succ (i : Fin m) :
    mappedZiskRegFile L steps decoded (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      mappedRegWriteAction
        (stepChannelOutput (physicalStart L i) (steps i) (decoded i))
        (mappedZiskRegFile L steps decoded i.val (Nat.le_of_lt i.isLt)) := rfl

/-- A finite architectural prefix consisting only of actual source indices. -/
def mappedRegPrefix : (j : Nat) → j ≤ m → List (Fin m)
  | 0, _ => []
  | j + 1, _ => mappedRegPrefix j (by omega) ++ [⟨j, by omega⟩]

/-- Pointwise write actions fold over the finite real architectural prefix.
This form permits insertion/removal of genuine physical no-write actions. -/
theorem mappedZiskRegFile_eq_fold (j : Nat) (h : j ≤ m) :
    mappedZiskRegFile L steps decoded j h =
      (mappedRegPrefix j h).foldl
        (fun regs i => mappedRegWriteAction
          (stepChannelOutput (physicalStart L i) (steps i) (decoded i)) regs)
        (fun _ => 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [mappedZiskRegFile, mappedRegPrefix, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]

variable (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)

/-- Agreement on Sail's actual general-register cells, away from x0. -/
def mappedRegAgree (j : Nat) (h : j ≤ m) : Prop :=
  ∀ k : Fin 32, k ≠ 0 →
    (mappedSailStates L steps init j h).regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv])
        (mappedZiskRegFile L steps decoded j h k))

/-- This is precisely the existing register boot condition, unchanged. -/
theorem mappedRegAgree_zero
    (regBoot : ∀ k : Fin 32, k ≠ 0 →
      init.regs.get? (reg_of_fin k) =
        some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64))) :
    mappedRegAgree L steps decoded init 0 (Nat.zero_le m) := by
  intro k hk
  exact regBoot k hk

private lemma mapped_reg_of_fin_ne_nextPC (k : Fin 32) :
    reg_of_fin k ≠ Register.nextPC := by
  fin_cases k <;> simp [reg_of_fin]

private lemma mapped_reg_of_fin_injective {k₁ k₂ : Fin 32}
    (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0)
    (h : reg_of_fin k₁ = reg_of_fin k₂) : k₁ = k₂ := by
  revert h₁ h₂ h
  revert k₁ k₂
  decide

/-- Actual step soundness and the preceding invariant suffice for writeback.
No soundness of a future or auxiliary physical step is assumed. -/
theorem mappedRegAgree_succ (i : Fin m)
    (sound : StepSound trace (mappedSailTrace L steps init)
      (physicalStart L i) (steps i) (decoded i))
    (prev : mappedRegAgree L steps decoded init i.val (Nat.le_of_lt i.isLt)) :
    mappedRegAgree L steps decoded init (i.val + 1) (Nat.succ_le_of_lt i.isLt) := by
  intro k hk
  obtain ⟨result, post, h_ok⟩ :=
    stepChannelOutput_busEffect_ok (physicalStart L i) (steps i) (decoded i)
      (mappedSailTrace L steps init (physicalStart L i))
  have h_exec : execute_instruction (sailInstructionOf (physicalStart L i) (steps i))
      (mappedSailTrace L steps init (physicalStart L i)) = .ok result post :=
    ((stepSound_iff (physicalStart L i) (steps i) (decoded i)).mp sound).trans h_ok
  have h_regs :
      (mappedSailStates L steps init (i.val + 1) (Nat.succ_le_of_lt i.isLt)).regs.get?
          (reg_of_fin k) = post.regs.get? (reg_of_fin k) := by
    rw [mappedSailStates_retire L steps init i result post h_exec,
      retirePC_general_register]
  obtain ⟨v, h_post_regs⟩ :=
    post_regs_eq_of_stepChannelOutput (physicalStart L i) (steps i) (decoded i)
      (mappedSailTrace L steps init (physicalStart L i)) post result h_ok
  change _ = some (cast (by rw [register_type_reg_of_fin_equiv])
    (mappedZiskRegFile L steps decoded (i.val + 1) (Nat.succ_le_of_lt i.isLt) k))
  rw [h_regs, h_post_regs, mappedZiskRegFile_succ]
  unfold mappedRegWriteAction
  rw [Std.ExtDHashMap.get?_insert,
    dif_neg (by simp only [beq_iff_eq]; exact Ne.symm (mapped_reg_of_fin_ne_nextPC k))]
  cases hw : stepRegWrite
      (stepChannelOutput (physicalStart L i) (steps i) (decoded i)) with
  | none =>
      simpa only [state_at_start] using prev k hk
  | some e =>
      by_cases heq : Transpiler.wrap_to_regidx e.ptr = k
      · have hnz : Transpiler.wrap_to_regidx e.ptr ≠ 0 := by rw [heq]; exact hk
        subst heq
        dsimp only
        rw [if_neg hnz, if_pos rfl, Std.ExtDHashMap.get?_insert,
          dif_pos (by simp only [beq_self_eq_true])]
        simp
      · by_cases hz : Transpiler.wrap_to_regidx e.ptr = 0
        · dsimp only
          rw [if_pos hz, if_neg heq]
          simpa only [state_at_start] using prev k hk
        · have hne : reg_of_fin (Transpiler.wrap_to_regidx e.ptr) ≠ reg_of_fin k :=
            fun hc => heq (mapped_reg_of_fin_injective hz hk hc)
          dsimp only
          rw [if_neg hz, if_neg heq, Std.ExtDHashMap.get?_insert,
            dif_neg (by simp only [beq_iff_eq]; exact hne)]
          simpa only [state_at_start] using prev k hk

/-- Bounded prefix induction consumes only preceding real architectural sounds.
In particular the endpoint j = m requires no fictitious step at m. -/
theorem mappedRegAgree_prefix
    (regBoot : ∀ k : Fin 32, k ≠ 0 →
      init.regs.get? (reg_of_fin k) =
        some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (j : Nat) (h : j ≤ m)
    (sounds : ∀ i : Fin m, i.val < j →
      StepSound trace (mappedSailTrace L steps init)
        (physicalStart L i) (steps i) (decoded i)) :
    mappedRegAgree L steps decoded init j h := by
  induction j with
  | zero => exact mappedRegAgree_zero L steps decoded init regBoot
  | succ j ih =>
      have hj : j < m := by omega
      exact mappedRegAgree_succ L steps decoded init ⟨j, hj⟩
        (sounds ⟨j, hj⟩ (by simp))
        (ih (by omega) (fun i hi => sounds i (by omega)))

end ZiskFv.Compliance.SerializedExecutionRows
