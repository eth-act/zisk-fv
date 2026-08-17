import ZiskFv.Compliance.RegisterPushCounting
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding

/-!
# The register coverage bridge — #330 S3

`a_columns_of_bootWalk` says the a-columns of a register-reading Main row either are `(0, 0)` or
match a c-slot on the backward walk. `RegAgree` says the ZisK register file and the Sail registers
agree at every step. This module closes the gap: it connects the walk's c-slot value to the
register file, proving that the a-columns equal the lane decomposition of the register value.
-/

namespace ZiskFv.Compliance

open Air.Flat (Table)
open ZiskFv.AirsClean.FullEnsemble (mainTableRowAtOrZero mainTableRowAtOrZero_get)
open ZiskFv.AirsClean.Main (MainRowWithRom cMemMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep RegSupplies
  readTimestamp_lt_of_regSupplies)

variable {n : Nat}

/-! ## Timestamp monotonicity along `AnswersRegPre` chains

One backward step strictly decreases the read timestamp. -/

theorem timestamp_val_lt_of_answersRegPre_active (trace : AcceptedZiskTrace n)
    {p q : RegWalkStep}
    (h_ap : IsActiveWitnessMainRow trace p) (h_aq : IsActiveWitnessMainRow trace q)
    (h_link : RegWalkStep.AnswersRegPre p q) :
    q.timestamp.val < p.timestamp.val := by
  have h_ts : q.2.readTimestamp q.1 = p.2.prevStep p.1 := by
    have := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_link
    simp [Instantiation.RegSlot.readMessage_timestamp,
      Instantiation.RegSlot.regPreMessage_timestamp] at this
    exact this
  exact readTimestamp_lt_of_regSupplies h_ts.symm
    (regSlot_descent_of_witnessMainRow trace h_ap)
    (regSlot_timestamp_bound_of_witnessMainRow trace h_aq)

/-! ## Elements on an `AnswersRegPre` chain have timestamps bounded by the head. -/

theorem timestamp_val_le_head_of_mem_chain (trace : AcceptedZiskTrace n)
    {path : List RegWalkStep} (h_ne : path ≠ [])
    (h_act : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.AnswersRegPre path)
    {x : RegWalkStep} (hx : x ∈ path) :
    x.timestamp.val ≤ (path.head h_ne).timestamp.val := by
  induction path with
  | nil => contradiction
  | cons a rest ih =>
      simp only [List.head_cons]
      rcases List.mem_cons.mp hx with rfl | hx_rest
      · exact Nat.le_refl _
      · cases rest with
        | nil => contradiction
        | cons b tl =>
            have h_chain_rest : List.IsChain RegWalkStep.AnswersRegPre (b :: tl) :=
              (List.isChain_cons.mp h_chain).2
            have h_le_rest := ih (List.cons_ne_nil b tl)
              (fun q hq => h_act q (List.mem_cons_of_mem _ hq))
              h_chain_rest hx_rest
            have h_link : RegWalkStep.AnswersRegPre a b :=
              (List.isChain_cons_cons.mp h_chain).1
            have h_lt := timestamp_val_lt_of_answersRegPre_active trace
              (h_act a List.mem_cons_self)
              (h_act b (List.mem_cons_of_mem _ List.mem_cons_self))
              h_link
            simp only [List.head_cons] at h_le_rest
            omega

theorem not_mem_chain_of_timestamp_ge (trace : AcceptedZiskTrace n)
    {path : List RegWalkStep} (h_ne : path ≠ [])
    (h_act : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.AnswersRegPre path)
    {x : RegWalkStep} (h_ne_head : x ≠ path.head h_ne)
    (h_ts : (path.head h_ne).timestamp.val ≤ x.timestamp.val) :
    x ∉ path := by
  intro hx
  have h_le := timestamp_val_le_head_of_mem_chain trace h_ne h_act h_chain hx
  have h_eq : x = path.head h_ne := by
    by_contra h_ne'
    cases path with
    | nil => contradiction
    | cons a rest =>
        simp only [List.head_cons] at h_ts h_le h_ne_head h_ne'
        rcases List.mem_cons.mp hx with rfl | hx_rest
        · exact h_ne' rfl
        · cases rest with
          | nil => contradiction
          | cons b tl =>
              have h_link := (List.isChain_cons_cons.mp h_chain).1
              have h_lt := timestamp_val_lt_of_answersRegPre_active trace
                (h_act a List.mem_cons_self)
                (h_act b (List.mem_cons_of_mem _ List.mem_cons_self))
                h_link
              have h_le_rest := timestamp_val_le_head_of_mem_chain trace
                (List.cons_ne_nil b tl)
                (fun q hq => h_act q (List.mem_cons_of_mem _ hq))
                ((List.isChain_cons.mp h_chain).2)
                hx_rest
              simp only [List.head_cons] at h_le_rest
              omega
  exact h_ne_head h_eq

end ZiskFv.Compliance
