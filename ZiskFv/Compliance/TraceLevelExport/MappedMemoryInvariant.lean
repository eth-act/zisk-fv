import ZiskFv.Compliance.TraceLevelExport.MappedSourceSailChain
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.TakeDrop

/-!
# Actual mapped architectural memory replay

The full channel effect and the architectural memory-row replay have the same
memory action. The channel shape used below is proved for the actual decoded
step, not supplied by a caller. In particular, the store action is the exact
eight-byte update already used by memory replay, including preserved lanes of
narrow stores.

The bounded invariant consumes soundness only at preceding real source starts.
It neither changes the boot-memory seed nor removes its successor obligation by
assuming future soundness. Auxiliary physical rows introduce no Sail action;
the physical replay spine can transport the exact finite prefix proved here.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Goldilocks
open CanonicalExecutionRows
open ZiskFv.ZiskCircuit.MemTrace

private lemma memory_one_ne_neg_one : ((1 : FGL) = -1) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private lemma memory_one_ne_two : ((1 : FGL) = 2) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private lemma memory_neg_one_ne_one : ((-1 : FGL) = 1) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private lemma memory_as_one_val : ((1 : FGL) : Nat) = 1 := rfl

private lemma memory_as_two_val : ((2 : FGL) : Nat) = 2 := rfl

private lemma post_mem_eq_of_busEffect_ok_nil
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_ok : (bus_effect execRows [] state).2 = .ok result post) :
    post.mem = state.mem := by
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_nil,
    Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

private lemma post_mem_eq_of_busEffect_ok_one
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m : e.multiplicity = 1) (h_a : e.as = 1)
    (h_ok : (bus_effect execRows [e] state).2 = .ok result post) :
    post.mem = state.mem := by
  by_cases h_z : Transpiler.wrap_to_regidx e.ptr = 0
  · unfold bus_effect at h_ok
    simp only [h_len, h_ex0, h_ex1, and_self, if_true,
      List.foldl_cons, List.foldl_nil, h_m, h_a, memory_one_ne_neg_one,
      memory_as_one_val, if_false, dif_pos h_z,
      write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
    cases h_ok
    rfl
  · unfold bus_effect at h_ok
    simp only [h_len, h_ex0, h_ex1, and_self, if_true,
      List.foldl_cons, List.foldl_nil, h_m, h_a, memory_one_ne_neg_one,
      memory_as_one_val, if_false, dif_neg h_z,
      write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
    cases h_ok
    rfl

private lemma post_mem_eq_of_busEffect_ok_three_register
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m0 : e0.multiplicity = -1) (h_a0 : e0.as = 1)
    (h_m1 : e1.multiplicity = -1) (h_a1 : e1.as = 1 ∨ e1.as = 2)
    (h_m2 : e2.multiplicity = 1) (h_a2 : e2.as = 1)
    (h_ok : (bus_effect execRows [e0, e1, e2] state).2 = .ok result post) :
    post.mem = state.mem := by
  rcases h_a1 with h_a1 | h_a1
  all_goals
    by_cases h_z : Transpiler.wrap_to_regidx e2.ptr = 0
    · unfold bus_effect at h_ok
      simp only [h_len, h_ex0, h_ex1, and_self, if_true,
        List.foldl_cons, List.foldl_nil, h_m0, h_m1, h_m2, h_a0, h_a1, h_a2,
        memory_one_ne_neg_one, memory_as_one_val, memory_as_two_val,
        if_false, dif_pos h_z, write_xreg, Sail.writeReg, PreSail.writeReg,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
        EStateM.Result.map] at h_ok
      cases h_ok
      rfl
    · unfold bus_effect at h_ok
      simp only [h_len, h_ex0, h_ex1, and_self, if_true,
        List.foldl_cons, List.foldl_nil, h_m0, h_m1, h_m2, h_a0, h_a1, h_a2,
        memory_one_ne_neg_one, memory_as_one_val, memory_as_two_val,
        if_false, dif_neg h_z, write_xreg, Sail.writeReg, PreSail.writeReg,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
        EStateM.Result.map] at h_ok
      cases h_ok
      rfl

private lemma post_mem_eq_of_busEffect_ok_three_store
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m0 : e0.multiplicity = -1) (h_a0 : e0.as = 1)
    (h_m1 : e1.multiplicity = -1) (h_a1 : e1.as = 1)
    (h_m2 : e2.multiplicity = 1) (h_a2 : e2.as = 2)
    (h_ok : (bus_effect execRows [e0, e1, e2] state).2 = .ok result post) :
    post.mem = writeMemoryOfEntry state.mem e2 := by
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true,
    List.foldl_cons, List.foldl_nil, h_m0, h_m1, h_m2, h_a0, h_a1, h_a2,
    memory_one_ne_neg_one, memory_as_one_val, memory_as_two_val, if_false,
    Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- The actual channel effect replays all its actual memory-bus rows. The row
shape and execution-bus shape are derived from the decoded step itself. -/
theorem post_mem_eq_replay_of_stepChannelOutput
    {numInstructions : Nat} {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_ok : (bus_effect (stepChannelOutput i zs rd).execRows
      (stepChannelOutput i zs rd).memRows state).2 = .ok result post) :
    post.mem = replayMemoryAfterBusRows state.mem (stepChannelOutput i zs rd).memRows := by
  have hx := stepChannelOutput_execRows i zs rd
  have h_len : (stepChannelOutput i zs rd).execRows.length = 2 := by rw [hx]; rfl
  have h_ex0 : (stepChannelOutput i zs rd).execRows[0]!.multiplicity = -1 := by
    rw [hx]; rfl
  have h_ex1 : (stepChannelOutput i zs rd).execRows[1]!.multiplicity = 1 := by
    rw [hx]; rfl
  rcases stepChannelOutput_memRows_shape i zs rd with
    h_shape | ⟨e, h_shape, h_m, h_a⟩ |
      ⟨e0, e1, e2, h_shape, h_m0, h_a0, h_m1, h_m2, h_as⟩
  · rw [h_shape] at h_ok
    simpa only [h_shape, replayMemoryAfterBusRows, List.foldl_nil] using
      post_mem_eq_of_busEffect_ok_nil _ _ _ _ h_len h_ex0 h_ex1 h_ok
  · rw [h_shape] at h_ok
    simpa only [h_shape, replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
      replayMemoryAfterBusRow, h_a, memory_one_ne_two, if_false] using
      post_mem_eq_of_busEffect_ok_one _ _ _ _ _ h_len h_ex0 h_ex1 h_m h_a h_ok
  · rw [h_shape] at h_ok
    rcases h_as with ⟨h_a1, h_a2⟩ | ⟨h_a1, h_a2⟩ | ⟨h_a1, h_a2⟩
    · simpa only [h_shape, replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
        replayMemoryAfterBusRow, h_a0, h_a1, h_a2, memory_one_ne_two, if_false] using
        post_mem_eq_of_busEffect_ok_three_register _ _ _ _ _ _ _ h_len h_ex0 h_ex1
          h_m0 h_a0 h_m1 (Or.inl h_a1) h_m2 h_a2 h_ok
    · simpa only [h_shape, replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
        replayMemoryAfterBusRow, h_a0, h_a1, h_a2, h_m2, memory_one_ne_two,
        if_false, if_true, replayStoreEvent_storeEventOfEntry] using
        post_mem_eq_of_busEffect_ok_three_store _ _ _ _ _ _ _ h_len h_ex0 h_ex1
          h_m0 h_a0 h_m1 h_a1 h_m2 h_a2 h_ok
    · simpa only [h_shape, replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
        replayMemoryAfterBusRow, h_a0, h_a1, h_a2, h_m1, memory_one_ne_two,
        memory_neg_one_ne_one, if_false, if_true] using
        post_mem_eq_of_busEffect_ok_three_register _ _ _ _ _ _ _ h_len h_ex0 h_ex1
          h_m0 h_a0 h_m1 (Or.inr h_a1) h_m2 h_a2 h_ok

private lemma replay_register_one
    (mem : Std.ExtHashMap Nat (BitVec 8)) (e : Interaction.MemoryBusEntry FGL)
    (h_a : e.as = 1) :
    replayMemoryAfterBusRows mem [e] = replayMemoryAfterBusRows mem [] := by
  simp only [replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
    replayMemoryAfterBusRow, h_a, memory_one_ne_two, if_false]

private lemma replay_register_three
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_a0 : e0.as = 1) (h_a1 : e1.as = 1) (h_a2 : e2.as = 1) :
    replayMemoryAfterBusRows mem [e0, e1, e2] = replayMemoryAfterBusRows mem [] := by
  simp only [replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
    replayMemoryAfterBusRow, h_a0, h_a1, h_a2, memory_one_ne_two, if_false]

private lemma replay_drop_register_reads
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_a0 : e0.as = 1) (h_a1 : e1.as = 1) :
    replayMemoryAfterBusRows mem [e0, e1, e2] = replayMemoryAfterBusRows mem [e2] := by
  simp only [replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
    replayMemoryAfterBusRow, h_a0, h_a1, memory_one_ne_two, if_false]

private lemma replay_drop_register_sides
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_a0 : e0.as = 1) (h_a2 : e2.as = 1) :
    replayMemoryAfterBusRows mem [e0, e1, e2] = replayMemoryAfterBusRows mem [e1] := by
  simp only [replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
    replayMemoryAfterBusRow, h_a0, h_a2, memory_one_ne_two, if_false]

/-- All 63 decoded arms have exactly the architectural mutable-memory action:
seven load rows, four store rows, and no memory rows for the other arms. The
register rows are erased only from this memory action, not from physical slots. -/
theorem channel_replay_eq_memoryRowsOfStep
    {numInstructions : Nat} {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) (mem : Std.ExtHashMap Nat (BitVec 8)) :
    replayMemoryAfterBusRows mem (stepChannelOutput i zs rd).memRows =
      replayMemoryAfterBusRows mem (memoryRowsOfStep ziskTrace i zs) := by
  cases zs <;>
    first
    | exact replay_register_three mem _ _ _ rfl rfl rfl
    | exact replay_register_one mem _ rfl
    | exact replay_drop_register_reads mem _ _ _ rfl rfl
    | exact replay_drop_register_sides mem _ _ _ rfl rfl
    | rfl

section MappedMemory

variable {m : Nat} {words : Fin m → BitVec 32}
variable (L : ∀ i, SuccessfulRowLowering (words i))
variable {trace : AcceptedZiskTrace (sourceEnd L)}
variable (steps : ∀ i : Fin m, ZiskStep trace (physicalStart L i))
variable (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)

/-- A real source-start soundness fact determines the memory of its genuine
architectural successor, including the final successor at index `m`. -/
theorem mapped_mem_succ_of_stepSound (i : Fin m)
    (rd : RowDecode trace (physicalStart L i) (steps i))
    (sound : StepSound trace (mappedSailTrace L steps init)
      (physicalStart L i) (steps i) rd) :
    (mappedSailStates L steps init (i.val + 1) (Nat.succ_le_of_lt i.isLt)).mem =
      replayMemoryAfterBusRows
        (mappedSailStates L steps init i.val (Nat.le_of_lt i.isLt)).mem
        (memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
  obtain ⟨result, post, h_ok⟩ :=
    stepChannelOutput_busEffect_ok (physicalStart L i) (steps i) rd
      (mappedSailTrace L steps init (physicalStart L i))
  have h_exec : execute_instruction (sailInstructionOf (physicalStart L i) (steps i))
      (mappedSailTrace L steps init (physicalStart L i)) = .ok result post :=
    ((stepSound_iff (physicalStart L i) (steps i) rd).mp sound).trans h_ok
  rw [mappedSailStates_retire L steps init i result post h_exec, retirePC_mem]
  have h_mem := post_mem_eq_replay_of_stepChannelOutput (physicalStart L i) (steps i) rd
    (mappedSailTrace L steps init (physicalStart L i)) post result h_ok
  rw [channel_replay_eq_memoryRowsOfStep] at h_mem
  simpa only [state_at_start] using h_mem

private lemma mapped_memory_finRange_take_succ (i : Fin m) :
    (List.finRange m).take (i.val + 1) =
      (List.finRange m).take i.val ++ [i] := by
  simpa using (List.take_concat_get' (List.finRange m) i.val
    (by simpa using i.isLt)).symm

/-- Memory at a bounded architectural cursor is replay of precisely its real
preceding source indices. Only soundness strictly before that cursor is used;
there is no out-of-range/default step or premise about a future instruction. -/
theorem mapped_mem_prefix_of_stepSound
    (decoded : ∀ i : Fin m, RowDecode trace (physicalStart L i) (steps i))
    (j : Nat) (hj : j ≤ m)
    (sound : ∀ i : Fin m, i.val < j →
      StepSound trace (mappedSailTrace L steps init)
        (physicalStart L i) (steps i) (decoded i)) :
    (mappedSailStates L steps init j hj).mem =
      replayMemoryAfterBusRows init.mem
        (((List.finRange m).take j).flatMap
          (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i))) := by
  revert hj sound
  induction j with
  | zero =>
      intro hj sound
      rfl
  | succ j ih =>
      intro hj sound
      let i : Fin m := ⟨j, by omega⟩
      have hprev := ih (by omega) (fun k hk => sound k (by omega))
      calc
        (mappedSailStates L steps init (j + 1) hj).mem =
            replayMemoryAfterBusRows
              (mappedSailStates L steps init j (by omega)).mem
              (memoryRowsOfStep trace (physicalStart L i) (steps i)) :=
          mapped_mem_succ_of_stepSound L steps init i (decoded i)
            (sound i (by simp only [i, Fin.val_mk]; omega))
        _ = replayMemoryAfterBusRows
              (replayMemoryAfterBusRows init.mem
                (((List.finRange m).take j).flatMap
                  (fun k => memoryRowsOfStep trace (physicalStart L k) (steps k))))
              (memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
          rw [hprev]
        _ = replayMemoryAfterBusRows init.mem
              (((List.finRange m).take (j + 1)).flatMap
                (fun k => memoryRowsOfStep trace (physicalStart L k) (steps k))) := by
          rw [mapped_memory_finRange_take_succ i, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil,
            replayMemoryAfterBusRows_append]

end MappedMemory

end ZiskFv.Compliance.SerializedExecutionRows
