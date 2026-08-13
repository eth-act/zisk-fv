import ZiskFv.Compliance.TraceLevelExport.ChainedSailTrace
import ZiskFv.Compliance.TraceLevelExport.RegisterWriteback

/-!
# The ZisK register file, and `RegAgree` — #330 Phase 4 S2

S1 (`RegisterValueTelescope.lean`) carries a value backwards along the memory bus to the boot
anchor. That is one half of the a-slot low-lane input field: it says what a ZisK operand column
holds, in ZisK's own terms. This module builds the other half — a **register file** the two machines
can be compared at, and the invariant `RegAgree` saying they agree.

(The field names are spelled out nowhere in this module on purpose. The slice's acceptance gate is a
raw `grep -rc` over `ZiskFv/`, so prose that quotes them inflates the count and makes the gate lie.)

## Why the file is defined from the channel output

`stepChannelOutput` is the object `StepSound` already compares Sail against — for every arm it is
one of five concrete bus shapes, and its memory rows are literally the Main row's `cMemMessage`
(`busSub.e2`, `eRdLui`, `eRdAt` are all `MemBusMessage.toEntry (cMemMessage row) 1 1`). Defining the
ZisK register file by folding the *same* entries makes the inductive step a statement about one
object rather than a correspondence between two, so the step reduces to the Sail-side writeback
lemmas in `RegisterWriteback.lean` with nothing left over.

The alternative — recursing over the Main table's `store_reg` flag — would need a per-opcode decode
fact tying `store_reg` to the arm's literal `as`, for all 63 arms, before the step could even be
stated. Nothing is hidden by the choice made here: `stepRegWrite` reads the entry off the same list
`bus_effect` folds.

## What `RegAgree 0` costs, stated plainly

`RegAgree 0` says every general register starts at `0`. It is a **new named boot premise**, in the
same class as `SegmentPcSeed.boot` and `BootSegmentMemorySeed`. Phase 4 is a real reduction only if
the 116 per-row `h_[ab]_[lo|hi]_t` fields go away against it; carrying both would be a strict loss.
That accounting is the slice's gate, not this module's.

## Where `RegAgree` has to be carried, and why it is not circular

`regAgree_succ` consumes `StepSound` at step `j`. `StepSound` at step `j` is in turn what an
`InputsCore_<op>`'s register fields feed — so once those fields are *derived* from `RegAgree`
instead of assumed, the two look circular. They are not: `RegAgree (j + 1)` needs `StepSound` only
at steps `≤ j`, and `StepSound j` needs `RegAgree` only at `j`. That is a single well-founded
interleaved induction on the step index, and Phase 7 already installed exactly that skeleton in
`stepSound_of_programDecodes`, carrying per-row PC agreement. `RegAgree` widens the invariant it
carries; it must not be derived *after* the fact from `∀ i, StepSound i`, which would be circular.
-/

namespace ZiskFv.Compliance

open Goldilocks

variable {numInstructions : ℕ}

/-- The 64-bit value a memory-bus entry carries, in the byte-lane form `bus_effect` writes back.
    Exactly the term `regs_write_of_busEffect_ok_three` produces, named once so the register file
    and the Sail lemma are visibly the same value. -/
noncomputable def entryRegValue (e : Interaction.MemoryBusEntry FGL) : BitVec 64 :=
  U64.toBV
    #v[Channels.MemoryBusBytes.byteAt e 0, Channels.MemoryBusBytes.byteAt e 1,
      Channels.MemoryBusBytes.byteAt e 2, Channels.MemoryBusBytes.byteAt e 3,
      Channels.MemoryBusBytes.byteAt e 4, Channels.MemoryBusBytes.byteAt e 5,
      Channels.MemoryBusBytes.byteAt e 6, Channels.MemoryBusBytes.byteAt e 7]

/-- **The step's register write, if it has one.** The three live bus shapes are: no memory rows
    (branches, `FENCE`), one row (`LUI` / `AUIPC` / `JAL` / `JALR`, whose single entry is the `rd`
    write), and three rows (two operand reads and a c-side write). Only an entry at address space
    `1` writes a register; a store's third entry rides at `as = 2` and touches memory instead. -/
noncomputable def stepRegWrite (out : ZiskFv.Channels.ChannelEnsembleOutput) :
    Option (Interaction.MemoryBusEntry FGL) :=
  match out.memRows with
  | [e] => if e.as = 1 then some e else none
  | [_, _, e2] => if e2.as = 1 then some e2 else none
  | _ => none

/-- **The ZisK register file after `j` executed steps.** Every general register starts at `0` — the
    value `RegisterBoundary.bootMessage` pushes — and each step overwrites at most one register,
    with the value its own memory-bus write entry carries. -/
noncomputable def ziskRegFile
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (rowDecode : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i)) :
    ℕ → Fin 32 → BitVec 64
  | 0, _ => 0
  | j + 1, k =>
      if h : j < ziskTrace.numInstructions then
        match stepRegWrite (stepChannelOutput ⟨j, h⟩ (ziskStep ⟨j, h⟩) (rowDecode ⟨j, h⟩)) with
        | some e =>
            if Transpiler.wrap_to_regidx e.ptr = k then entryRegValue e
            else ziskRegFile ziskStep rowDecode j k
        | none => ziskRegFile ziskStep rowDecode j k
      else ziskRegFile ziskStep rowDecode j k

@[simp] theorem ziskRegFile_zero
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (rowDecode : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i))
    (k : Fin 32) :
    ziskRegFile ziskStep rowDecode 0 k = 0 := rfl

/-- **The two machines agree on the general registers at step `j`.**

    `x0` is excluded: the memory-bus write entries never target it (`bus_effect` takes
    `wrap_to_regidx e.ptr ≠ 0` as a side condition, and the Sail register map has no `x0` cell), so
    there is nothing to state there. -/
def RegAgree
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (rowDecode : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (j : ℕ) : Prop :=
  ∀ k : Fin 32, k ≠ 0 →
    (chainedSailStates ziskStep init j).regs.get? (reg_of_fin k)
      = some (cast (by rw [register_type_reg_of_fin_equiv])
          (ziskRegFile ziskStep rowDecode j k))

/-! ## The post-state's registers, for the shapes `RegisterWriteback` does not cover

`RegisterWriteback.lean` proves the three-entry all-register shape, which is what an ALU arm uses.
`RegAgree`'s step has to hold at *every* arm, so the remaining live shapes need the same treatment:
a store's third entry rides at `as = 2` and writes memory, a load's second entry rides at `as = 2`
and reads it, `LUI` / `AUIPC` / `JAL` / `JALR` carry a single write entry, and the branches carry
none. Each proof is the existing one's shape — the `.ok` hypothesis rules out the error exits, so
the fold computes. -/

/-- `bus_effect`'s pull branch is decided by `as.val`, so the two literals it tests against need
    their `val`s. `2` is the memory address space. -/
private lemma as_two_val : ((2 : FGL) : ℕ) = 2 := rfl

private lemma as_two_ne_one : (((2 : FGL) : ℕ) = 1) = False := by
  simp only [eq_iff_iff, iff_false]; decide

/-- **A store leaves every register alone.** Its third entry rides at `as = 2`, so the fold writes
    memory and the register map only picks up `nextPC`. -/
private lemma post_eq_of_busEffect_ok_three_store
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
    post.regs
      = state.regs.insert Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_two_ne_neg_one : ((2 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_two_ne_one : ((2 : FGL) = 1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m0, h_m1, h_m2, h_a0, h_a1, h_a2, h_one_ne, h_one_val, as_two_val, as_two_ne_one,
    h_two_ne_neg_one, h_two_ne_one, if_false, if_true,
    write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- **The ALU shape's write.** `RegisterWriteback.lean` proves this post-state equation too, but
    keeps it `private` behind the two `get?` projections it exports; this module needs the equation
    itself to state all five shapes uniformly. -/
private lemma post_eq_of_busEffect_ok_three_write
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m0 : e0.multiplicity = -1) (h_a0 : e0.as = 1)
    (h_m1 : e1.multiplicity = -1) (h_a1 : e1.as = 1)
    (h_m2 : e2.multiplicity = 1) (h_a2 : e2.as = 1)
    (h_nz : Transpiler.wrap_to_regidx e2.ptr ≠ 0)
    (h_ok : (bus_effect execRows [e0, e1, e2] state).2 = .ok result post) :
    post.regs
      = (state.regs.insert (reg_of_fin (Transpiler.wrap_to_regidx e2.ptr))
            (cast (by rw [register_type_reg_of_fin_equiv]) (entryRegValue e2))).insert
          Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m0, h_m1, h_m2, h_a0, h_a1, h_a2, h_one_ne, h_one_val, if_false, if_true, dif_neg h_nz,
    write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- **A load still writes its destination register.** Only the second entry moves to `as = 2`; the
    third is the `rd` write, exactly as in the ALU shape. The `x0` branch is kept open because
    `bus_effect` skips the write when the target wraps to `0`. -/
private lemma post_eq_of_busEffect_ok_three_load
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m0 : e0.multiplicity = -1) (h_a0 : e0.as = 1)
    (h_m1 : e1.multiplicity = -1) (h_a1 : e1.as = 2)
    (h_m2 : e2.multiplicity = 1) (h_a2 : e2.as = 1)
    (h_nz : Transpiler.wrap_to_regidx e2.ptr ≠ 0)
    (h_ok : (bus_effect execRows [e0, e1, e2] state).2 = .ok result post) :
    post.regs
      = (state.regs.insert (reg_of_fin (Transpiler.wrap_to_regidx e2.ptr))
            (cast (by rw [register_type_reg_of_fin_equiv]) (entryRegValue e2))).insert
          Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_two_ne_neg_one : ((2 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m0, h_m1, h_m2, h_a0, h_a1, h_a2, h_one_ne, h_one_val, as_two_val, as_two_ne_one,
    h_two_ne_neg_one, if_false, if_true, dif_neg h_nz,
    write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- **The single-entry shape.** `LUI` / `AUIPC` / `JAL` / `JALR` emit only the `rd` write. -/
private lemma post_eq_of_busEffect_ok_one
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m : e.multiplicity = 1) (h_a : e.as = 1)
    (h_nz : Transpiler.wrap_to_regidx e.ptr ≠ 0)
    (h_ok : (bus_effect execRows [e] state).2 = .ok result post) :
    post.regs
      = (state.regs.insert (reg_of_fin (Transpiler.wrap_to_regidx e.ptr))
            (cast (by rw [register_type_reg_of_fin_equiv]) (entryRegValue e))).insert
          Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m, h_a, h_one_ne, h_one_val, if_false, if_true, dif_neg h_nz,
    write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- **The empty shape.** A branch or `FENCE` touches no memory bus entry, so only `nextPC` moves. -/
private lemma post_eq_of_busEffect_ok_nil
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_ok : (bus_effect execRows [] state).2 = .ok result post) :
    post.regs
      = state.regs.insert Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_nil,
    write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-! ## The step's effect on the register file, uniformly over the 63 arms

`stepChannelOutput_busEffect_ok` collapses the arms to five bus shapes; these two theorems read the
register effect off each. Together they say exactly what `stepRegWrite` claims: a step writes the
register its write entry names, and leaves every other one alone. -/

private lemma reg_of_fin_neq_pc (r : Fin 32) : reg_of_fin r ≠ Register.PC := by
  fin_cases r <;> simp [reg_of_fin]

/-- **`reg_of_fin` separates the general registers — but only away from `0`.**

    Its last `match` arm is a catch-all returning `x31`, and the explicit arms stop at `30`, so
    index `0` and index `31` both land on `Register.x31`. That collision is harmless here because
    `bus_effect` never writes a register whose index wraps to `0`, and `RegAgree` is stated off
    zero for the same reason — but it is a live trap for anyone who assumes plain injectivity. -/
private lemma reg_of_fin_injective {k₁ k₂ : Fin 32} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0)
    (h : reg_of_fin k₁ = reg_of_fin k₂) : k₁ = k₂ := by
  revert h₁ h₂ h
  revert k₁ k₂
  decide

/-- The `x0` branch of the three-entry write shape: `bus_effect` skips a write whose target index
    wraps to `0`, so the register map only picks up `nextPC`. -/
private lemma post_eq_of_busEffect_ok_three_x0
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
    (h_z : Transpiler.wrap_to_regidx e2.ptr = 0)
    (h_ok : (bus_effect execRows [e0, e1, e2] state).2 = .ok result post) :
    post.regs
      = state.regs.insert Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_two_ne_neg_one : ((2 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  rcases h_a1 with h_a1 | h_a1 <;>
    · simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
        h_m0, h_m1, h_m2, h_a0, h_a1, h_a2, h_one_ne, h_one_val, as_two_val, as_two_ne_one,
        h_two_ne_neg_one, if_false, if_true, dif_pos h_z,
        write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
      cases h_ok
      rfl

/-- The `x0` branch of the single-entry shape. -/
private lemma post_eq_of_busEffect_ok_one_x0
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e : Interaction.MemoryBusEntry FGL)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_ex0 : execRows[0]!.multiplicity = -1)
    (h_ex1 : execRows[1]!.multiplicity = 1)
    (h_m : e.multiplicity = 1) (h_a : e.as = 1)
    (h_z : Transpiler.wrap_to_regidx e.ptr = 0)
    (h_ok : (bus_effect execRows [e] state).2 = .ok result post) :
    post.regs
      = state.regs.insert Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m, h_a, h_one_ne, h_one_val, if_false, if_true, dif_pos h_z,
    write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- **Every arm's memory bus is one of three shapes**, with literal multiplicities and address
    spaces. This is `stepChannelOutput_busEffect_ok`'s companion: that theorem needs the shapes to
    rule out `bus_effect`'s error exits, this one needs them to read off the register write.

    The `as` disjunctions are where stores and loads differ from the ALU arms: a store's third
    entry rides at `2` and writes memory, a load's second entry rides at `2` and reads it. -/
theorem stepChannelOutput_memRows_shape
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) :
    (stepChannelOutput i zs rd).memRows = []
      ∨ (∃ e, (stepChannelOutput i zs rd).memRows = [e]
            ∧ e.multiplicity = 1 ∧ e.as = 1)
      ∨ (∃ e0 e1 e2, (stepChannelOutput i zs rd).memRows = [e0, e1, e2]
            ∧ e0.multiplicity = -1 ∧ e0.as = 1
            ∧ e1.multiplicity = -1 ∧ e2.multiplicity = 1
            ∧ ((e1.as = 1 ∧ e2.as = 1) ∨ (e1.as = 1 ∧ e2.as = 2)
                ∨ (e1.as = 2 ∧ e2.as = 1))) := by
  cases zs <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩)
      | exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
      | exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)

/-- **The whole register effect of one step, in one equation.** Whatever the arm, the post-state's
    register map is the pre-state's with at most the step's write entry applied, and then `nextPC`.

    Stating it once, rather than as a write theorem plus a preservation theorem, is what keeps
    `RegAgree`'s inductive step free of per-shape case work: the step reads both directions off
    this. The `nextPC` value is existentially quantified because nothing about it is needed here —
    that is the PC arm's business, and `RegAgree` is stated away from `PC` and `nextPC`. -/
theorem post_regs_eq_of_stepChannelOutput
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs)
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_ok : (bus_effect (stepChannelOutput i zs rd).execRows
      (stepChannelOutput i zs rd).memRows state).2 = .ok result post) :
    ∃ v : RegisterType Register.nextPC,
      post.regs
        = (match stepRegWrite (stepChannelOutput i zs rd) with
            | some e =>
                if Transpiler.wrap_to_regidx e.ptr = 0 then state.regs
                else state.regs.insert (reg_of_fin (Transpiler.wrap_to_regidx e.ptr))
                    (cast (by rw [register_type_reg_of_fin_equiv]) (entryRegValue e))
            | none => state.regs).insert Register.nextPC v := by
  have hx := stepChannelOutput_execRows i zs rd
  have h_len : (stepChannelOutput i zs rd).execRows.length = 2 := by rw [hx]; rfl
  have h_ex0 : (stepChannelOutput i zs rd).execRows[0]!.multiplicity = -1 := by rw [hx]; rfl
  have h_ex1 : (stepChannelOutput i zs rd).execRows[1]!.multiplicity = 1 := by rw [hx]; rfl
  refine ⟨register_type_pc_equiv ▸
    (BitVec.ofNat 64 ((stepChannelOutput i zs rd).execRows[1]!.pc).val), ?_⟩
  rcases stepChannelOutput_memRows_shape i zs rd with
    h_shape | ⟨e, h_shape, h_m, h_a⟩ | ⟨e0, e1, e2, h_shape, h_m0, h_a0, h_m1, h_m2, h_as⟩
  · rw [h_shape] at h_ok
    rw [post_eq_of_busEffect_ok_nil _ _ _ _ h_len h_ex0 h_ex1 h_ok]
    simp [stepRegWrite, h_shape]
  · rw [h_shape] at h_ok
    by_cases h_z : Transpiler.wrap_to_regidx e.ptr = 0
    · rw [post_eq_of_busEffect_ok_one_x0 _ _ _ _ _ h_len h_ex0 h_ex1 h_m h_a h_z h_ok]
      simp [stepRegWrite, h_shape, h_a, h_z]
    · rw [post_eq_of_busEffect_ok_one _ _ _ _ _ h_len h_ex0 h_ex1 h_m h_a h_z h_ok]
      simp [stepRegWrite, h_shape, h_a, h_z]
  · rw [h_shape] at h_ok
    rcases h_as with ⟨h_a1, h_a2⟩ | ⟨h_a1, h_a2⟩ | ⟨h_a1, h_a2⟩
    · by_cases h_z : Transpiler.wrap_to_regidx e2.ptr = 0
      · rw [post_eq_of_busEffect_ok_three_x0 _ _ _ _ _ _ _ h_len h_ex0 h_ex1 h_m0 h_a0 h_m1
          (Or.inl h_a1) h_m2 h_a2 h_z h_ok]
        simp [stepRegWrite, h_shape, h_a2, h_z]
      · rw [post_eq_of_busEffect_ok_three_write _ _ _ _ _ _ _ h_len h_ex0 h_ex1 h_m0 h_a0 h_m1
          h_a1 h_m2 h_a2 h_z h_ok]
        simp [stepRegWrite, h_shape, h_a2, h_z]
    · rw [post_eq_of_busEffect_ok_three_store _ _ _ _ _ _ _ h_len h_ex0 h_ex1 h_m0 h_a0 h_m1
        h_a1 h_m2 h_a2 h_ok]
      simp [stepRegWrite, h_shape, h_a2]
    · by_cases h_z : Transpiler.wrap_to_regidx e2.ptr = 0
      · rw [post_eq_of_busEffect_ok_three_x0 _ _ _ _ _ _ _ h_len h_ex0 h_ex1 h_m0 h_a0 h_m1
          (Or.inr h_a1) h_m2 h_a2 h_z h_ok]
        simp [stepRegWrite, h_shape, h_a2, h_z]
      · rw [post_eq_of_busEffect_ok_three_load _ _ _ _ _ _ _ h_len h_ex0 h_ex1 h_m0 h_a0 h_m1
          h_a1 h_m2 h_a2 h_z h_ok]
        simp [stepRegWrite, h_shape, h_a2, h_z]

/-! ## The inductive step

With the register effect in hand the step is short, and — this is the point of #343 — it needs the
trace to be *chained*. On a bare `Fin n → SequentialState` there is no equation relating step
`j + 1` to step `j`'s post-state, so `RegAgree j → RegAgree (j + 1)` could not even be stated
without assuming one, which is the swap the anti-laundering rule forbids. -/

/-- **Writeback preservation.** If the register files agree before a step, they agree after it.

    Sail's side: the post-state's registers are the pre-state's with the write entry applied
    (`post_regs_eq_of_stepChannelOutput`), and retire moves only `PC`
    (`chainedSailStates_regs_of_ne_pc`). ZisK's side: `ziskRegFile` applies the same entry, by
    construction. So the two updates are the same update. -/
theorem regAgree_succ
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (rowDecode : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (j : ℕ) (h : j < ziskTrace.numInstructions)
    (h_sound : StepSound ziskTrace (chainedSailTrace ziskStep init) ⟨j, h⟩ (ziskStep ⟨j, h⟩)
      (rowDecode ⟨j, h⟩))
    (h_prev : RegAgree ziskStep rowDecode init j) :
    RegAgree ziskStep rowDecode init (j + 1) := by
  intro k h_k
  obtain ⟨result, post, h_ok⟩ :=
    stepChannelOutput_busEffect_ok (⟨j, h⟩ : Fin ziskTrace.numInstructions) (ziskStep ⟨j, h⟩)
      (rowDecode ⟨j, h⟩) (chainedSailStates ziskStep init j)
  have h_exec : execute_instruction (sailInstructionOf ⟨j, h⟩ (ziskStep ⟨j, h⟩))
      (chainedSailStates ziskStep init j) = .ok result post :=
    ((stepSound_iff ⟨j, h⟩ (ziskStep ⟨j, h⟩) (rowDecode ⟨j, h⟩)).mp h_sound).trans h_ok
  have h_post : sailStepPost (sailInstructionOf ⟨j, h⟩ (ziskStep ⟨j, h⟩))
      (chainedSailStates ziskStep init j) = post := by
    rw [sailStepPost, h_exec]
  have h_regs : (chainedSailStates ziskStep init (j + 1)).regs.get? (reg_of_fin k)
      = post.regs.get? (reg_of_fin k) := by
    rw [chainedSailStates_regs_of_ne_pc ziskStep init j h (reg_of_fin k) (reg_of_fin_neq_pc k),
      h_post]
  obtain ⟨v, h_post_regs⟩ :=
    post_regs_eq_of_stepChannelOutput ⟨j, h⟩ (ziskStep ⟨j, h⟩) (rowDecode ⟨j, h⟩)
      (chainedSailStates ziskStep init j) post result h_ok
  rw [h_regs, h_post_regs, ziskRegFile, dif_pos h]
  have h_nextPC : reg_of_fin k ≠ Register.nextPC := reg_of_fin_neq_nextPC
  rw [Std.ExtDHashMap.get?_insert,
    dif_neg (by simp only [beq_iff_eq, ne_eq]; exact Ne.symm h_nextPC)]
  cases h_w : stepRegWrite (stepChannelOutput (⟨j, h⟩ : Fin ziskTrace.numInstructions)
      (ziskStep ⟨j, h⟩) (rowDecode ⟨j, h⟩)) with
  | none => exact h_prev k h_k
  | some e =>
      by_cases h_eq : Transpiler.wrap_to_regidx e.ptr = k
      · have h_nz : Transpiler.wrap_to_regidx e.ptr ≠ 0 := by rw [h_eq]; exact h_k
        subst h_eq
        dsimp only
        rw [if_neg h_nz, if_pos rfl, Std.ExtDHashMap.get?_insert,
          dif_pos (by simp only [beq_self_eq_true])]
        simp
      · by_cases h_z : Transpiler.wrap_to_regidx e.ptr = 0
        · dsimp only
          rw [if_pos h_z, if_neg h_eq]
          exact h_prev k h_k
        · have h_ne : reg_of_fin (Transpiler.wrap_to_regidx e.ptr) ≠ reg_of_fin k := fun hc =>
            h_eq (reg_of_fin_injective h_z h_k hc)
          dsimp only
          rw [if_neg h_z, if_neg h_eq, Std.ExtDHashMap.get?_insert,
            dif_neg (by simp only [beq_iff_eq, ne_eq]; exact h_ne)]
          exact h_prev k h_k

end ZiskFv.Compliance
