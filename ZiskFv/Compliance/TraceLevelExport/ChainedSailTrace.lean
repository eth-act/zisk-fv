import ZiskFv.Compliance.TraceLevelExport.SailRetireChain

/-!
# A `SailTrace` that Sail's own semantics generates — #343

`SailTrace n` is `Fin n → PreSail.SequentialState`: a *family* of states with no relation between
indices. Because nothing links step `j` to step `j + 1`, every cross-step law has to be **assumed**.
`SegmentPcChain` assumes `retire`, and `SailRetireChain.lean:789` says what that costs — Phase 7 is
a restructure, not a logical-strength reduction. #330 Phase 4 hits the same wall: `RegAgree`'s
inductive step has nothing to stand on.

This module builds the trace instead of assuming it. `chainedSailStates` runs
`execute_instruction` at each step from an initial state and then performs Sail's **retire**: copy
`nextPC` into `PC`. `chainedSailStates_retire` is then true **by construction**, not by hypothesis.

## What this does and does not settle

It settles the shape: a trace generated this way satisfies `retire` definitionally, so a caller that
supplies one is supplying an actual Sail execution rather than an arbitrary family of states with a
promise attached. `root_soundness` consumes it — that theorem takes an initial state, builds the
trace here, and no longer carries a `SegmentPcChain` binder.

`stepSound_of_programDecodes` still takes an arbitrary `SailTrace`, so the five multi-step
accepted-trace witnesses keep their hand-built state families.

**Nothing below is exercised by a checked-in witness yet — say so plainly.** The two witnesses that
instantiate `root_soundness` run at `numInstructions = 1` and `0`. `chainedSailStates … 0` is `init`
by `rfl`, so index `0` is the caller's own state and no witness reaches index `≥ 1`. `retirePC` and
`sailStepPost` are therefore never applied in the checked-in tree, and
`chainedSailTrace_retireChain` is proved but never *used* by a witness. The premise reduction on
`root_soundness` is real regardless — it is a statement-level fact — but the claim that the trace is
"harder to inhabit" is not yet demonstrated by an instantiation that has to run Sail.
-/

namespace ZiskFv.Compliance

variable {numInstructions : ℕ}

/-- **Sail's retire step, as a state function.** Copy `nextPC` into `PC`. This is the transition the
    old `SegmentPcChain.retire` field asserted; here it is performed.

    **The `none` branch erases `PC`, and that is a coverage cliff, not a soundness hole.** Erasing
    makes both sides of `retire` equal to `none`, which is what lets `chainedSailTrace_retireChain`
    hold with no side condition — the alternative needs a fact about all 63 `execute` arms. The cost
    is that a step which leaves `nextPC` unset produces a state with no `PC` at all, and every
    `Inputs_<op>`'s `h_input_pc` demands `.some`. So such a step makes `inputsAgree` *unsatisfiable*
    from there on: the theorem becomes uninstantiable rather than silently matching `.elim 0`'s
    zero. Nothing is proved about a state that never arises; a real trace is simply lost. -/
noncomputable def retirePC
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  match s.regs.get? Register.nextPC with
  | none => { s with regs := s.regs.erase Register.PC }
  | some v =>
      { s with regs := s.regs.insert Register.PC (cast (by simp [RegisterType]) v) }

/-- The post-state of one Sail step.

    **Both branches return `post`**, the state the step ended in — including the error branch, where
    `post` is the trap's post-state, not the pre-state. So a trapping step advances the chain from
    wherever Sail left it. That is what makes this total, and it is the honest reading: the retire
    law says nothing about a trapping step because `chainedSailTrace_retireChain`'s hypothesis is an
    `.ok`. An earlier docstring here claimed the error branch "stays put"; it does not. -/
noncomputable def sailStepPost
    (instr : instruction)
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  match execute_instruction instr s with
  | .ok _ post => post
  | .error _ post => post


/-- **The trace Sail's semantics generates.** Step `0` is the given initial state; step `j + 1` is
    the post-state of executing step `j`'s instruction, followed by Sail's retire — copy `nextPC`
    into `PC`.

    Out-of-range indices stay put, which keeps the recursion total without affecting any index the
    trace is used at. -/
noncomputable def chainedSailStates
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    ℕ → PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  | 0 => init
  | j + 1 =>
      if h : j < ziskTrace.numInstructions then
        retirePC (sailStepPost (sailInstructionOf ⟨j, h⟩ (ziskStep ⟨j, h⟩))
          (chainedSailStates ziskStep init j))
      else
        chainedSailStates ziskStep init j

/-- The chained states, packaged as a `SailTrace`. -/
noncomputable def chainedSailTrace
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    SailTrace ziskTrace.numInstructions :=
  fun i => chainedSailStates ziskStep init i.val

@[simp] theorem chainedSailStates_zero
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    chainedSailStates ziskStep init 0 = init := rfl

@[simp] theorem chainedSailTrace_apply
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin ziskTrace.numInstructions) :
    chainedSailTrace ziskStep init i = chainedSailStates ziskStep init i.val := rfl

/-- **`retire` holds by construction.** For a chained trace the PC at step `j + 1` *is* the `nextPC`
    the step at `j` wrote, because `chainedSailStates` performs the copy rather than assuming it.

    This is the whole point of #343. `SegmentPcChain.retire` is a hypothesis precisely because
    `SailTrace` is an arbitrary family of states; on a trace Sail actually generated there is nothing
    left to assume. -/
theorem chainedSailStates_retire
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (j : ℕ) (h : j < ziskTrace.numInstructions)
    (v : RegisterType Register.nextPC)
    (h_next : (sailStepPost (sailInstructionOf ⟨j, h⟩ (ziskStep ⟨j, h⟩))
        (chainedSailStates ziskStep init j)).regs.get? Register.nextPC = some v) :
    (chainedSailStates ziskStep init (j + 1)).regs.get? Register.PC
      = some (cast (by simp [RegisterType]) v) := by
  rw [chainedSailStates, dif_pos h, retirePC]
  rw [h_next]
  simp [Std.ExtDHashMap.get?_insert]


/-! ## Why this unblocks `RegAgree`

The retire step touches `PC` and nothing else. So on a chained trace the *general* registers at step
`j + 1` are exactly the post-state's — which is what `RegisterWriteback.lean`'s
`regs_write_of_busEffect_ok_three` and `regs_preserved_of_busEffect_ok_three` describe.

That is the link `RegAgree j → RegAgree (j + 1)` was missing. On a bare `Fin n → State` there is no
such equation to state, let alone prove. -/

/-- **Retire moves `PC` and leaves every other register alone.** -/
theorem retirePC_regs_of_ne
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r : Register) (h_r : r ≠ Register.PC) :
    (retirePC s).regs.get? r = s.regs.get? r := by
  rw [retirePC]
  cases h_next : s.regs.get? Register.nextPC with
  | none => simp [Std.ExtDHashMap.get?_erase, h_r.symm]
  | some v => simp [Std.ExtDHashMap.get?_insert, h_r.symm]

/-- **The general registers at step `j + 1` are the post-state's.**

    This is the equation `RegAgree`'s inductive step needs, and the equation a bare
    `Fin n → SequentialState` cannot even state. Compose it with
    `regs_write_of_busEffect_ok_three` (the destination register takes the write entry's lanes) and
    `regs_preserved_of_busEffect_ok_three` (every other register is untouched), and the Sail side of
    the step is complete; #330 Phase 4's `exists_bootAnchored` supplies the ZisK side. -/
theorem chainedSailStates_regs_of_ne_pc
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (j : ℕ) (h : j < ziskTrace.numInstructions)
    (r : Register) (h_r : r ≠ Register.PC) :
    (chainedSailStates ziskStep init (j + 1)).regs.get? r
      = (sailStepPost (sailInstructionOf ⟨j, h⟩ (ziskStep ⟨j, h⟩))
          (chainedSailStates ziskStep init j)).regs.get? r := by
  rw [chainedSailStates, dif_pos h]
  exact retirePC_regs_of_ne _ r h_r


/-! ## The decisive consequence: `retire` stops being a premise

`SailRetireChain.retire` is the per-step law `SegmentPcChain` assumes. On a chained trace it is a
theorem. A caller that supplies an initial state instead of a `SailTrace` therefore owes one premise
fewer — and this is what makes the PC arm a *reduction* rather than a restructure. -/

/-- **`SailRetireChain` holds for a chained trace.** No hypothesis: the trace performs the retire. -/
theorem chainedSailTrace_retireChain
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    SailRetireChain ziskTrace (chainedSailTrace ziskStep init) ziskStep := by
  constructor
  intro j h result post h_step
  have h_post : sailStepPost (sailInstructionOf ⟨j, Nat.lt_of_succ_lt h⟩
      (ziskStep ⟨j, Nat.lt_of_succ_lt h⟩)) (chainedSailStates ziskStep init j) = post := by
    rw [sailStepPost]
    rw [show execute_instruction (sailInstructionOf ⟨j, Nat.lt_of_succ_lt h⟩
      (ziskStep ⟨j, Nat.lt_of_succ_lt h⟩)) (chainedSailStates ziskStep init j)
        = .ok result post from h_step]
  show (chainedSailStates ziskStep init (j + 1)).regs.get? Register.PC
    = post.regs.get? Register.nextPC
  rw [chainedSailStates, dif_pos (Nat.lt_of_succ_lt h), h_post, retirePC]
  cases h_next : post.regs.get? Register.nextPC with
  | none => simp [Std.ExtDHashMap.get?_erase, h_next]
  | some v => simp [Std.ExtDHashMap.get?_insert]

end ZiskFv.Compliance
