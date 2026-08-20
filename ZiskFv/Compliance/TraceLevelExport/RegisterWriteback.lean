import ZiskFv.Compliance.TraceLevelExport.SailRetireChain

/-!
# The Sail-side register writeback — #330 Phase 4 groundwork

The four operand-lane fields were 116 assumed occurrences across the 63
`Inputs_<op>` structures, each asserting that a ZisK operand column equals a Sail register value.
Phase 4 aims to derive them instead of assuming them.

## Where those fields actually live, measured

`bus_effect` returns a `Prop × EStateM.Result`. Its **`.1`** accumulates, for every memory entry
with `multiplicity = -1` and `as = 1`, exactly

```
read_xreg (wrap_to_regidx entry.ptr) state = .ok (U64.toBV #v[byteAt entry 0, …]) state
```

— which is `h_a_lo` / `h_a_hi` in the byte-lane representation. But
`state_effect_via_channels` is `(bus_effect …).2`, so `StepSound` compares only the post-state and
**discards `.1` entirely**. That is the structural reason the register fields are assumed rather
than checked: nothing in the export ever looks at the read conditions.

So Phase 4 cannot recover them from `StepSound`. It needs two independent halves:

* **ZisK side (Phase 3).** The operand column at step `j` equals the ZisK register file cell for
  `rs1` / `rs2`, from the register MemBus telescope anchored at `RegisterBoundary.bootMessage`.
  That is gated on `pulledIf` / `pushedIf` and the Clean repoint.
* **Cross-machine side.** `RegAgree` by induction, in the strong induction Phase 7 already
  installed in `stepSound_of_programDecodes`: a boot premise at step `0`, and writeback
  preservation at each step.

This module proves the Sail half of that writeback step, and nothing else. It is deliberately
independent of Phase 3 so it can be checked on its own.

## What is proved here

`regs_of_busEffect_ok` reads the whole post-state register file off a successful channel effect:
the c-side entry's register takes the entry's byte lanes, `nextPC` takes the producer entry's `pc`,
and **every other register is unchanged**. Together with the Phase 3 telescope that is exactly the
preservation step `RegAgree` needs.

The proof is the same shape as `nextPC_of_busEffect_ok`: the `.ok` hypothesis rules out the error
branches, so the memory fold is computed rather than inspected. It is opcode-uniform — nothing here
mentions an opcode, a Main row, or a decode.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

variable {numInstructions : ℕ}

/-- The tactic prefix shared by both projections: the `.ok` hypothesis rules out `bus_effect`'s
    error branches, so the three-entry memory fold computes to a pair of register inserts. -/
private lemma post_eq_of_busEffect_ok_three
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
            (cast (by rw [register_type_reg_of_fin_equiv])
              (U64.toBV
                #v[Channels.MemoryBusBytes.byteAt e2 0, Channels.MemoryBusBytes.byteAt e2 1,
                  Channels.MemoryBusBytes.byteAt e2 2, Channels.MemoryBusBytes.byteAt e2 3,
                  Channels.MemoryBusBytes.byteAt e2 4, Channels.MemoryBusBytes.byteAt e2 5,
                  Channels.MemoryBusBytes.byteAt e2 6,
                  Channels.MemoryBusBytes.byteAt e2 7]))).insert
          Register.nextPC
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect at h_ok
  simp only [h_len, h_ex0, h_ex1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m0, h_m1, h_m2, h_a0, h_a1, h_a2, h_one_ne, h_one_val, if_false, if_true,
    dif_neg h_nz, write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map] at h_ok
  cases h_ok
  rfl

/-- **The channel effect touches exactly two registers.** Every register other than the c-side
    write target and `nextPC` comes through unchanged.

    This is the preservation half of `RegAgree`: if the ZisK register file and Sail's `xreg` agree
    before a step, they still agree afterwards at every register the step does not write. -/
theorem regs_preserved_of_busEffect_ok_three
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
    (h_ok : (bus_effect execRows [e0, e1, e2] state).2 = .ok result post)
    (r : Register)
    (h_r_nextPC : r ≠ Register.nextPC)
    (h_r_write : r ≠ reg_of_fin (Transpiler.wrap_to_regidx e2.ptr)) :
    post.regs.get? r = state.regs.get? r := by
  rw [post_eq_of_busEffect_ok_three execRows e0 e1 e2 state post result h_len h_ex0 h_ex1
    h_m0 h_a0 h_m1 h_a1 h_m2 h_a2 h_nz h_ok]
  simp [Std.ExtDHashMap.get?_insert, h_r_nextPC.symm, h_r_write.symm]

/-- **The c-side write landed.** The step's destination register holds exactly the byte lanes the
    memory-bus write entry carried.

    This is the update half of `RegAgree`. Phase 3 supplies the matching ZisK-side fact — that the
    register file's new cell for the same `cMemMessage` holds the same lanes — and the two compose
    into the inductive step. -/
theorem regs_write_of_busEffect_ok_three
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
    post.regs.get? (reg_of_fin (Transpiler.wrap_to_regidx e2.ptr))
      = some (cast (by rw [register_type_reg_of_fin_equiv])
          (U64.toBV
            #v[Channels.MemoryBusBytes.byteAt e2 0, Channels.MemoryBusBytes.byteAt e2 1,
              Channels.MemoryBusBytes.byteAt e2 2, Channels.MemoryBusBytes.byteAt e2 3,
              Channels.MemoryBusBytes.byteAt e2 4, Channels.MemoryBusBytes.byteAt e2 5,
              Channels.MemoryBusBytes.byteAt e2 6, Channels.MemoryBusBytes.byteAt e2 7])) := by
  have h_ne : reg_of_fin (Transpiler.wrap_to_regidx e2.ptr) ≠ Register.nextPC :=
    reg_of_fin_neq_nextPC
  rw [post_eq_of_busEffect_ok_three execRows e0 e1 e2 state post result h_len h_ex0 h_ex1
    h_m0 h_a0 h_m1 h_a1 h_m2 h_a2 h_nz h_ok]
  simp [Std.ExtDHashMap.get?_insert, h_ne.symm]

end ZiskFv.Compliance
