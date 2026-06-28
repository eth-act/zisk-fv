import ZiskFv.Compliance.Pilot.SubNextPC

/-!
# Branch next-PC discharge mechanism (#100 / #101, conditional branches)

The shared `Air.Flat`-transition mechanism for the six RV64I conditional
branches (BEQ, BNE, BLT, BGE, BLTU, BGEU). Like its siblings
`sequential_nextPC_discharged` / `flag_path_nextPC_discharged` /
`setpc_path_nextPC_discharged` in `SubNextPC.lean`, this derives the
producer entry's committed next-row PC from the accepted trace's
in-circuit `pcHandshakeBetween` transition certificate
(`mainTransition_to_next_pc`) composed with the within-segment
fixed-column fact (`segment_l1_succ`) — NOT a caller-supplied promise.

A branch row sets `set_pc = 0`, so the Main PC handshake collapses
(via `pc_handshake_branch`) to the **flag-dispatched** mux

```
next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)
```

with `flag` the Binary-SM comparison output surfaced on the operation
bus (see `ZiskFv/Airs/OperationBus/OperationBus.lean::opBus_row_Binary`'s
`flag := carry_7` and `matches_entry`'s `a.flag = b.flag` clause). The
per-branch caller (`stepStrong_<branch>`) then substitutes the derived
`flag = (cmp ? 1 : 0)` (from `binary_{lt,ltu,eq}_chunks_eq_bv_*_of_wf`)
and the `jmp_offset{1,2}` decode/offset bridges, and casts the field
sum to the Sail conditional next-PC `if cmp then PC + signExtend imm
else PC + 4`.

This lemma supplies only the **mechanism** half (transition certificate
→ the field-level branch mux through the PC cast); deriving `flag` and
the offset bridges is the substantive per-branch piece. Kernel-only,
like its siblings. -/

namespace ZiskFv.Compliance.Pilot

open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Airs.Main (pc_handshake_branch)
open Interaction

/-- **General BRANCH-PATH next-PC discharge (#100/#101).** For a branch
    row (`set_pc = 0`), the `execRowOf`-family producer entry's `pc` is
    the committed next-row column, which the accepted trace's in-circuit
    `pcHandshakeBetween` transition certificate
    (`mainTransition_to_next_pc`) composed with the within-segment
    fixed-column fact (`segment_l1_succ`) and the `set_pc = 0` branch
    decode pin equates — via `pc_handshake_branch` — to the field-level
    flag-dispatched mux value

    `pc i + jmp_offset2 i + flag i * (jmp_offset1 i - jmp_offset2 i)`.

    The conclusion is left at the field level (cast through
    `register_type_pc_equiv`); the per-branch caller substitutes the
    derived `flag` value and the `jmp_offset{1,2}` bridges, then casts to
    the Sail conditional next-PC. -/
theorem branch_path_nextPC_field
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64
          ((execRowOf trace i)[1]!.pc).val))
      = BitVec.ofNat 64
          (((mainOfTable trace.program trace.mainTable).pc i.val
            + (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val
            + (mainOfTable trace.program trace.mainTable).flag i.val
              * ((mainOfTable trace.program trace.mainTable).jmp_offset1 i.val
                - (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val)).val) := by
  -- (1) The producer entry's pc is the committed next-row pc column (structural).
  have h_pc1 :
      (execRowOf trace i)[1]!.pc
        = (mainOfTable trace.program trace.mainTable).pc (i.val + 1) := rfl
  -- (2) Transition certificate + within-segment fixed-column fact.
  have h_seg := trace.mainTable_fixed.segment_l1_succ i.val h_idx
  have h_hand :=
    ZiskFv.Compliance.AcceptedZiskTrace.mainTransition_to_next_pc trace i.val h_idx h_seg
  -- (3) The branch decode pin (`set_pc = 0`) collapses the mux to the
  --     flag-dispatched value (via `pc_handshake_branch`).
  have h_step :
      (mainOfTable trace.program trace.mainTable).pc (i.val + 1)
        = (mainOfTable trace.program trace.mainTable).pc i.val
          + (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val
          + (mainOfTable trace.program trace.mainTable).flag i.val
            * ((mainOfTable trace.program trace.mainTable).jmp_offset1 i.val
              - (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val) :=
    pc_handshake_branch (mainOfTable trace.program trace.mainTable) i.val
      ((mainOfTable trace.program trace.mainTable).pc (i.val + 1)) h_set_pc h_hand
  -- (4) Substitute; the `register_type_pc_equiv ▸ …` cast is defeq-identity.
  rw [h_pc1, h_step]

/-- **Conditional next-PC cast — taken-on-`flag=1` polarity (BLTU / BLT / BEQ).**
    Specializes `branch_path_nextPC_field` to the polarity where the Sail-taken
    branch corresponds to `flag = 1`: the row pins `jmp_offset2 = 4` (the
    `flag = 0` / fall-through side) and carries the taken offset on
    `jmp_offset1` (bridged to `offset_bv`). Substituting the derived
    `flag = (if cmp then 1 else 0)` keystone (`cmp` the Binary-SM comparison)
    and casting through the wide-PC no-wrap bounds yields the Sail conditional
    next-PC `if cmp then PC + offset_bv else PC + 4#64`. -/
theorem branch_nextPC_flag1_taken
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (cmp : Bool) (PC offset_bv : BitVec 64)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0)
    (h_flag :
      (mainOfTable trace.program trace.mainTable).flag i.val
        = if cmp then 1 else 0)
    (h_jmp2 :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4)
    (h_off_bridge :
      ((mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val
        = offset_bv.toNat)
    (h_pc_bridge :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val = PC.toNat)
    (h_no_wrap :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val
        + ((mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val
        < GL_prime)
    (h_pc_bound : PC.toNat < 18446744069414584321 - 4) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((execRowOf trace i)[1]!.pc).val))
      = (if cmp then PC + offset_bv else PC + 4#64) := by
  rw [branch_path_nextPC_field trace i h_idx h_set_pc, h_jmp2, h_flag]
  set pc := (mainOfTable trace.program trace.mainTable).pc i.val with hpc
  set j1 := (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val with hj1
  cases cmp with
  | true =>
    simp only [reduceIte]
    rw [show (pc + 4 + (1 : FGL) * (j1 - 4)) = pc + j1 from by ring]
    exact ofNat_fgl_pc_plus_offset_eq pc j1 PC offset_bv h_pc_bridge h_off_bridge h_no_wrap
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [show (pc + 4 + (0 : FGL) * (j1 - 4)) = pc + 4 from by ring]
    exact ofNat_fgl_pc_plus_4_eq pc PC h_pc_bridge h_pc_bound

/-- **Conditional next-PC cast — taken-on-`flag=0` polarity (BGEU / BGE / BNE).**
    Mirror of `branch_nextPC_flag1_taken` for the `create_branch_op`-`neg`
    polarity: the row pins `jmp_offset1 = 4` (the `flag = 1` / fall-through
    side) and carries the taken offset on `jmp_offset2`. Substituting the
    derived `flag = (if cmp then 1 else 0)` keystone yields
    `if cmp then PC + 4#64 else PC + offset_bv`; the per-branch caller bridges
    the `cmp ↔ ¬taken` polarity on the Sail side. -/
theorem branch_nextPC_flag0_taken
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (cmp : Bool) (PC offset_bv : BitVec 64)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0)
    (h_flag :
      (mainOfTable trace.program trace.mainTable).flag i.val
        = if cmp then 1 else 0)
    (h_jmp1 :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4)
    (h_off_bridge :
      ((mainOfTable trace.program trace.mainTable).jmp_offset2 i.val).val
        = offset_bv.toNat)
    (h_pc_bridge :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val = PC.toNat)
    (h_no_wrap :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val
        + ((mainOfTable trace.program trace.mainTable).jmp_offset2 i.val).val
        < GL_prime)
    (h_pc_bound : PC.toNat < 18446744069414584321 - 4) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((execRowOf trace i)[1]!.pc).val))
      = (if cmp then PC + 4#64 else PC + offset_bv) := by
  rw [branch_path_nextPC_field trace i h_idx h_set_pc, h_jmp1, h_flag]
  set pc := (mainOfTable trace.program trace.mainTable).pc i.val with hpc
  set j2 := (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val with hj2
  cases cmp with
  | true =>
    simp only [reduceIte]
    rw [show (pc + j2 + (1 : FGL) * (4 - j2)) = pc + 4 from by ring]
    exact ofNat_fgl_pc_plus_4_eq pc PC h_pc_bridge h_pc_bound
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [show (pc + j2 + (0 : FGL) * (4 - j2)) = pc + j2 from by ring]
    exact ofNat_fgl_pc_plus_offset_eq pc j2 PC offset_bv h_pc_bridge h_off_bridge h_no_wrap

end ZiskFv.Compliance.Pilot
