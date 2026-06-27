import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.MainTransition

/-!
# Pilot next-PC discharge for SUB (#100 Phase 3)

This is the end-to-end pilot milestone for issue #100: it **discharges** SUB's
`h_nextPC_matches` residual — the control-flow next-PC promise the construction
otherwise carries as a caller-supplied binder — from the new Main transition
mechanism (`AcceptedZiskTrace.mainTransition_to_next_pc`, the in-circuit
`pcHandshakeBetween` certificate) composed with a **trace-derived** execution-bus
row (`execRowOf`).

The construction-chosen bus `busSub trace i execRow` sets `exec_row := execRow`
verbatim, so pinning `execRow := execRowOf trace i` — whose producer entry's `pc`
reads the *committed* Main `pc` column at the next row `i+1` — lets us replace the
opaque `exec_row[1]!.pc` with `(mainOfTable …).pc (i+1)`, which the transition
certificate equates to the current row's mux. With the SUB/R-type decode pins
(`set_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`) the mux collapses to `pc i + 4`,
and the wide-PC no-wrap cast (mirroring `WidePCNoWrap`) lifts the field-level
`pc i + 4` to the Sail `PC + 4#64`.

## Justification of the residual hypotheses (none is a smuggled discharge)

* `h_idx : i + 1 < mainTable.length` — the one honest structural side condition
  ("the next Main row exists"); needed for the cross-row transition to apply at
  the pair `(i, i+1)`. The caller derives it from `mainTable_index` for any
  non-terminal row (`i + 1 < numInstructions`); the terminal row is the
  cross-segment boundary (#103, out of scope).
  The `SEGMENT_L1 = [1,0,…]` fixed-column fact (`main.pil:19`) is **no longer a
  binder** — it is read off the accepted trace's shared `segment_l1_fixed`
  certificate via `trace.mainTable_fixed` (a `main_height`-class once-for-all
  obligation), supplying `segment_l1 (i+1) = 0` (within-segment), the
  non-boundary side condition of the transition.
* `h_set_pc`, `h_jmp1`, `h_jmp2` — Main decode pins for a register-type SUB row:
  the Rust lowerer's R-type arm `create_register_op(…, "sub", 4)` calls
  `zib.j(4, 4)` (⇒ `jmp_offset1 = jmp_offset2 = 4`) and never `set_pc()`
  (⇒ `set_pc = 0`); cf. `RowShape/Contract.lean` ADD/R-type arm and
  `main.pil:150-152`. These describe **row `i`** (the decoded instruction),
  NOT the thing being discharged (the next-row `pc`).
* `h_pc_bridge : ((mainOfTable …).pc i).val = sub_input.PC.toNat` — the same
  per-op PC provenance bridge `Equivalence/Jal.lean` / `Equivalence/Auipc.lean`
  already carry (`h_pc_bridge : (m.pc r_main).val = …PC.toNat`): the committed
  Main `pc` column at the decoded row equals the Sail program counter. It binds
  the *current* row, not the next.
* `h_pc_bound : sub_input.PC.toNat < GL_prime - 4` — the JAL-style PC-trajectory
  bound (`Equivalence/Jal.lean` `h_pc_bound`) ruling out FGL wrap on `pc + 4`.

None of these asserts `exec_row[1].pc = …` or `pc (i+1) = …`; those are *derived*
from `mainTransition_to_next_pc` + the decode pins.
-/

namespace ZiskFv.Compliance.Pilot

open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Airs.Main (pc_handshake_with_next_pc pc_handshake_branch pc_handshake_jump)
open Interaction

/-- **Trace-derived execution-bus row.** The two committed execution-bus entries
    for the Main row at trace index `i`: the read entry (`multiplicity = -1`) whose
    `pc` is the *current* committed Main `pc` column `pc i`, and the write/next-PC
    entry (`multiplicity = 1`) whose `pc` is the *next-row* committed column
    `pc (i+1)`. Both `pc` cells read the real `mainOfTable` columns — never
    arbitrary values — so pinning `busSub`'s `execRow` to this row exposes the
    committed next-row `pc` to the transition certificate. Multiplicities and
    length match what `h_e0_mult = -1` / `h_e1_mult = 1` / `h_exec_len = 2`
    expect. -/
@[reducible] noncomputable def execRowOf
    (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) :
    List (Interaction.ExecutionBusEntry FGL) :=
  [ { multiplicity := -1
    , pc := (mainOfTable trace.program trace.mainTable).pc i.val
    , timestamp := 1 }
  , { multiplicity := 1
    , pc := (mainOfTable trace.program trace.mainTable).pc (i.val + 1)
    , timestamp := 1 } ]

/-- **Wide-PC `pc + 4` cast (full BitVec form).** Given the committed-`pc` ↔
    Sail-`PC` bridge and the no-wrap PC bound, the field-level `pc_fgl + 4`'s
    `BitVec.ofNat 64`-image is exactly `PC + 4#64`. This mirrors the
    `ZiskFv.PackedBitVec.WidePCNoWrap` toolkit (`fgl_pc_plus_4_lo/hi`), but
    delivers the un-split 64-bit equality the next-PC residual consumes. -/
lemma ofNat_fgl_pc_plus_4_eq
    (pc_fgl : FGL) (PC : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_pc_bound : PC.toNat < 18446744069414584321 - 4) :
    BitVec.ofNat 64 ((pc_fgl + 4).val) = PC + 4#64 := by
  have h4 : (4 : FGL).val = 4 := by decide
  have h_no_wrap : pc_fgl.val + (4 : FGL).val < GL_prime := by
    rw [h_pc_bridge, h4]; omega
  have h_fgl_val : (pc_fgl + 4 : FGL).val = pc_fgl.val + (4 : FGL).val := by
    rw [show (pc_fgl + 4 : FGL) = pc_fgl + 4 from rfl, Fin.val_add]
    exact Nat.mod_eq_of_lt h_no_wrap
  rw [h_fgl_val, h_pc_bridge, h4]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add]
  norm_num

/-- **General sequential next-PC discharge (#100).** Op-agnostic core: for ANY
    sequential (non-jump) opcode — whose Sail `nextPC = PC + 4#64` — the
    `busSub`-family producer entry's wide-PC cast equals `PC + 4#64`, derived from
    the accepted trace's in-circuit `pcHandshakeBetween` transition certificate
    (`mainTransition_to_next_pc`) composed with the within-segment fixed-column
    fact (`trace.mainTable_fixed.segment_l1_succ`) and the register-type decode
    pins (`set_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`).

    This is the SUB pilot (`sub_nextPC_discharged`) lifted to a `PC : BitVec 64`
    parameter and a bus-agnostic `PC + 4#64` conclusion.  Every busSub-family
    sequential op discharges its `h_nextPC_matches` residual by applying this
    lemma with `PC := <op>_input.PC` (the per-op Sail `nextPC = PC + 4#64` holds
    by `rfl` from the pure-spec definition, so no extra input is needed).  Inputs
    are exactly the SUB pilot's set minus the op-specific `sub_input`/`binding`. -/
theorem sequential_nextPC_discharged
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (PC : BitVec 64)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0)
    (h_jmp1 :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4)
    (h_jmp2 :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4)
    (h_pc_bridge :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val = PC.toNat)
    (h_pc_bound : PC.toNat < 18446744069414584321 - 4) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64
          ((execRowOf trace i)[1]!.pc).val))
      = PC + 4#64 := by
  -- (1) The producer entry's pc is the committed next-row pc column (structural).
  -- Stated directly over `execRowOf` (the bus constructor factored out): every
  -- exec-row bus constructor (`busSub`/`busLd`/`busSt`) sets `exec_row := execRow`
  -- as a verbatim passthrough, so `(bus … (execRowOf trace i)).exec_row[1]!.pc`
  -- is defeq to `(execRowOf trace i)[1]!.pc`. Working over the latter makes this
  -- lemma bus-CONSTRUCTOR-agnostic, reusable by loads (`busLd`) and stores
  -- (`busSt`) as well as the `busSub` family.
  have h_pc1 :
      (execRowOf trace i)[1]!.pc
        = (mainOfTable trace.program trace.mainTable).pc (i.val + 1) := rfl
  -- (2) Transition certificate + within-segment fixed-column fact.  The
  -- `SEGMENT_L1 = [1,0,…]` shape is now read off the accepted trace's shared
  -- `segment_l1_fixed` certificate (`trace.mainTable_fixed`), not a per-arm binder.
  have h_seg := trace.mainTable_fixed.segment_l1_succ i.val h_idx
  have h_hand :=
    ZiskFv.Compliance.AcceptedZiskTrace.mainTransition_to_next_pc trace i.val h_idx h_seg
  -- (3) Decode pins collapse the mux to `pc i + 4`.
  have h_step :
      (mainOfTable trace.program trace.mainTable).pc (i.val + 1)
        = (mainOfTable trace.program trace.mainTable).pc i.val + 4 := by
    have hb := pc_handshake_branch (mainOfTable trace.program trace.mainTable) i.val
      ((mainOfTable trace.program trace.mainTable).pc (i.val + 1)) h_set_pc h_hand
    rw [h_jmp1, h_jmp2] at hb
    linear_combination hb
  -- (4) Substitute and discharge the wide-PC cast.  The residual
  -- `register_type_pc_equiv ▸ (PC + 4#64) = PC + 4#64` closes by `rfl` because the
  -- cast (`RegisterType Register.PC = BitVec 64`) is defeq-identity.
  rw [h_pc1, h_step,
      ofNat_fgl_pc_plus_4_eq ((mainOfTable trace.program trace.mainTable).pc i.val)
        PC h_pc_bridge h_pc_bound]

/-- **General FLAG-PATH next-PC discharge (#100).** Sibling of
    `sequential_nextPC_discharged` for the unconditional-jump (`flag = 1`,
    `set_pc = 0`) family (AUIPC, JAL): the `execRowOf`-family producer entry's
    `pc` is the committed next-row column, which the accepted trace's in-circuit
    `pcHandshakeBetween` transition certificate (`mainTransition_to_next_pc`)
    composed with the within-segment fixed-column fact
    (`trace.mainTable_fixed.segment_l1_succ`) and the flag-path decode pins
    (`set_pc = 0`, `flag = 1`) equates to the *taken-offset* mux value
    `pc i + jmp_offset1 i` (via `pc_handshake_jump`).
    Unlike the sequential lemma, the conclusion is left at the field-level
    `pc + jmp_offset1` (cast through `register_type_pc_equiv`); the per-op caller
    then bridges `jmp_offset1` to its Sail next-PC (AUIPC: `jmp_offset1 = 4` ⇒
    `PC + 4#64` via `ofNat_fgl_pc_plus_4_eq`; JAL: `jmp_offset1 = imm` ⇒
    `PC + signExtend 64 imm` via the signed-offset cast).
    `flag = 1` is itself a genuine OP_FLAG decode fact, derivable in the caller
    from `is_external_op = 0`, `op = OP_FLAG = 0`, and the Main `internal_op0_sets_flag`
    constraint (`flag_eq_one_of_internal_op_zero`) — it is NOT a smuggled
    `pc (i+1) = …`. Kernel-only, like its sibling. -/
theorem flag_path_nextPC_discharged
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0)
    (h_flag :
      (mainOfTable trace.program trace.mainTable).flag i.val = 1) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64
          ((execRowOf trace i)[1]!.pc).val))
      = BitVec.ofNat 64
          (((mainOfTable trace.program trace.mainTable).pc i.val
            + (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val) := by
  -- (1) The producer entry's pc is the committed next-row pc column (structural).
  have h_pc1 :
      (execRowOf trace i)[1]!.pc
        = (mainOfTable trace.program trace.mainTable).pc (i.val + 1) := rfl
  -- (2) Transition certificate + within-segment fixed-column fact.
  have h_seg := trace.mainTable_fixed.segment_l1_succ i.val h_idx
  have h_hand :=
    ZiskFv.Compliance.AcceptedZiskTrace.mainTransition_to_next_pc trace i.val h_idx h_seg
  -- (3) The flag-path decode pins collapse the mux to the taken offset
  --     `pc i + jmp_offset1 i` (via `pc_handshake_jump`, `flag = 1`).
  have h_step :
      (mainOfTable trace.program trace.mainTable).pc (i.val + 1)
        = (mainOfTable trace.program trace.mainTable).pc i.val
          + (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val :=
    pc_handshake_jump (mainOfTable trace.program trace.mainTable) i.val
      ((mainOfTable trace.program trace.mainTable).pc (i.val + 1)) h_set_pc h_flag h_hand
  -- (4) Substitute; the `register_type_pc_equiv ▸ …` cast is defeq-identity.
  rw [h_pc1, h_step]

/-- **Pilot SUB next-PC discharge.** From the accepted trace's transition
    certificate (`mainTransition_to_next_pc`), the within-segment fixed-column
    fact, the SUB/R-type decode pins, and the PC provenance bridge/bound, prove
    SUB's `h_nextPC_matches` residual *for the trace-derived exec row*
    `execRowOf trace i`. No `h_nextPC_matches` (or `pc (i+1) = …`, or
    `exec_row[1].pc = …`) binder appears: the next-row PC is derived.

    Now a thin wrapper of the general `sequential_nextPC_discharged`: SUB's Sail
    `nextPC` unfolds to `sub_input.PC + 4#64` (defeq), so the general lemma's
    `PC + 4#64` conclusion *is* `(execute_RTYPE_sub_pure sub_input).nextPC`. -/
theorem sub_nextPC_discharged
    (trace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (sub_input : PureSpec.SubInput)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0)
    (h_jmp1 :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4)
    (h_jmp2 :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4)
    (h_pc_bridge :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val
        = sub_input.PC.toNat)
    (h_pc_bound : sub_input.PC.toNat < 18446744069414584321 - 4) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64
          ((busSub trace i (execRowOf trace i)).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC :=
  sequential_nextPC_discharged trace i sub_input.PC h_idx
    h_set_pc h_jmp1 h_jmp2 h_pc_bridge h_pc_bound

/-- **Bonus: SUB construction with the next-PC promise removed.** Restates the
    canonical SUB construction (`construction_sub_sound_claimed_dead`) at the
    trace-derived bus `execRow := execRowOf trace i`, with the
    `h_nextPC_matches` binder **and** the three exec-artifact binders
    (`h_exec_len`, `h_e0_mult`, `h_e1_mult`) all removed — derived internally.

    `h_nextPC_matches` is discharged by `sub_nextPC_discharged` (the circuit
    transition certificate); the exec artifacts become `rfl` because `execRowOf`
    is a concrete two-entry list with the expected multiplicities/length. The
    `execRow` ∀-binder is likewise gone (pinned to the committed columns).

    In exchange the statement takes the genuinely-lighter, independently-justified
    transition inputs: the structural next-row-exists side condition `h_idx`, the
    SUB decode pins `h_set_pc`/`h_jmp1`/`h_jmp2`, and the Jal/Auipc-style
    `h_pc_bridge`/`h_pc_bound`. The `SEGMENT_L1` fixed-column fact is no longer a
    binder here — it is read off the accepted trace's shared `segment_l1_fixed`
    certificate (`trace.mainTable_fixed`). The opaque cross-row next-PC *promise*
    is thereby replaced by a derivation from the in-circuit `pcHandshakeBetween`
    transition — a real reduction of the next-PC trust surface, not a relabel. -/
theorem construction_sub_sound'
    (trace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    -- decode pins (unchanged from the canonical construction)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_m32 :
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0)
    (h_store_pc :
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0)
    -- Sail reads + operands (unchanged)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok sub_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok sub_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some sub_input.PC)
    (h_input_rd : sub_input.rd = regidx_to_fin rd)
    -- lane bridges (unchanged)
    (h_a_lo_t :
      (mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_rd_idx :
      sub_input.rd =
        Transpiler.wrap_to_regidx (busSub trace i (execRowOf trace i)).e2.ptr)
    -- NEW transition inputs (replace the removed next-PC promise + exec artifacts)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc :
      (mainOfTable trace.program trace.mainTable).set_pc i.val = 0)
    (h_jmp1 :
      (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4)
    (h_jmp2 :
      (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4)
    (h_pc_bridge :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val
        = sub_input.PC.toNat)
    (h_pc_bound : sub_input.PC.toNat < 18446744069414584321 - 4) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) (binding i)
      = (bus_effect (busSub trace i (execRowOf trace i)).exec_row
          [ (busSub trace i (execRowOf trace i)).e0
          , (busSub trace i (execRowOf trace i)).e1
          , (busSub trace i (execRowOf trace i)).e2 ] (binding i)).2 :=
  ZiskFv.Compliance.construction_sub_sound_claimed_dead
    trace binding i sub_input r1 r2 rd
    h_main_op h_main_active h_m32 h_store_pc
    h_input_r1 h_input_r2 h_input_pc h_input_rd
    h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t
    (execRowOf trace i)
    -- exec artifacts: now `rfl` (execRowOf is a concrete two-entry list)
    rfl rfl rfl
    -- next-PC promise: discharged from the transition certificate
    (sub_nextPC_discharged trace binding i sub_input h_idx
      h_set_pc h_jmp1 h_jmp2 h_pc_bridge h_pc_bound)
    h_rd_idx

end ZiskFv.Compliance.Pilot
