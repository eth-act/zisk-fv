import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.AirsClean.Main.Constraints

/-!
# Route C — `nextPC_matches` discharge via the #100 PC-continuation seam

This file is the **GO/NO-GO gate** for XCAP Gap (c) (the `h_nextPC_matches`
residual). It closes the SEQUENTIAL `+4` case of `h_nextPC_matches` by composing
a 3-equality chain (Route C):

1. `exec_row[1].pc = next-row pc`   — the faithful exec-bus producer entry.
2. `next-row pc = nextpc_mux(row i)` — the #100 PC-continuation SEAM
   (`pcLastMessageExpr`, `main.pil:410`), STUBBED here as a hypothesis `h_seam`,
   discharged downstream by X100.1a's `BalancedChannels` conjunct.
3. `nextpc_mux(row i) = pc_col(i) + 4` — sequential selectors
   (`set_pc = 0`, `flag = 0`, `jmp_offset2 = 4`).

plus the FAITHFUL pc-column ↔ Sail-PC bridge `h_pc_col` (the `pc` COLUMN, coerced
to `BitVec 64`, equals the Sail PC — the control-flow analogue of the a/b lane
bridges) and a no-field-wraparound side condition `h_no_overflow`.

The 3-equality chain yields exactly the `nextPC_matches` promise of
`RTypePromises` for ADD, whose pure-spec `nextPC` is `add_input.PC + 4#64`.

## Why this is a genuine reduction, not a relocation

`h_seam` is STRICTLY SMALLER than `h_nextPC_matches`:

* `h_nextPC_matches` : `register_type_pc_equiv ▸ BitVec.ofNat 64 (exec_row[1].pc).val
   = add_input.PC + 4#64`  — a `BitVec`-level coerced equation against the Sail
   PC with the `+4` arithmetic baked in.
* `h_seam` : `exec_row[1].pc = (pcLastMessage row).pc`  — a single `FGL` equation
   (the X100.1a BalancedChannels conjunct), with no coercion, no Sail PC, no `+4`.

The remaining new binders (`h_set_pc`, `h_flag`, `h_jmp2`, `h_pc_col`,
`h_no_overflow`) are faithful per-row decode / column-bridge facts, NOT a clone of
`h_nextPC_matches`. This is the structural-unpacking shape (one compressed promise
→ explicit ingredients).

## Trust note

No PROJECT (`ZiskFv.*`) axioms. Closure is Sail + Lean kernel
(`propext` / `Classical.choice` / `Quot.sound`). `h_seam` carries a clearly-
labelled stub status (it is a hypothesis, never a `sorry`); the bridge lemma and
the gate theorem are fully proved.
-/

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Channels.PcContinuation (PcMessage)
open ZiskFv.AirsClean.Main (pcLastMessageExpr)

namespace ZiskFv.Compliance.GapC

/-! ## The concrete PC-continuation push message (faithful to the real emission) -/

/-- Concrete-FGL evaluation of the Main next-PC continuation push message
    (`pcLastMessageExpr`, `main.pil:410`), applied to a concrete row. The mux is

    `set_pc*(c_0 + jmp_offset1) + (1-set_pc)*(pc + jmp_offset2)
       + flag*(jmp_offset1 - jmp_offset2)`. -/
@[reducible]
def pcLastMessage (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL) : PcMessage FGL :=
  { pc := row.core.set_pc * (row.core.c_0 + row.core.jmp_offset1)
            + (1 - row.core.set_pc) * (row.core.pc + row.core.jmp_offset2)
            + row.core.flag * (row.core.jmp_offset1 - row.core.jmp_offset2)
    tag := row.rom.main_step + 1 }

/-- **Faithfulness.** The concrete `pcLastMessage` is exactly the evaluation of
    the real circuit emission `pcLastMessageExpr`. This pins the seam fact
    `h_seam` to the genuine #100 emission (no invented formula). Mirrors the
    `eval_aMemMessageExpr` / `eval_cMemMessageExpr` idiom in `Main/Bridge.lean`. -/
theorem eval_pcLastMessageExpr
    (env : Environment FGL) (row : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    eval env (pcLastMessageExpr row) = pcLastMessage (eval env row) := by
  rw [PcMessage.mk.injEq]
  simp only [pcLastMessageExpr, pcLastMessage,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp <;> ring_nf

/-! ## Field-to-bitvec arithmetic -/

/-- Field-to-bitvec `+4` advance: when the field add does not wrap the modulus,
    it maps to a `BitVec 64` add. (`FGL.val < GL_prime < 2^64`, so the bitvec
    side never overflows; the side condition rules out the field side wrapping.) -/
theorem ofNat_val_add_four
    (x : FGL) (h : x.val + 4 < GL_prime) :
    BitVec.ofNat 64 ((x + 4 : FGL)).val = BitVec.ofNat 64 x.val + 4#64 := by
  rw [show ((x + 4 : FGL)).val = x.val + 4 from by
        simp only [Fin.add_def]; exact Nat.mod_eq_of_lt h]
  bv_omega

/-- Sequential mux reduction: with `set_pc = 0` and `flag = 0`, the next-PC mux
    output collapses to `pc + jmp_offset2`. -/
theorem pcLastMessage_pc_sequential
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_set_pc : row.core.set_pc = 0)
    (h_flag : row.core.flag = 0) :
    (pcLastMessage row).pc = row.core.pc + row.core.jmp_offset2 := by
  simp only [pcLastMessage, h_set_pc, h_flag]
  ring

/-- **Flag-free sequential mux reduction.** With `set_pc = 0` and
    `jmp_offset1 = jmp_offset2` the next-PC mux output collapses to
    `pc + jmp_offset2` REGARDLESS of `flag`: the flag term of the mux is
    `flag * (jmp_offset1 - jmp_offset2)`, which vanishes when the two offsets
    are equal. For every sequential ALU opcode the ZisK decode sets
    `jmp_offset1 = jmp_offset2 = 4` (documented in
    `Tactics/ALURTypeArchetype.lean`), so this is the faithful reduction and it
    DROPS the `flag = 0` hypothesis that `pcLastMessage_pc_sequential` needed. -/
theorem pcLastMessage_pc_sequential_of_jmp_eq
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_set_pc : row.core.set_pc = 0)
    (h_jmp_eq : row.core.jmp_offset1 = row.core.jmp_offset2) :
    (pcLastMessage row).pc = row.core.pc + row.core.jmp_offset2 := by
  simp only [pcLastMessage, h_set_pc, h_jmp_eq]
  ring

/-! ## The Route C bridge lemma -/

/-- **Route C bridge lemma (`nextPC_matches_of_seam`).** Discharge a
    `nextPC_matches`-shaped goal for a SEQUENTIAL `+4` opcode.

    GIVEN
    * `h_seam` — the X100.1a SEAM output: the producer exec-bus PC equals this
      row's next-PC continuation push (`pcLastMessage` = `eval pcLastMessageExpr`).
      STUBBED as a hypothesis (discharged downstream by X100.1a BalancedChannels).
    * `h_set_pc`, `h_flag` — sequential mux selectors.
    * `h_jmp2` — `jmp_offset2 = 4` for a sequential op.
    * `h_pc_col` — the FAITHFUL pc-column ↔ Sail-PC bridge.
    * `h_no_overflow` — no field wraparound on the `+4`.

    CONCLUDES the coerced `nextPC_matches` equation against `sailPC + 4#64`. -/
theorem nextPC_matches_of_seam
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (nextPcVal : FGL) (sailPC : BitVec 64)
    (h_seam : nextPcVal = (pcLastMessage row).pc)
    (h_set_pc : row.core.set_pc = 0)
    (h_flag : row.core.flag = 0)
    (h_jmp2 : row.core.jmp_offset2 = 4)
    (h_pc_col :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (row.core.pc).val) : BitVec 64) = sailPC)
    (h_no_overflow : (row.core.pc).val + 4 < GL_prime) :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 nextPcVal.val) : BitVec 64)
      = sailPC + 4#64 := by
  -- 1+2+3: seam + sequential mux ⟹ nextPcVal = pc_col + 4 (field level).
  have h_field : nextPcVal = row.core.pc + 4 := by
    rw [h_seam, pcLastMessage_pc_sequential row h_set_pc h_flag, h_jmp2]
  -- The `register_type_pc_equiv ▸` coercion is `rfl` (both sides are `BitVec 64`).
  show (BitVec.ofNat 64 nextPcVal.val : BitVec 64) = sailPC + 4#64
  rw [← h_pc_col]
  show (BitVec.ofNat 64 nextPcVal.val : BitVec 64)
    = BitVec.ofNat 64 (row.core.pc).val + 4#64
  rw [h_field, ofNat_val_add_four (row.core.pc) h_no_overflow]

/-- **Route C bridge lemma, flag-free (`nextPC_matches_of_seam'`).** Same as
    `nextPC_matches_of_seam`, but the sequential mux is collapsed via
    `pcLastMessage_pc_sequential_of_jmp_eq` (offsets equal) rather than
    `flag = 0`. This DROPS the `h_flag` hypothesis: the flag term of the mux
    cancels once `jmp_offset1 = jmp_offset2`, so for a sequential ALU op (where
    the decode sets both offsets to 4) the next-PC value is `pc + jmp_offset2`
    independent of `flag`.

    The remaining hypotheses are exactly the genuine residuals:
    * `h_seam` — the X100.1a SEAM output (the channel-balance trust class).
    * `h_decode` (`set_pc = 0`, `jmp_offset1 = jmp_offset2`, `jmp_offset2 = 4`)
      — ROM/decode column facts (the `aeneasBridgeTrust` decode class).
    * `h_pc_col` — the FAITHFUL pc-column ↔ Sail-PC bridge (the control-flow
      analogue of the operand lane bridges; the `aeneasBridgeTrust` pc class).
    * `h_no_overflow` — a pure `+4` field side-condition. -/
theorem nextPC_matches_of_seam'
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (nextPcVal : FGL) (sailPC : BitVec 64)
    (h_seam : nextPcVal = (pcLastMessage row).pc)
    (h_set_pc : row.core.set_pc = 0)
    (h_jmp_eq : row.core.jmp_offset1 = row.core.jmp_offset2)
    (h_jmp2 : row.core.jmp_offset2 = 4)
    (h_pc_col :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (row.core.pc).val) : BitVec 64) = sailPC)
    (h_no_overflow : (row.core.pc).val + 4 < GL_prime) :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 nextPcVal.val) : BitVec 64)
      = sailPC + 4#64 := by
  have h_field : nextPcVal = row.core.pc + 4 := by
    rw [h_seam, pcLastMessage_pc_sequential_of_jmp_eq row h_set_pc h_jmp_eq, h_jmp2]
  show (BitVec.ofNat 64 nextPcVal.val : BitVec 64) = sailPC + 4#64
  rw [← h_pc_col]
  show (BitVec.ofNat 64 nextPcVal.val : BitVec 64)
    = BitVec.ofNat 64 (row.core.pc).val + 4#64
  rw [h_field, ofNat_val_add_four (row.core.pc) h_no_overflow]

/-! ## Non-vacuity witness

A concrete `k ≥ 2`-style sequential witness: a real Main row with `pc = 0x1000`,
sequential selectors (`set_pc = 0`, `flag = 0`, `jmp_offset2 = 4`), and a concrete
`execRow`-style next-PC value EQUAL to the real mux output (`pcLastMessage`,
NOT arbitrary). `h_seam` then holds by `rfl`, and `nextPC_matches_of_seam` fires,
yielding a TRUE, non-vacuous coerced `nextPC = pc + 4` equation. This proves the
Route C discharge is jointly satisfiable with a faithful next-row PC. -/

/-- A concrete sequential Main+ROM witness row with `pc = 4096`. All control
    columns are set for a sequential ADD step (`set_pc = 0`, `flag = 0`,
    `jmp_offset2 = 4`); the data/ROM columns are zeroed (irrelevant to the seam). -/
def witnessRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL where
  core :=
    { a_0 := 0, a_1 := 0, b_0 := 0, b_1 := 0, c_0 := 0, c_1 := 0
      flag := 0, pc := 4096, is_external_op := 1, op := OP_ADD, m32 := 0
      ind_width := 0, set_pc := 0, jmp_offset1 := 0, jmp_offset2 := 4
      store_pc := 0, im_high_degree_2 := 0, segment_l1 := 0 }
  rom :=
    { a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0
      store_offset := 0, a_src_imm := 0, a_src_mem := 0, is_precompiled := 0
      b_src_imm := 0, b_src_mem := 0, store_mem := 0, store_ind := 0
      b_src_ind := 0, a_src_reg := 0, b_src_reg := 0, store_reg := 0
      addr0 := 0, addr1 := 0, addr2 := 0, main_step := 0 }

/-- The witness's real next-row PC: the genuine mux output of `witnessRow`
    (`pcLastMessage`), NOT an arbitrary value. By construction it is `4096 + 4`. -/
def witnessNextPc : FGL := (pcLastMessage witnessRow).pc

/-- **NON-VACUITY.** Instantiating `nextPC_matches_of_seam` on the concrete
    sequential witness — with the faithful next-row PC (`= pcLastMessage`, so
    `h_seam` is `rfl`) and `sailPC = 4096#64` — yields a TRUE coerced equation
    `BitVec.ofNat 64 witnessNextPc.val = 4096#64 + 4#64`. The Route C hypotheses
    are jointly satisfiable with a real next-row PC, so the discharge is not
    vacuous. -/
theorem nextPC_matches_of_seam_nonvacuous :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 witnessNextPc.val) : BitVec 64)
      = (4096#64 : BitVec 64) + 4#64 :=
  nextPC_matches_of_seam witnessRow witnessNextPc 4096#64
    rfl                              -- h_seam: witnessNextPc = (pcLastMessage witnessRow).pc
    rfl                              -- h_set_pc
    rfl                              -- h_flag
    rfl                              -- h_jmp2
    (by decide)                     -- h_pc_col: ofNat 64 (4096).val = 4096#64
    (by decide)                     -- h_no_overflow: 4096 + 4 < GL_prime

/-- The witness next-PC, evaluated concretely, is `4100` — the genuine `pc + 4`
    of a sequential step. Confirms `h_seam` is fed the REAL mux output. -/
theorem witnessNextPc_eq : witnessNextPc = (4100 : FGL) := by
  decide

end ZiskFv.Compliance.GapC

#print axioms ZiskFv.Compliance.GapC.nextPC_matches_of_seam
#print axioms ZiskFv.Compliance.GapC.nextPC_matches_of_seam_nonvacuous
#print axioms ZiskFv.Compliance.GapC.eval_pcLastMessageExpr
