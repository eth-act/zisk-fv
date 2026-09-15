# Issue #61 Phase 0 — the raw-word join: design decision document

**Track C, read-only.** No file edits, no commits, no gates. All file:line citations verified by
reading the definitions in `/home/cody/zisk-fv` at `origin/main` = `2da97416`.

> **Checkout note for the coordinator.** The base checkout `/home/cody/zisk-fv` is at `a60b2bd5`,
> which is **behind** `origin/main` (`2da97416`). Everything below is stated against `origin/main`;
> where the two differ I read `git show origin/main:<path>` explicitly. Anyone starting this work
> should `git fetch && git checkout` the real tip first, because PR #293 changed the root theorem's
> **conclusion**, which changes the shape of the endpoint this design proposes (see §1.4).

---

## 0. Verification of the scouting report

I re-derived the load-bearing claims from primary sources rather than trusting the summary.

| Scout claim | Verdict | Evidence I read |
|---|---|---|
| The raw-word → `ZiskInst` lowering is already Aeneas-extracted into Lean | **CONFIRMED** | `trust/aeneas/ProductionM2.lean:3642-3672` |
| ...and is in the Lake build graph (not a side artifact) | **CONFIRMED** | `lakefile.toml` declares `[[lean_lib]] name = "ProductionM2"`; `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Helpers.lean:29` and `ZiskFv/Compliance/AeneasBridgeTrust/Decode/Leaves.lean:7` both `import ProductionM2`, and `ZiskFv` is a default target |
| ...and it calls the *production* lowerer, not a re-implementation | **CONFIRMED** | `ProductionM2.lean:3652-3665` calls `riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input`, the same entry point the ELF transpiler uses (`zisk/core/src/riscv2zisk_context.rs:663,834,941,1000,1059,1100`) |
| A ~4.7k-line 63-op join was built in June and left unmerged | **CONFIRMED** | 9 files exist at `a16bd97c`, absent from `origin/main`; exact line counts in §3 |
| Defect 1: `SRC_IND` written as literal `3` | **CONFIRMED** | asset writes `b_src_ind := decide (e.b_src = (3#u64 : Std.U64))`; truth is `SRC_IND = 5` (`zisk/core/src/zisk_inst.rs:53`, extracted at `ProductionM2.lean:2704`); `3` is `SRC_STEP` (`zisk_inst.rs:49`) |
| Defect 2: unsigned coercion of `a/b_offset_imm0` | **CONFIRMED** | asset writes `(e.b_offset_imm0.val : FGL)` with `UScalar.val : ℕ` (`build/aeneas-lean/Aeneas/Std/Scalar/Core.lean:69`); `rom.rs:226-236` reinterprets as `i64` and negates |
| Defect 3 (milder): `a_imm1`/`b_imm1` ungated | **CONFIRMED** | asset writes `a_imm1 := (e.a_use_sp_imm1.val : FGL)`; `rom.rs:240-244` zeroes it unless `a_src == SRC_IMM` |
| Injectivity route is dead (FENCE discards operands) | **CONFIRMED** | `zisk/core/src/riscv2zisk_single_row.rs:195` routes Fence to `nop`; `zisk/core/src/riscv2zisk_context.rs:896-916` `nop` builds from constants only, reading nothing from `rd`/`rs1`/`imm`/`pred`/`succ` |
| `h_prog` gained a fifth clause since June | **CONFIRMED** | `origin/main` `RomDecodeBindingOps.lean:327-334` has 5 clauses incl. `store_offset = Transpiler.ind (regidx_to_fin c.rd)`; `a16bd97c:…/RomDecodeBinding.lean:496-502` had 4 |

**Three things the scout did not report, which change the recommendation:**

1. **A concrete in-tree witness already falsifies the June asset.** `ZiskFv/Compliance/SdLdSpinWitness.lean:105-119`
   defines `sdLdLdBits` with `b_src_ind := true` — an honest LD ROM row with flag bit 12 set. The
   June `romFlagBitsOfExtract` would compute that bit as `decide (5 = 3) = false`. So the falsification
   is not hypothetical: it is checkable against a witness that already ships in the semantic gate
   (`trust/scripts/check-all-semantic.sh:96`).
2. **`root_soundness`'s conclusion is now decode-indexed** (PR #293). The June endpoint's
   "same conclusion, thinner premises" framing no longer type-checks unchanged. See §1.4.
3. **Tracker/tree discrepancy** (bookkeeping observation only, claiming no progress): issue #159
   is `CLOSED / COMPLETED` and issue #172's body asserts `root_soundness_rawProgram` landed via
   "PRs #167 → #168 → #170", but `grep -rn "root_soundness_rawProgram" ZiskFv/ trust/ bin/` returns
   nothing on main, and PR #170's own body says it "**no longer closes #159**" and that the
   grounding "remains #159's residual (machinery preserved in this PR's git history)".

---

## 1. The gap, precisely stated

### 1.1 What the trace commits to (the ZisK side of the join)

An accepted ZisK trace commits to a **program**, but that program is already a *lowered* object —
eleven field elements per instruction, not a RISC-V word.

`ZiskFv/Compliance/AcceptedZiskTrace.lean:93-95`:

```lean
structure AcceptedZiskTrace (numInstructions : Nat) where
  programLength : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program programLength
  witness : Air.Flat.EnsembleWitness
    (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble programLength program).ensemble
  constraints_hold : witness.Constraints
  channels_balanced : witness.BalancedChannels
  mem_replay_table : …
```

`ZiskFv/AirsClean/ZiskInstructionRom.lean:51`:

```lean
@[reducible] def Program (length : ℕ) : Type := Fin length → ZiskRomMessage FGL
```

`ZiskFv/Channels/ZiskRomBus.lean:61-90` — the eleven slots:

```lean
structure ZiskRomMessage (F : Type) where
  line, a_offset_imm0, a_imm1, b_offset_imm0, b_imm1,
  ind_width, op, store_offset, jmp_offset1, jmp_offset2, flags : F
```

`flags` is a packed 16-bit word (`ZiskFv/AirsClean/Main/Circuit.lean:198-214` `packFlags`, mirroring
`zisk/core/src/zisk_inst.rs:289-308` `get_flags` bit for bit, up to bit 15 = `store == STORE_REG`).

The ROM's static table is *membership-only* — `ZiskFv/AirsClean/ZiskInstructionRom.lean:56-67`:

```lean
def romStaticTable (length) (program) : StaticTable FGL ZiskRomMessage where
  row i := program i
  index msg := msg.line.val
  Spec msg := ∃ i, msg = program i
```

So the circuit checks *"the Main row's ROM tuple is some entry of the committed program"*. It never
checks *what* that entry means.

### 1.2 What the raw side already offers

`trust/aeneas/ProductionM2.lean:3645-3672`:

```lean
def aeneas_extract.extract_transpile_rv64im_raw
  (raw1 : Std.U32) : Result aeneas_extract.Rv64imTranspileExtract := do
  let decoded ← aeneas_extract.rv64im_decode.decode_32_core raw1
  let decode  ← aeneas_extract.decode_extract_from_decoded decoded
  let o       ← aeneas_extract.lowering_opcode decoded.opcode
  match o with
  | none => … ok { accepted := false, decode, row := default }
  | some opcode =>
    let input ← riscv2zisk_single_row.Rv64imLoweringInput.new
                  0#u64 decoded.rd decoded.rs1 decoded.rs2 decoded.imm
    let ctx   ← riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
                  { … } input opcode false
    let zib   ← core.option.Option.unwrap ctx.extract_inst
    let row   ← aeneas_extract.ZiskInstExtract.from_inst zib.i
    ok { accepted := true, decode, row }
```

with (`ProductionM2.lean:880-903, 957-961`):

```lean
structure aeneas_extract.ZiskInstExtract where
  paddr : Std.U64;  store_pc, store_use_sp : Bool;  store : Std.U64
  store_offset : Std.I64;  set_pc, is_precompiled : Bool;  ind_width : Std.U64
  «end» : Bool;  a_src, a_use_sp_imm1, a_offset_imm0 : Std.U64
  b_src, b_use_sp_imm1, b_offset_imm0 : Std.U64
  jmp_offset1, jmp_offset2 : Std.I64;  is_external_op : Bool
  op : Std.U8;  op_type_id : Std.U32;  m32 : Bool
  input_size : Std.U64;  sorted_pc_list_index : Std.Usize

structure aeneas_extract.Rv64imTranspileExtract where
  accepted : Bool;  decode : Rv64imDecodeExtract;  row : ZiskInstExtract
```

This is the **real production lowerer**, not a Lean re-implementation: `zisk/core/src/aeneas_extract.rs`
is a thin harness over `crate::{Riscv2ZiskContext, Rv64imLoweringInput, …}`, and the extraction is
CI-checked byte-identical (`nix run .#aeneas-production-extract-check-tracked`, `trust/aeneas/README.md`).

### 1.3 The gap in one sentence

**There is no function `ZiskInstExtract → ZiskRomMessage FGL` in the tree, and no theorem that the
committed `trace.program` is the image of any raw program under it.**

That missing arrow is a real, specified object: it is `compute_trace_rom` at
`zisk/state-machines/rom/src/rom.rs:204-260`. Reading that function, the per-instruction row is:

| ROM slot | rom.rs line | Rule |
|---|---|---|
| `line` | `:238` | `F::from_u64(inst.paddr)` |
| `a_offset_imm0` | `:226-230` | **signed reinterpretation**: `if inst.a_offset_imm0 as i64 >= 0 then from_u64(x) else neg(from_u64((-(x as i64)) as u64))` |
| `a_imm1` | `:240-241` | `from_u64(if inst.a_src == SRC_IMM then inst.a_use_sp_imm1 else 0)` — **gated** |
| `b_offset_imm0` | `:231-235` | signed reinterpretation, as above |
| `b_imm1` | `:242-243` | gated on `b_src == SRC_IMM` |
| `ind_width` | `:245` | `from_u64(inst.ind_width)` |
| `op` | `:247-255` | `inst.op`, with Fcall/FcallGet/FcallParam remapped to `CopyB` (out of RV64IM scope) |
| `store_offset` | `:220-225, :256` | signed split from `i64` |
| `jmp_offset1/2` | `:210-219, :257-258` | signed split from `i64` |
| `flags` | `:259` | `from_u64(inst.get_flags())` — the 16-bit pack |

And the iteration order is `for (i, key) in rom.insts.keys().sorted().enumerate()` (`:205`) — **ROM
entry `i` is the `i`-th smallest `paddr`**, not `4*i`.

### 1.4 The root theorem the join must attach to (verified on `origin/main`)

`git show origin/main:ZiskFv/Soundness.lean` — the live signature, after PR #293:

```lean
theorem root_soundness
    (numInstructions : Nat)
    (ziskTrace  : AcceptedZiskTrace numInstructions)
    (sailTrace  : SailTrace numInstructions)
    (ziskStep   : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (programDecodes : ∀ i : Fin numInstructions, ProgramDecode ziskTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i (programDecodes i)) :=
  fun i =>
    stepSound_of_evidence ziskTrace sailTrace i (ziskStep i)
      (rowDecode_of_programDecode ziskTrace i (programDecodes i)) (inputsAgree i)
      (memEvidence_of_bootSeed bootSeed i) (hAvoidKnownBugs i)
```

`programDecodes` is what the join must make *derived*. Its per-op payload
(`ZiskFv/Compliance/TraceLevelExport/ProgramDecode.lean:47-64`, SUB shown):

```lean
structure ProgramDecode_sub … where
  h_idx : i.val + 1 < trace.mainTable.table.length
  bits : RomFlagBits
  h_bits_ieo, h_bits_m32, h_bits_set_pc, h_bits_store_pc, h_bits_store_ind : …
  h_prog : ∀ j : Fin trace.programLength,
    (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc i.val →
      (trace.program j).op = ZiskFv.Trusted.OP_SUB
    ∧ (trace.program j).jmp_offset1 = 4
    ∧ (trace.program j).jmp_offset2 = 4
    ∧ (trace.program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)   -- NEW since June
    ∧ (trace.program j).flags = packFlags bits
```

**Two consequences of PR #293 for any additive endpoint.** `StepSound` now takes the `RowDecode` as
an index (`Dispatcher.lean:1212-1229`), and the JALR arm genuinely consumes it
(`Pilot.execRowAt ziskTrace decode.rows.finish`). So a `root_soundness_rawProgram` cannot say
"same conclusion as `root_soundness`": its conclusion is indexed by the *derived*
`rowDecode_of_programDecode … (programDecode_of_raw …)`, a different term. For 62 arms this is
irrelevant (`| other, _ => StepSoundWithoutDecode …`); for JALR the two conclusions are
propositionally distinct until one proves the derived decode's `rows.finish` agrees. **Do not paper
over this**; either state the endpoint with the derived index (correct, slightly different theorem)
or carry an explicit JALR row-range agreement lemma.

---

## 2. Why the obvious move is laundering

The obvious move is: *"the ROM message already contains `op`, the register indices, the immediates —
just treat it as the instruction."* Concretely, someone writes a `rawWordOfRomMessage` that reassembles
a 32-bit word from the eleven slots, or declares that binding `programDecodes` to the ROM columns is
already "program-grounded". Here is what a reviewer sees when they pull that thread.

**(a) The map is not injective, so "the word" does not exist.** FENCE lowers through
`self.nop(riscv_instruction, 4)` (`riscv2zisk_single_row.rs:195`), and `nop`
(`riscv2zisk_context.rs:896-916`) builds its row from constants only — `src_a_imm(0)`, `src_b_imm(0)`,
`op_zisk(ZiskOp::Flag)`, `j(4,4)` — reading **nothing** from `rd`, `rs1`, `imm`, `pred`, or `succ`.
Every `fence` word in RV64IM produces the identical ROM row. Separately, every word the lowerer
rejects produces the same default row. So there is no function from messages back to words, and any
"recovery" lemma has to be weakened until it no longer recovers a unique word — at which point it has
stopped being the thing anyone wanted.

**(b) It moves the obligation instead of discharging it.** `root_soundness` today assumes the
committed ROM decodes as the claimed op. Reading the ROM as if it were the program renames that
assumption "program grounding" and changes nothing: `trace.program` is still an arbitrary
prover-chosen `Fin programLength → ZiskRomMessage FGL`, and `romStaticTable.Spec msg := ∃ i, msg = program i`
(`ZiskInstructionRom.lean:63`) still checks only membership. A malicious prover picks a `program` whose
row at `pc` is a well-formed SUB tuple while the actual binary at that address is a JAL, and every
hypothesis is satisfied. Nothing in `AcceptedZiskTrace` forbids it. The theorem's strength is
literally unchanged; only the prose moved.

**(c) The specific way it fails in review.** A reviewer asks: *"show me the trace where this
premise is inhabited, and show me the prover step that produces it."* The honest answer for the ROM-as-program
reading is "the prover writes down whatever eleven-tuple it likes". The honest answer for a real
raw-word join is "the prover ran `compute_trace_rom` on the transpiled ELF". Only the second one is a
statement about the pipeline that actually built the witness. That distinction — *is the premise a
property of an honestly-generated witness, or a free choice?* — is the whole content of #61.

**(d) And the near-miss version is worse.** The June asset (§3) did the right thing structurally and
then got the serialization wrong in three places. That is strictly more dangerous than doing nothing,
because it *looks* like grounding: 63 kernel-sound theorems, zero new axioms, a trust-ledger entry
asserting "Non-vacuous: … `ProgramBinding` holds because the ROM is its serialized lowering". A
reviewer skimming the axiom closure sees green. A reviewer who checks the premise finds it is false
for every program containing a load or store — because `ProgramBinding` is `∀ k`, one bad entry
poisons the whole program, so the register arms become vacuous too. **Re-landing that asset as-is
would be the single most efficient way to launder this obligation**, and the fact that the mistake was
made once already by careful people is the reason §4's spike is a hard gate rather than a nicety.

---

## 3. The unmerged June asset (input to every candidate below)

Reachable from `main`'s history at `a16bd97c`; present in no file on `origin/main`. Verified line counts:

| File (at `a16bd97c`) | lines |
|---|---|
| `ZiskFv/Compliance/TraceLevelExport/RawProgramBinding.lean` | 102 |
| `…/RawProgramBindingControl.lean` | 1066 |
| `…/RawProgramBindingCopyb.lean` | 856 |
| `…/RawProgramBindingLoadStore.lean` | 609 |
| `…/RawProgramBindingImmediate.lean` | 560 |
| `…/RawProgramBindingMext.lean` | 349 |
| `…/RawProgramBindingRegister.lean` | 244 |
| `…/RawRowDecode.lean` | 201 |
| `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Totality.lean` | 743 |
| **total** | **4730** |

plus `ZiskFv/Soundness.lean` +36 at `e529530b` and a 51-line trust-ledger entry at `fe7d353c`.

Its core (verbatim from `a16bd97c:…/RawProgramBinding.lean`):

```lean
def serializeExtract (line : FGL) (e : ZiskInstExtract) : ZiskRomMessage FGL where
  line := line
  a_offset_imm0 := (e.a_offset_imm0.val : FGL)     -- ← DEFECT 2 (UScalar.val : ℕ)
  a_imm1        := (e.a_use_sp_imm1.val : FGL)     -- ← DEFECT 3 (ungated)
  b_offset_imm0 := (e.b_offset_imm0.val : FGL)     -- ← DEFECT 2
  b_imm1        := (e.b_use_sp_imm1.val : FGL)     -- ← DEFECT 3
  ind_width     := (e.ind_width.val : FGL)
  op            := (e.op.val : FGL)
  store_offset  := (e.store_offset.val : FGL)      -- OK: IScalar.val : ℤ, sign-correct
  jmp_offset1   := (e.jmp_offset1.val : FGL)       -- OK
  jmp_offset2   := (e.jmp_offset2.val : FGL)       -- OK
  flags         := packFlags (romFlagBitsOfExtract e)

def romFlagBitsOfExtract (e : ZiskInstExtract) : RomFlagBits where
  …
  b_src_ind := decide (e.b_src = (3#u64 : Std.U64))   -- ← DEFECT 1 (SRC_IND = 5)
  …

noncomputable def romMessageOfRaw (line : FGL) (raw : BitVec 32) : ZiskRomMessage FGL :=
  match extract_transpile_rv64im_raw (toU32 raw) with
  | .ok ext => serializeExtract line ext.row
  | _       => ⟨line, 0,0,0,0,0,0,0,0,0,0⟩

def ProgramBinding (trace) (rawProgram : Fin n → BitVec 32) : Prop :=
  ∀ k, trace.program k = romMessageOfRaw (trace.program k).line (rawProgram k)
```

### 3.1 Defect 1 — `SRC_IND` literal, and its bite

`SRC_IND = 5` (`zisk/core/src/zisk_inst.rs:53`), extracted as
`@[global_simps, irreducible] def zisk_inst.SRC_IND : Std.U64 := 5#u64` (`ProductionM2.lean:2704`).
`3` is `SRC_STEP` (`zisk_inst.rs:49`). Every load and store sets `b_src := SRC_IND` via
`src_b_ind` (`ProductionM2.lean:2709-2738`; e.g. reached from `load_op_with_reg_offset` at `:2754`).
The real ROM's `get_flags` sets bit 12 from `b_src == SRC_IND` (`zisk_inst.rs:302`).

**In-tree confirmation:** `ZiskFv/Compliance/SdLdSpinWitness.lean:105-119` — the honest LD row of the
SD/LD spin witness has `b_src_ind := true`. Its committed message is
`sdLdLdProgramRow` (`:127-130`, `flags := packFlags sdLdLdBits`). Under the June serialization the
computed bit would be `decide (5 = 3) = false`, so `packFlags` differs from the committed `flags` by
`4096 ≠ 0` in Goldilocks, and `ProgramBinding` is **false at that entry**.

### 3.2 Defect 2 — unsigned coercion, and why register/immediate ops hid it

`UScalar.val : ℕ` (`build/aeneas-lean/Aeneas/Std/Scalar/Core.lean:69`); `IScalar.val : ℤ` (`:77`).
So the three `I64` slots (`store_offset`, `jmp_offset1/2`) got the correct sign-aware `Int → FGL`
cast, and only the two `U64` offset slots were wrong. That is exactly why the bug survived:

- `src_a_imm` / `src_b_imm` (`ProductionM2.lean:2086-2118`) set `*_offset_imm0 := value &&& 0xFFFFFFFF`
  — always `< 2^32`, so `as i64 >= 0` and rom.rs's signed branch is a no-op. Register and immediate
  families never exercise the negative path.
- `src_b_ind` (`:2709-2738`) sets `b_offset_imm0 := offset` where the caller passes
  `IScalar.hcast .U64 i.imm` (`:2751`). Aeneas `IScalar.hcast` **sign-extends**
  (`Aeneas/Std/Scalar/Casts.lean:41-43`, matching Rust `as`), so a negative RISC-V offset yields
  `b_offset_imm0 ≥ 2^63`.

For such a value, real = `-(2^64 − x) mod p`, serialized = `x mod p`, and the difference is
`2^64 mod p = 2^32 − 1 ≠ 0` for `p = 2^64 − 2^32 + 1`. **Any `ld a0, -8(sp)` breaks the binding.**

### 3.3 Defect 3 — ungated `a_imm1`/`b_imm1`

Provably harmless on this path but not for free: it needs a lemma that every non-`SRC_IMM` setter on
the RV64IM single-row path leaves `*_use_sp_imm1 = 0`. Verified setters: `src_b_lastc`
(`ProductionM2.lean:2240-2254`, sets `b_use_sp_imm1 := 0#u64`), `src_b_ind` with `use_sp = false`
(`:2726-2737`), `src_a_reg`/`src_b_reg`. All RV64IM callers pass `use_sp = false`.

### 3.4 What is genuinely good in the asset, and should be salvaged first

- **`Extraction/Totality.lean` (743 lines)** — proves the lowerer *succeeds* (`= ok …`) for symbolic
  in-range registers, discharging the side condition #111's static pins and block-2's dynamic pins
  currently **assume**. Key content: `decode_r_bounds` (`:45`), the `numBits`-split cast lemmas
  (`:55-80`), and the per-shape `*_ok` totality theorems (`create_register_op_typed_ok:134`,
  `immediate_op_typed_ok:239`, `load_op_with_reg_offset_ok:332`, `store_op_typed_ok:400`,
  `create_branch_op_typed_ok:486`, …). It is **independent of the defective serialization** and is
  independently valuable. Land it first, alone.
- **The per-family `<family>_decode_fields_of_binding` + `transpile_<op>` sweep.** These are correct
  and are the expensive part. E.g. `register_decode_fields_of_binding` (`RawProgramBindingRegister.lean:117-137`)
  delivers exactly `msg.op / msg.jmp_offset1 / msg.jmp_offset2 / msg.flags`, and the load/store macro
  adds `msg.ind_width`. None of these touch the two broken offset slots — which is precisely why they
  are salvageable and why the vacuity is entirely in the premise, not the bridges.

### 3.5 The residual the asset silently left open

`ProgramBinding` reads `romMessageOfRaw (trace.program k).line (rawProgram k)` — it feeds the message
**its own** `line` back in. So the binding constrains ten slots and says **nothing** about the
eleventh. Nothing forces ROM entry `k` to sit at the address the binary places word `k` at
(`rom.rs:238` `line = paddr`, keys sorted at `:205`). The June trust-ledger draft at `fe7d353c` does
not name this. Any re-landing must.

---

## 4. Candidate designs

### (a) Put the raw word and an agreement certificate inside `AcceptedZiskTrace`

**Sketch.** Add `rawProgram : Fin programLength → BitVec 32` and
`program_is_lowering : ∀ k, program k = romRowOf (addr k) (rawProgram k)` as fields of
`AcceptedZiskTrace`. Every downstream consumer gets the grounding for free.

**Adds to trust surface.** Two new structure fields, i.e. two new obligations on *every* trace
constructor. **Removes.** Nothing by itself; it relocates where the premise is discharged.

**Difficulty.** Medium proof work, **high blast radius**: every instantiation witness must now build
a raw program and prove the binding — `AddSpinWitness.lean` (65K), `AddAddiSpinWitness.lean` (82K),
`SdLdSpinWitness.lean`, `root_soundness_instantiation_degenerate.lean`, plus #74. `AcceptedZiskTrace`
is also adjacent to the "protected proof interfaces" AGENTS.md fences off, so it needs explicit
owner sign-off.

**Honest failure mode.** The witnesses are hand-built to satisfy constraints, not transpiled from
real ELF words (see §4.1). Forcing the field on all of them creates pressure to make the field weak
enough that the existing witnesses still typecheck — and a weakened field is exactly the laundering
outcome. PR #170's own rationale already rejected this route ("putting it in `AcceptedZiskTrace`
would only burden #74's instantiation").

### (b) Prove the lowering injective and recover the word from the eleven slots

**Sketch.** Show `romRowOf` injective on RV64IM, define its inverse, read the raw word off the
committed ROM.

**Verdict: eliminated, not merely hard.** Two independent counterexamples, verified:
FENCE discards `pred`/`succ`/`rd`/`rs1` (`riscv2zisk_context.rs:896-916`), and all rejected words
collapse to one default row (`ProductionM2.lean:3655-3657`). Injectivity is **false**, so the only way
to "make progress" here is to weaken the statement until it no longer identifies a word. Do not
attempt.

### (c) Bind the committed ROM to a raw program through the already-extracted transpiler

**Sketch.** Repair `serializeExtract` into a *cited line-by-line transcription* of `rom.rs:204-260`;
generalize the binding to carry an explicit ROM layout; prove it inhabited on a real concrete trace;
then re-target the salvaged 63-op sweep at `ProgramDecode` and add an **additive** endpoint. Proposed
shape (note the three differences from June, all deliberate):

```lean
/-- Literal transcription of `zisk/state-machines/rom/src/rom.rs:204-260`.
    Every field carries its rom.rs line in a comment. -/
def romRowOf (line : FGL) (e : ZiskInstExtract) : ZiskRomMessage FGL

noncomputable def romMessageOfRaw (line : FGL) (raw : BitVec 32) : ZiskRomMessage FGL

/-- `addr` is the committed ROM layout: entry k sits at address `addr k`.
    `h_sorted` mirrors `rom.rs:205` (`keys().sorted()`) and makes `line` injective,
    so the `∀ j at pc(i)` selection in `h_prog` is determinate. -/
def ProgramBinding (trace : AcceptedZiskTrace n)
    (addr : Fin trace.programLength → FGL)
    (rawProgram : Fin trace.programLength → BitVec 32) : Prop :=
  (∀ k k', k < k' → (addr k).val < (addr k').val)
  ∧ ∀ k, trace.program k = romMessageOfRaw (addr k) (rawProgram k)
```

**Adds to trust surface.** Three named caller-supplied inputs: `rawProgram`, `addr`, and
`ProgramBinding`. Plus, per row, a **strengthened** `hLine` (see below).

**Removes from trust surface.** Per row, the five `h_prog` clauses of every `ProgramDecode_<op>`
(op, jmp1, jmp2, store_offset, flags = packFlags bits) plus the existential `bits` and its five
`h_bits_*` facts. These become computed. 63 arms × ~11 assumed equations → one shared certificate
plus one raw-word shape fact per row.

**The one honest new per-row premise.** June's `RawDecode_<op>` carried free `rd rs1 rs2 : Nat` with
no tie to the claim (`RawProgramBindingRegister.lean:196-211`), which was sound then because `h_prog`
had four register-independent clauses. Main's fifth clause
`store_offset = Transpiler.ind (regidx_to_fin c.rd)` breaks that. Two equivalent fixes; **prefer the
second**:
- add `hRd : rd = (regidx_to_fin c.rd).val` as a new field — visibly an extra premise; or
- **fold it into `hLine`**, i.e. state the premise as
  `rawProgram j = rawRType 32 (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0 (regidx_to_fin c.rd).val 0x33`.
  Now the per-row premise reads as one sentence — *"the raw word at this pc is the encoding of this
  claim"* — with no extra field.

Either way this is a **reduction, not a removal**: a ROM-column equation is traded for a raw-word
bit-field equation. Report it in that column.

**Difficulty.** Moderate. `Totality.lean` and the sweep already exist; the new work is the
transcription + fidelity lemma, the inhabitation spike, the layout generalization, the `rd` binding,
`Fin n` → `Fin trace.programLength`, and the decode-indexed conclusion (§1.4).

**Honest failure mode.** Exactly what happened in June: a plausible-looking serialization that no
real ROM ever produces, yielding 63 green theorems over a false premise. §4.1 is the gate against it.

**Additional standing fidelity notes for the ledger.** (i) `extract_transpile_rv64im_raw` hard-codes
`rom_address := 0#u64` (`ProductionM2.lean:3660`); this is sound only because `rom_address` reaches
nothing but `ZiskInstBuilder::new(paddr)` (`:2164-2181`) and `insert_inst`'s discarded key
(`:2192-2200`) — assert with citations, and note that a future ZisK making any row field pc-dependent
would silently falsify the binding. (ii) The extraction runs under
`#[cfg(feature = "aeneas_extract")]` variants in `zisk/core/src/zisk_inst_builder.rs`; for ROM-relevant
fields these only drop debug strings and replace `nto32s(value as i128)` (`:109-122`) with a
numerically identical `>>32` / `&0xffffffff` split for `u64` inputs — but this is a standing surface,
and any new cfg divergence changes what the join proves.

### (d) Name it as a trust residual and scope #61 to what is reachable without it

**Sketch.** Status quo. `trust/envelope-burden-audit.md` already carries a bucket-(b) row
"Program binding and decode → Named `ProgramBinding`/decode premise".

**Adds/removes.** Nothing either way. **Difficulty.** Zero.

**Honest failure mode.** It is a legitimate *boundary* and an illegitimate *result*. Reporting it as
#61 progress is precisely what AGENTS.md's Anti-Laundering section forbids ("Do not claim issue
progress for … splitting scope"). Defensible only as the fallback if (c)'s inhabitation cannot be
established — and in that case the correct output is a blocker report naming the specific ROM entry
that cannot be produced from any raw word.

### 4.1 The spike that decides between (c) and (d)

The circular version of this test is worthless: if you *define* `program k := romMessageOfRaw (addr k) (rawProgram k)`,
then `ProgramBinding` holds by `rfl` and proves nothing. The test must run against a `program` built
independently.

**Use `SdLdSpinWitness`.** `ZiskFv/Compliance/SdLdSpinWitness.lean:283-291` defines
`sdLdProgram : Program 7` from seven hand-written `*ProgramRow` constants (lines `:122-130` for the SD
and LD entries), constructed to satisfy the ensemble constraints — *not* from any lowering. It
already contains a store and a load, i.e. exactly the family where both defects bite. Proving

```lean
theorem sdLdProgramBinding :
    ProgramBinding sdLdAcceptedTrace sdLdAddr sdLdRawProgram
```

for a concrete `sdLdRawProgram : Fin 7 → BitVec 32` and `sdLdAddr k = 4*k` is a genuine,
non-circular fidelity check, and it drops straight into the existing gate: check 15/18 globs
`trust/consistency/root_soundness_instantiation_*.lean` (`trust/scripts/check-all-semantic.sh:57-64, 96`).

Add a second, harder witness containing a **negative-offset** load (`ld a0, -8(sp)`), since the SD/LD
witness's `b_offset_imm0` values are `0` and `2` (`:123, :128`) and would not exercise Defect 2.

**Kill criterion.** If the concrete `program` rows of an *honest* witness cannot be produced by
`romMessageOfRaw` from any raw word — after `serializeExtract` is corrected against `rom.rs` — then
either the witness is not a real transpiled program (fix the witness, or build a small honest one
from real ELF words) or the extracted lowerer diverges from the ROM emitter (a genuine fidelity
finding, and a blocker worth reporting on its own merits). In either case **stop and report; do not
proceed to the 63-arm sweep.**

**Second, cheap, high-value check.** Run the real Rust `compute_trace_rom` on a small transpiled
program and diff its `RomRomTraceRow` field values against the Lean `romMessageOfRaw` evaluation.
This is a test, not a proof, and it does not belong in the trust ledger as evidence — but it is the
thing that would have caught all three June defects in an afternoon.

---

## 5. Ranked recommendation

**(c) ≫ (a) > (d); (b) eliminated.**

Reasoning, made explicit:

1. **(b) is out on a proved fact**, not on difficulty. Two independent non-injectivity witnesses.
2. **(c) beats (a) on blast radius, not on strength.** They have the same mathematical content — an
   agreement certificate between the committed ROM and a raw program. (c) attaches it to a new
   additive endpoint; (a) attaches it to `AcceptedZiskTrace` and thereby to every existing witness
   and to #74. Since several of those witnesses are hand-built rather than transpiled, (a) creates
   direct pressure to weaken the field, which is the failure mode we most need to avoid.
3. **(c) beats (d) because (d) is not a result.** (d) is where we already are.
4. **(c) is mostly already written.** ~4.7k lines of kernel-sound Lean exist and reduce through the
   real production lowerer, which is already in-build. The remaining work is repair, one
   generalization, one re-target, and the inhabitation gate.

**Spike first, in this order:**

- **S1.** Land `Extraction/Totality.lean` alone. Independently valuable (it discharges the
  lowering-success side condition #111 and block-2 currently assume), no dependence on the defective
  serialization, smallest merge-conflict surface. This is a real win even if everything after it dies.
- **S2.** Write `romRowOf` as a cited line-by-line transcription of `rom.rs:204-260`, and prove
  `serializeExtract`-style agreement — i.e. keep two independently-written Lean definitions and prove
  them equal, so a transcription slip shows up as a failed proof rather than as silence.
- **S3.** The §4.1 inhabitation on `SdLdSpinWitness` **plus** a negative-offset load. Hard gate.

**What kills the approach:** S3 failing after S2 is correct — i.e. an honest, constraint-satisfying
committed ROM row that is provably not the lowering of any 32-bit word. Then `ProgramBinding` is not
a property of honest witnesses, (c) collapses to (d), and the right output is a blocker naming the
offending slot.

**What does *not* kill it:** heartbeat pressure in the sweep (the asset already carried
`maxHeartbeats 4000000`/`8000000`), or `romMessageOfRaw` being `noncomputable` (fine for a `Prop`).

---

## 6. Scope boundary vs #172

The join grounds the **ZisK** side only. #172 ("Ground the Sail side of `root_soundness` in the
committed raw program") owns the following, and pulling any of it in converts this work into that
blocked campaign:

1. **The Sail decode bridge** — `ext_decode (rawProgram (pc i)) = pure (instruction.RTYPE (c.r2, c.r1, c.rd, rop.SUB))`.
   #172 records why this is a separate campaign: `ext_decode = encdec_backwards`
   (`build/sail-lean/LeanRV64D/{DecodeExt,InstsEnd}.lean`) is **`noncomputable`**, ~70k lines, a
   deeply nested fall-through match with **state-dependent** guards (`currentlyEnabled Ext_M`), and
   `rfl` / `decide` / `native_decide` / `simp` all fail on it. There is no roundtrip lemma between
   `encdec_forwards` and `encdec_backwards` anywhere in the tree.
2. **The Sail-side operand binding** — `c.r2 = encdec_reg_backwards (extractLsb W 24 20)`, which
   needs a Sail↔Aeneas register-decode agreement lemma.
   *In scope here, and do not confuse the two:* the **ZisK-side** analogue
   (`regidx_to_fin c.rd` vs. the raw word's `rd` bit-field) is forced by main's fifth `h_prog` clause
   and is a pure bit-field equation with no Sail content. That one belongs to #61.
3. **"`rawProgram` is the intended RISC-V binary"** — the compile/commitment boundary. Not
   Lean-provable; document-only.

**Also not closed by (c), and a residual rather than an omission:** even with the `addr` layout map,
"entry `k` sits where the binary places word `k`" is `addr`'s *meaning*, not a theorem. The layout
map converts a silent gap into a named premise and buys `line` injectivity; it does not close the
program-image pillar. Say so in the ledger.

---

## 7. Revised #61 Phase-0 checklist (paste-ready)

```markdown
### #61 Phase 0 — the raw-word join (revised 2026-07-28)

Route (c): bind the committed ROM to a raw program through the already-extracted
production transpiler. Additive endpoint only — `root_soundness` and
`AcceptedZiskTrace` are NOT modified.

Recover the June asset onto a work branch WITHOUT trusting it:
  git checkout a16bd97c -- \
    ZiskFv/Compliance/TraceLevelExport/RawProgramBinding*.lean \
    ZiskFv/Compliance/TraceLevelExport/RawRowDecode.lean \
    ZiskFv/Compliance/AeneasBridgeTrust/Extraction/Totality.lean

- [ ] **P0-1 (independent win, land alone).** `Extraction/Totality.lean`: the lowerer
      SUCCEEDS for symbolic in-range registers. Discharges the side condition #111's
      static pins and block-2's dynamic pins currently assume. No dependence on the
      serialization. Green under `lake build` + `check-extraction-closure`.

- [ ] **P0-2 (fidelity, gates everything after it).** Write `romRowOf` as a
      LINE-BY-LINE transcription of `zisk/state-machines/rom/src/rom.rs:204-260`,
      each field carrying its rom.rs line in a comment:
        - `b_src_ind` from the EXTRACTED constant `zisk_inst.SRC_IND`
          (`ProductionM2.lean:2704` = 5) — never a literal (June used `3` = SRC_STEP);
        - `a/b_offset_imm0` via the signed-i64 reinterpretation of `rom.rs:226-236`
          (June used the plain `UScalar.val : ℕ` cast);
        - `a/b_imm1` gated on `a/b_src == SRC_IMM` per `rom.rs:240-244`.
      Prove agreement against the salvaged `serializeExtract` so a transcription slip
      fails a proof instead of passing silently.

- [ ] **P0-3 (side lemma for the gating).** On the `lower_rv64im_single_row_input`
      path, `a_src ≠ SRC_IMM → a_use_sp_imm1 = 0` (and the b-side). Setters to cover:
      `src_a_reg`, `src_b_reg`, `src_b_lastc` (`ProductionM2.lean:2240-2254`),
      `src_b_ind` with `use_sp = false` (`:2726-2737`).

- [ ] **P0-4 (layout).** State the binding with an explicit ROM layout:
        ProgramBinding trace addr rawProgram :=
          (∀ k k', k < k' → (addr k).val < (addr k').val)     -- rom.rs:205 sorted keys
          ∧ ∀ k, trace.program k = romMessageOfRaw (addr k) (rawProgram k)
      This closes the `line` slot June left free and makes `line` injective, so
      `h_prog`'s `∀ j at pc(i)` selection is determinate. Index by
      `Fin trace.programLength` (main's dependent field), not `Fin numInstructions`.

- [ ] **P0-5 (NON-VACUITY — HARD GATE, do BEFORE any per-op sweep).** Prove
      `ProgramBinding` inhabited on a committed program built INDEPENDENTLY of
      `romMessageOfRaw`. Target: `sdLdProgram` (`SdLdSpinWitness.lean:283-291`,
      hand-written rows, contains an SD and an LD). Add a second witness with a
      NEGATIVE-offset load (`ld a0, -8(sp)`) — the SD/LD witness's
      `b_offset_imm0` values (0 and 2) do not exercise the signed path.
      Land as `trust/consistency/root_soundness_instantiation_rawprogram_*.lean`
      so semantic check 15/18 picks it up automatically.
      **If this cannot be closed, STOP and report a blocker naming the ROM slot.
      Do not proceed.**

- [ ] **P0-5b (cheap external cross-check, not ledger evidence).** Run the real Rust
      `compute_trace_rom` on a small transpiled program; diff its `RomRomTraceRow`
      values against the Lean `romMessageOfRaw` evaluation.

- [ ] **P0-6 (re-target).** June's `RawRowDecode`/`rowDecode_of_rawRowDecode` target
      the RETIRED `RowDecode` shape. Replace with `RawProgramDecode` /
      `programDecode_of_rawProgramDecode` producing `ProgramDecode_<op>`
      (`TraceLevelExport/ProgramDecode.lean`), so main's `rowDecode_of_programDecode`
      is untouched.

- [ ] **P0-7 (the NEW fifth h_prog clause).** Close
      `(program j).store_offset = Transpiler.ind (regidx_to_fin c.rd)`, which did not
      exist in June. Derive `msg.store_offset = (decoded.rd : FGL)` through
      `store_reg` (`ProductionM2.lean:2009-2069`; note the `offset = 0` early return
      leaves `store_offset = 0`, matching `Transpiler.ind 0 = 0`), and PIN the raw
      word's rd bit-field to the claim by folding it into `hLine` rather than adding a
      new field. REPORT HONESTLY: this trades a ROM-column equation for a raw-word
      bit-field equation — a reduction, not a free win.

- [ ] **P0-8 (63-arm sweep).** Family by family — register / immediate / shift /
      load-store / branch / control-UType / copyb / M-ext — rebuilding each
      `transpile_<op>` on the CORRECTED serialization. One commit per family, each
      green under `lake build`. Expect `maxHeartbeats 4000000`/`8000000`.

- [ ] **P0-9 (gate coverage).** Add `ZiskFv.Compliance.RawProgramBinding` to
      `extractionNamespaces` (`bin/TrustGate/Main.lean:344-345`, currently
      `[ZiskFv.Compliance.Extraction, ZiskFv.Compliance.Decode]`) so
      `check-extraction-closure` (18/18) covers the new bridges, as `a16bd97c` did.

- [ ] **P0-10 (additive endpoint).** Add `root_soundness_rawProgram` to
      `ZiskFv/Soundness.lean`: same binders as `root_soundness` EXCEPT
      `programDecodes` replaced by `addr` + `rawProgram` + `hbind : ProgramBinding` +
      `rawProgramDecodes`; body delegates to `root_soundness`.
      **PR #293 wrinkle:** the conclusion is now decode-indexed
      (`StepSound … (rowDecode_of_programDecode … )`), so the endpoint's conclusion is
      indexed by the DERIVED decode. Irrelevant for 62 arms
      (`| other, _ => StepSoundWithoutDecode`); for JALR the index is genuinely
      consumed (`Pilot.execRowAt ziskTrace decode.rows.finish`, Dispatcher.lean:1220-1227)
      and needs either the derived-index statement or an explicit row-range agreement
      lemma. Do NOT modify `root_soundness` or `AcceptedZiskTrace`.

- [ ] **P0-11 (ledger).** Rewrite the `fe7d353c` draft entry in `trust/trusted-base.md`.
      It MUST name three residuals, none of which this work closes:
        (1) `addr` is caller-supplied — "entry k sits where the binary places word k"
            is its MEANING, not a theorem (the program-image / pc-layout pillar);
        (2) the Sail-side `W → ext_decode` bridge is #172;
        (3) "`rawProgram` is the intended binary" is the document-only
            compile/commitment boundary.
      It MUST NOT repeat the draft's claim "Non-vacuous: ProgramBinding holds because
      the ROM is its serialized lowering" unless P0-5 actually landed; cite P0-5's
      witness by name instead. Add the two standing fidelity notes: the hard-coded
      `rom_address := 0#u64` (`ProductionM2.lean:3660`, sound only because rom_address
      reaches nothing but paddr and a discarded key) and the
      `#[cfg(feature = "aeneas_extract")]` divergence surface.
      Also update `trust/envelope-burden-audit.md`'s "Program binding and decode" row.

- [ ] **P0-12 (gates, exact counts).** `lake build`; then `trust/scripts/check-all.sh`
      (17 checks); then `trust/scripts/check-all-semantic.sh` (18 checks). Confirm 0 new
      project axioms via the V2 export closure. Report observed counts, never assumed.

**Explicitly OUT of scope (belongs to #172):** `ext_decode` / `encdec_backwards`;
the Sail-side operand binding `c.r2 = encdec_reg_backwards (extractLsb W 24 20)`;
any claim that `rawProgram` is the intended binary.

**Tracker hygiene (bookkeeping only — claims NO progress):** #159 is CLOSED/COMPLETED
and #172's body asserts `root_soundness_rawProgram` landed via PRs #167→#168→#170, but
no such theorem exists on main and PR #170's body says it "no longer closes #159".
Worth correcting so the next reader is not misled about what is already proved.
```

---

## 8. Drafted replacement body for issue #61 — **DO NOT APPLY** (draft only)

> The current body quotes the pre-2026-06-25 signature (`rowDecodes : RowDecode`, a
> `RowOutsideDefectRegion` taking `sailTrace`/`inputsAgree`, no `bootSeed`, a non-indexed
> conclusion). The text below is verified against `git show origin/main:ZiskFv/Soundness.lean`
> at `2da97416`.

```markdown
## Current state (2026-07-28)

The original `OpEnvelope` construction gap is closed and the per-row residual bundle has been
split into named sub-burdens, but the decode is still not grounded in the program image. The
live headline is `ZiskFv.Compliance.root_soundness` in `ZiskFv/Soundness.lean`:

```lean
theorem root_soundness
    (numInstructions : Nat)
    (ziskTrace  : AcceptedZiskTrace numInstructions)
    (sailTrace  : SailTrace numInstructions)
    (ziskStep   : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (programDecodes : ∀ i : Fin numInstructions, ProgramDecode ziskTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin numInstructions, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i : Fin numInstructions,
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i (programDecodes i))
```

Changes since this issue was last edited:

- **`rowDecodes : RowDecode` → `programDecodes : ProgramDecode`** (PR #170). The witness row's
  decode columns are no longer assumed: they are DERIVED from program-level facts about the
  COMMITTED ROM `trace.program` via the in-circuit lookup (`rowDecode_of_programDecode`).
- **`bootSeed : BootSegmentMemorySeed`** is now a single named cross-row memory-seed binder
  (#185/PR #224), replacing the ten per-op memory residuals. Driving it to zero is #115 / #119.
- **`RowOutsideDefectRegion ziskTrace i (ziskStep i)` is now row-local** — it no longer takes
  `sailTrace` or `inputsAgree`.
- **The conclusion is decode-indexed** (PR #293): `StepSound` takes the checked `RowDecode` as an
  index. JALR genuinely consumes it (one architectural instruction may occupy an aligned singleton
  Main row or an unaligned pair); the other 62 arms fall through to `StepSoundWithoutDecode`.
- `AcceptedZiskTrace` now carries `programLength` as a dependent field: the committed ROM may be
  longer than the executed trace, and loops may execute more steps than the ROM has entries.
- `zisk_riscv_compliant_program_bus` (`ZiskFv/Compliance.lean`) remains the internal
  channel-balance theorem consumed by the per-op `stepStrong_<op>` steps. It is not the headline.

## What the per-row witnesses still carry

- **`ziskStep` (`Claim_<op>`)** — which RV64IM op the row decoded to, plus that op's operand /
  destination register indices.
- **`programDecodes` (`ProgramDecode_<op>`)** — the structural `h_idx`, an existential `RomFlagBits`
  with its `h_bits_*` pins, and `h_prog`: for every ROM entry at this row's pc, five equations on
  the committed message (`op`, `jmp_offset1`, `jmp_offset2`, `store_offset`, `flags`), plus the
  unchanged non-ROM operand witnesses. **These are the target of Phase 0 below.**
- **`inputsAgree` (`Inputs_<op>`)** — cross-world register / PC / memory agreement, plus placement
  and store-RMW facts that should ultimately be derived (#141, #119).
- **`bootSeed`** — the segment's initial memory state plus one memory-evolution chain (#115, #119).
- **`hAvoidKnownBugs`** — row-local known-defect exclusion; #151 tracks the remaining fidelity work.

## Remaining problem — Phase 0: the raw-word join

`programDecodes` is a statement about `trace.program`, an eleven-field-element-per-instruction
*lowered* object the prover chooses freely: `romStaticTable.Spec msg := ∃ i, msg = program i`
(`ZiskFv/AirsClean/ZiskInstructionRom.lean:63`) checks membership only. So "the committed program
decodes as SUB at this pc" is still an assumption about a prover-chosen table, not about a binary.

Phase 0 closes the ZisK half of that gap by binding `trace.program` to a raw RISC-V program through
ZisK's **real, already-Aeneas-extracted** production transpiler:

  `rawProgram(k) → decode_32_core → lower_rv64im_single_row_input → serialize → trace.program k`

The lowering is `aeneas_extract.extract_transpile_rv64im_raw` (`trust/aeneas/ProductionM2.lean:3645`),
already in the Lake build graph via the `ProductionM2` lean_lib, and calling the same entry point the
production ELF transpiler uses. The serialization target is `compute_trace_rom`
(`zisk/state-machines/rom/src/rom.rs:204-260`).

Approximately 4.7k lines of kernel-sound Lean for this exist unmerged at `a16bd97c` (see PR #170's
body: the grounding was re-scoped out, "machinery preserved in this PR's git history"). It must NOT
be re-landed as-is: its serialization has three confirmed fidelity defects (the `SRC_IND` constant
written as literal `3` instead of `5`; an unsigned `Nat` cast where `rom.rs:226-236` uses a signed
`i64` reinterpretation; ungated `a/b_imm1`), which make its `ProgramBinding` premise FALSE for any
program containing a load or store — i.e. 63 green theorems over an unsatisfiable premise.

**Non-vacuity is therefore a hard gate, not a nicety:** the binding must be exhibited on a committed
program built independently of the lowering (`sdLdProgram`, `ZiskFv/Compliance/SdLdSpinWitness.lean:283-291`,
whose LD row already sets `b_src_ind := true`), including at least one negative-offset load.

Additionally, the binding must pin the ROM layout. The unmerged version fed each message its own
`line` back in, so it constrained ten of eleven slots and said nothing about where entry `k` sits.

## Active child work

- **#172** — ground the **Sail** side in the same raw word (`ext_decode (rawProgram (pc i)) = …`).
  Separate campaign: `encdec_backwards` is `noncomputable`, ~70k lines, with state-dependent guards
  and no roundtrip lemma. Complementary to Phase 0; must not be pulled into it.
- **#141** — derive each op's effect placement (dest reg / store address / nextPC) from the Main AIR.
- **#74** — concrete end-to-end instantiation witnesses on a real ZisK trace.
- **#115 / #119** — drive `bootSeed` and the store RMW residual to zero.
- **#151** — Arith range-table fidelity for the signed-defect witness.
- **#111** (landed, standalone) — all 63 RV64IM *static* decode pins proven in-build, kernel-soundly,
  from the real Aeneas lowering. Their lowering-SUCCESS side condition is still assumed; the unmerged
  `Extraction/Totality.lean` proves it and should land first, on its own.

## Success criteria

- The theorem surface relies on no caller-supplied `OpEnvelope`, and `programDecodes` is derived from
  a raw program image rather than assumed on the committed ROM.
- Remaining public premises are named and defensible, each with an explicit residual statement:
  the Sail trace / state relation (`inputsAgree` core); the raw-program binding and its ROM layout
  map; the boot / cross-row memory seed; known-defect exclusions.
- `root_soundness`, `zisk_riscv_compliant_program_bus`, and the 63 canonical `equiv_<OP>` theorems
  keep zero `ZiskFv.*` project axioms in their audited closures (gated by
  `trust/generated/baseline-strong-export-closure.txt`, `baseline-zisk-riscv-compliant.txt`,
  `baseline-equiv-axiom-deps.txt`).
- Every premise added by Phase 0 is exhibited as inhabited on a concrete accepted trace, checked by
  `trust/scripts/check-all-semantic.sh` (check 15/18 auto-globs
  `trust/consistency/root_soundness_instantiation_*.lean`).
```

---

## 9. What I proved vs. changed vs. hypothesize

**Verified by reading primary sources** (all citations above): the extraction exists, is in-build,
and calls the production lowerer; the exact current `root_soundness` signature and its decode-indexed
conclusion; all three serialization defects and their Rust ground truth; the non-injectivity of the
lowering; the `h_prog` fifth-clause drift; `UScalar.val : ℕ` vs `IScalar.val : ℤ`; `IScalar.hcast`
sign-extension; `SRC_IND = 5` / `SRC_STEP = 3`; the 17/18 gate check counts; the unmerged asset's
exact file list and line counts; the absence of `root_soundness_rawProgram` from main.

**Changed:** nothing. No file edits, no commits, no branch.

**Hypothesized, not proved** (flagged so nobody treats it as established):
- That `ProgramBinding` **is** satisfiable on `sdLdProgram` once the serialization is corrected. I did
  not attempt the proof. `sdLdSdProgramRow.b_offset_imm0 = 2` (`SdLdSpinWitness.lean:123`) is not
  obviously the sign-extended immediate of any S-type word, so it is entirely possible the spin
  witness is not a transpiled program at all. That is exactly what P0-5 is for, and it is the single
  most important unknown in this document.
- The difficulty estimate for the 63-arm sweep on the corrected serialization. The bridges I read
  (`register_decode_fields_of_binding`, the load/store macro) do not touch the two broken offset
  slots, so I expect them to port largely unchanged — but I did not compile anything.
