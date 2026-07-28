import Extraction.Main
import ZiskFv.AirsClean.Main.Circuit

/-!
# Machine-checked weld: Main constraint mirror ↔ generated extraction

`ZiskFv/AirsClean/Main/Constraints.lean` asserts a handwritten mirror of the
Main AIR's row-local constraints, and `ZiskFv/AirsClean/Main/Spec.lean` /
`ZiskFv/AirsClean/Main/Circuit.lean` publish the predicates the opcode proofs
consume. Their correspondence to `build/extraction/Extraction/Main.lean` — the
machine-produced ground truth — was asserted only by comments. A mistyped
column or a dropped factor compiles fine and silently proves soundness of a
circuit that is not ZisK's.

This module replaces the comment citation with compiled identities.

## How the weld works

`Main.extraction.constraint_N_every_row` is stated against the abstract
`Extraction.Circuit` interface: its body only ever mentions
`Extraction.Circuit.main c (id := 1) (column := k) (row := r) (rotation := 0)`
and the `preprocessed` / `challenge` / `exposed` lanes. `ExtractedMainRow`
below is an `Extraction.Circuit` instance whose stage-1 column `k` reads field
`k` of a `MainRowWithRom`, using the column layout printed by the extractor at
`build/extraction/Extraction/Main.lean:13-59`. Instantiating a generated
constraint at that circuit turns it into a polynomial over `MainRowWithRom`
fields, and the weld theorems say that polynomial is *definitionally* the one
the mirror asserts.

## Coverage: 29 of the 144 generated constraints

`Extraction/Main.lean` defines `constraint_0_every_row` …
`constraint_143_every_row`. They partition by their PIL source comment:

* `0`–`38` (39) are the Main AIR's own constraints, sourced `main/pil/main.pil`;
* `39`–`143` (105) are logup bookkeeping, sourced `std_sum.pil`. Every one of
  those reads `Extraction.Circuit.challenge` (`std_gamma`) and/or the stage-2
  (`id := 2`) columns `gsum` / `im_cluster` / `im_single`, or the `exposed`
  `im_direct` lanes. They are represented in the Clean component by channel
  `emit` / `lookup` operations, never by `assertZero`, so there is nothing in
  the mirror to weld them to. This is the same structural exclusion as Arith's
  stage-2 set.

Of the 39, exactly 29 are pure stage-1 row-local (`id := 1`, `rotation := 0`,
`row := row`, no `preprocessed` / `exposed`): `1`, `2`, `5`–`8`, `11`–`17`,
`22`–`37`. All 29 are welded below, and every weld is an `Iff`.

The other 10 are **not** welded, individually because:

* `0` — `exposed(0) * (1 - exposed(0))` (`main_last_segment` booleanity). Reads
  no row column at all; there is no mirror counterpart anywhere in `ZiskFv/`.
* `3`, `9` — a-side C-copy `((1 - a_src_mem) - a_src_imm - a_src_reg) *
  (a[i] - previous_c)` (`main.pil:385`), reading `preprocessed(0)`,
  `exposed(3+i)` and `c[i]` at `row - 1`. `ZiskFv/` has no counterpart at all:
  `sourceCCopyBetween` (`Main/Circuit.lean:721`) covers only the *b*-side
  selector `1 - b_src_mem - b_src_imm - b_src_ind - b_src_reg`, and the legacy
  `Valid_Main` enumeration likewise stops at `b_src_c_copies_prev_c0` /
  `b_src_c_copies_prev_c1` (`ZiskFv/Airs/Main/Main.lean:139,147`). Recorded as a
  mirror-coverage gap; not fixed here, because inventing the missing mirror
  clause is a modelling decision, not a transcription fix.
* `4`, `10` — b-side C-copy (`main.pil:386`). `sourceCCopyBetween`'s own
  docstring (`Main/Circuit.lean:715-720`) states it is a deliberate
  specialization that drops the `__L1__`-selected public-input branch, so the
  best available relation is `generated → mirror`, never an `Iff`.
* `18` — pc handshake (`main.pil:410`). `pcHandshakeBetween`
  (`Main/Circuit.lean:708`) reproduces the polynomial but substitutes the
  witness field `core.segment_l1` for the generated `preprocessed (column := 0)`
  (`SEGMENT_L1`). That substitution is backed by `mainFixedColumns`
  (`Main/Circuit.lean:768`), which maps slot 17 to fixed column 0 — so this is
  *not* a claimed defect — but it is not an `Iff.rfl` fact, and it is a two-row
  constraint needing a two-row bridge this module does not build.
* `19`, `20`, `21` — segment-final constraints at rotation `row + 1`
  (`main.pil:423,426`), reading `preprocessed(0)@r+1` and `exposed(5/6/7)`. No
  mirror counterpart.
* `38` — `preprocessed(0) * (exposed(2) - pc)` (`main.pil:508`). No mirror
  counterpart.

## What the weld does and does not certify

* It certifies, by `Iff.rfl` (modulo a `simp only` that only renormalizes
  `a + -b` ↔ `a - b` and `x - y = 0` ↔ `x = y` — see each proof), that the four
  mirror predicates `Spec`, `RomBoolSpec`, `SourceSpec` and the
  generated-backed slice of `AddressSpec` are, conjunct for conjunct, the 29
  generated polynomials — same columns, same coefficients, same shape.
* The tie is to the *live* assertion list, not to retyped prose:
  `extracted_of_mainWithRomAndMemBus_constraints` derives all 29 generated
  constraints from `Operations.ConstraintsHold` on
  `(mainWithRomAndMemBus length program row).operations`, i.e. from the
  `assertZero` calls the component actually makes. A slip that is
  self-consistent across the `Spec` predicate, the `assertZero` expression and
  the projection proof — the exact failure this module exists to catch — breaks
  the weld and nothing else.
* Two of `mainWithRom`'s 31 `assertZero`s have **no** generated counterpart:
  `addr0 - a_offset_imm0` and `addr2 - (store_offset + store_ind * a[0])`
  (`Main/Constraints.lean:268,270`). This is not a mirror bug: `addr0` and
  `addr2` are not AIR witness columns (the generated stage-1 header lists 38
  columns and only `addr1`, column 29, is among them), because PIL inlines
  those two address expressions into the memory-bus emission instead of
  committing them. They pin mirror-only witnesses, so the mirror is *stronger*
  than the AIR there, in the direction that is safe for soundness.
* `RomBoolSpec` (`Main/Circuit.lean:346`) had, before this module, no consumer
  anywhere in `ZiskFv/` — it was a published predicate nothing checked against
  anything. `romBoolSpec_weld` and
  `romBoolSpec_row_of_mainWithRomAndMemBus_constraints` are now its only uses,
  and both pin it to the extraction.
* It does **not** certify the column layout itself: `mainValue` is handwritten
  from the generated header. Nothing on this branch pins it. A *compensating*
  pair of slips — mirror and column map wrong in the same direction — would
  still be `rfl`. Arith closes that with
  `trust/scripts/check-arith-column-map.py`; a Main analogue is gate wiring and
  is deliberately not added here.
* It does **not** rest on `mainValue`'s `0` answers outside the modeled lanes,
  nor on the `preprocessed` / `challenge` / `exposed` stubs. That is checked for
  all 29 by `weldedConstraints_readOnlyModeledLanes` and
  `weldedConstraints_probeBridge`, not assumed; see "Which lanes a welded
  constraint is allowed to read".

## Trust note

No axiom, `sorry`, `native_decide`, or other trust marker is added. Every weld
below reduces to `Iff.rfl` after a notation-only `simp only`.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- An `Extraction.Circuit` whose stage-1 columns are the fields of a single
    `MainRowWithRom`. Only used to instantiate the generated `Main` constraint
    predicates at the mirror's row type. -/
structure ExtractedMainRow (F ExtF : Type) where
  row : MainRowWithRom FGL

/-- Main AIR stage-1 column layout, transcribed from the generated header
    `build/extraction/Extraction/Main.lean:13-59` (`stage 1 col N: <name>`).

    This is the *only* handwritten datum the weld introduces. The 38 generated
    stage-1 columns land injectively in `MainRowWithRom`'s 43 slots; the five
    slots with no generated column are `core.im_high_degree_2`,
    `core.segment_l1` (a fixed column, not a witness — see `mainFixedColumns`),
    `rom.addr0`, `rom.addr2` and `rom.main_step`.

    Stage 2 (`gsum`, `im_cluster`, `im_single`) is not modeled: the generated
    constraints that read stage-2 columns (`constraint_39` … `constraint_143`)
    mix in `Extraction.Circuit.challenge` and are represented in the Clean
    component by channel `emit` / `lookup` operations, not by `assertZero`. -/
@[reducible]
def mainValue (c : ExtractedMainRow FGL FGL) (id column _row _rotation : ℕ) : FGL :=
  if id = 1 then
    match column with
    | 0 => c.row.core.a_0
    | 1 => c.row.core.a_1
    | 2 => c.row.core.b_0
    | 3 => c.row.core.b_1
    | 4 => c.row.core.c_0
    | 5 => c.row.core.c_1
    | 6 => c.row.core.flag
    | 7 => c.row.core.pc
    | 8 => c.row.rom.a_src_imm
    | 9 => c.row.rom.a_src_mem
    | 10 => c.row.rom.a_offset_imm0
    | 11 => c.row.rom.a_imm1
    | 12 => c.row.rom.is_precompiled
    | 13 => c.row.rom.b_src_imm
    | 14 => c.row.rom.b_src_mem
    | 15 => c.row.rom.b_offset_imm0
    | 16 => c.row.rom.b_imm1
    | 17 => c.row.rom.b_src_ind
    | 18 => c.row.core.ind_width
    | 19 => c.row.core.is_external_op
    | 20 => c.row.core.op
    | 21 => c.row.core.store_pc
    | 22 => c.row.rom.store_mem
    | 23 => c.row.rom.store_ind
    | 24 => c.row.rom.store_offset
    | 25 => c.row.core.set_pc
    | 26 => c.row.core.jmp_offset1
    | 27 => c.row.core.jmp_offset2
    | 28 => c.row.core.m32
    | 29 => c.row.rom.addr1
    | 30 => c.row.rom.a_reg_prev_mem_step
    | 31 => c.row.rom.b_reg_prev_mem_step
    | 32 => c.row.rom.store_reg_prev_mem_step
    | 33 => c.row.rom.store_reg_prev_value_0
    | 34 => c.row.rom.store_reg_prev_value_1
    | 35 => c.row.rom.a_src_reg
    | 36 => c.row.rom.b_src_reg
    | 37 => c.row.rom.store_reg
    | _ => 0
  else
    0

instance extractedMainRowCircuit : Extraction.Circuit FGL FGL ExtractedMainRow where
  main := mainValue
  preprocessed := fun _ _ _ _ => 0
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

/-- The generated constraints read cells through the `Extraction.Circuit.main`
    class projection, never through `mainValue` by name. This says the two
    coincide *at the instance the welds below resolve*, so a rebinding of
    `extractedMainRowCircuit.main` to anything but `mainValue` — the hole that
    a column-map gate reading only `mainValue` would leave open — is a
    compile error here, before any weld is stated.

    `extractedMainRowCircuit_pinned` at the end of the module pins the
    remaining three fields and re-checks this one after all welds have
    resolved their instance. -/
theorem extractedMainRowCircuit_main_eq
    (c : ExtractedMainRow FGL FGL) (id column r rotation : ℕ) :
    Extraction.Circuit.main c (id := id) (column := column) (row := r)
        (rotation := rotation)
      = mainValue c id column r rotation :=
  rfl

@[reducible]
def extractedMainRow (row : MainRowWithRom FGL) : ExtractedMainRow FGL FGL := ⟨row⟩

/-! ## Welds, spelled out

Four constraints are written longhand first, one per shape, so the identity is
readable as source against source. The predicate-level welds that follow cover
all 29 without restating every polynomial. -/

/-- `main/pil/main.pil:459 flag*(1-flag)`.

    Mirror: the first conjunct of `Spec`, asserted by `Constraints.main`. -/
theorem constraint_22_weld (row : MainRowWithRom FGL) :
    (row.core.flag * (1 - row.core.flag) = 0)
      ↔ Main.extraction.constraint_22_every_row (extractedMainRow row) 0 :=
  Iff.rfl

/-- `main/pil/main.pil:393 ((1-is_external_op)*(1-op))*c[0]` — the internal-op
    result-zeroing constraint, three lanes and the PIL association.

    Mirror: the third conjunct of `Spec`. -/
theorem constraint_7_weld (row : MainRowWithRom FGL) :
    ((1 - row.core.is_external_op) * (1 - row.core.op) * row.core.c_0 = 0)
      ↔ Main.extraction.constraint_7_every_row (extractedMainRow row) 0 :=
  Iff.rfl

/-- `main/pil/main.pil:192 addr1-(b_offset_imm0+(b_src_ind*a[0]))` — the
    indirect b-operand address, the one address witness ZisK actually commits.

    Mirror: `Constraints.lean:269`'s `assertZero`, and the second conjunct of
    `AddressSpec` after `sub_eq_zero`. -/
theorem constraint_1_weld (row : MainRowWithRom FGL) :
    (row.rom.addr1 - (row.rom.b_offset_imm0 + row.rom.b_src_ind * row.core.a_0) = 0)
      ↔ Main.extraction.constraint_1_every_row (extractedMainRow row) 0 :=
  Iff.rfl

/-- `main/pil/main.pil:197 (store_ind+b_src_ind)*a[1]` — the indirect-addressing
    high-limb overflow guard.

    Mirror: the fourth conjunct of `AddressSpec`, `Constraints.lean:271`. -/
theorem constraint_2_weld (row : MainRowWithRom FGL) :
    ((row.rom.store_ind + row.rom.b_src_ind) * row.core.a_1 = 0)
      ↔ Main.extraction.constraint_2_every_row (extractedMainRow row) 0 :=
  Iff.rfl

/-! ### The mirror predicates, welded

These restate the above against the actual predicates the Main component
publishes, so the weld breaks if either the predicate or the generated file
drifts. Between them they cover all 29 row-local generated constraints:
9 + 14 + 4 + 2. -/

/-- `main.pil:393,396,401,404,407,459,472` — the nine core Main constraints
    `Constraints.main` asserts. -/
theorem spec_weld (row : MainRowWithRom FGL) :
    Spec row.core ↔
      (Main.extraction.constraint_22_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_28_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_7_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_13_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_8_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_14_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_15_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_16_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_17_every_row (extractedMainRow row) 0) :=
  Iff.rfl

/-- `main.pil:467-481` — the fourteen `rom_flags` booleanity pins beyond the two
    (`flag`, `is_external_op`) already in `Spec`.

    `RomBoolSpec` writes each factor as `1 + -x` where the extractor emits
    `1 - x`; `← sub_eq_add_neg` renormalizes the mirror's notation and nothing
    else. That step is load-bearing, not decoration: `Iff.rfl` against the
    `1 + -x` form is rejected. -/
theorem romBoolSpec_weld (row : MainRowWithRom FGL) :
    RomBoolSpec row ↔
      (Main.extraction.constraint_33_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_32_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_29_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_23_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_24_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_25_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_26_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_27_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_30_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_31_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_34_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_35_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_36_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_37_every_row (extractedMainRow row) 0) := by
  simp only [RomBoolSpec, ← sub_eq_add_neg]
  exact Iff.rfl

/-- `main.pil:389-390` — the four immediate-source lane equations.

    `SourceSpec` writes `x + -1 * y` where the extractor emits `x - y`;
    `neg_one_mul` and `← sub_eq_add_neg` renormalize the mirror's notation and
    nothing else. -/
theorem sourceSpec_weld (row : MainRowWithRom FGL) :
    SourceSpec row ↔
      (Main.extraction.constraint_5_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_11_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_6_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_12_every_row (extractedMainRow row) 0) := by
  simp only [SourceSpec, neg_one_mul, ← sub_eq_add_neg]
  exact Iff.rfl

/-- `main.pil:192,197` — the two `AddressSpec` clauses that have a generated
    counterpart.

    `AddressSpec`'s other two clauses (`addr0 = a_offset_imm0`,
    `addr2 = store_offset + store_ind * a[0]`) have none, because `addr0` and
    `addr2` are not AIR witness columns: PIL inlines both expressions into the
    memory-bus emission rather than committing them. They are mirror-only
    witness pins, so the mirror is strictly stronger than the AIR there.

    `sub_eq_zero` crosses `AddressSpec`'s `x = y` phrasing against the
    extractor's `x - y = 0`; the polynomials themselves are unchanged. -/
theorem addressSpec_generatedSlice_weld (row : MainRowWithRom FGL) :
    (row.rom.addr1 = row.rom.b_offset_imm0 + row.rom.b_src_ind * row.core.a_0
      ∧ (row.rom.store_ind + row.rom.b_src_ind) * row.core.a_1 = 0) ↔
      (Main.extraction.constraint_1_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_2_every_row (extractedMainRow row) 0) := by
  simp only [Main.extraction.constraint_1_every_row,
    Main.extraction.constraint_2_every_row, sub_eq_zero]
  exact Iff.rfl

theorem addressSpec_weld (row : MainRowWithRom FGL) :
    AddressSpec row →
      (Main.extraction.constraint_1_every_row (extractedMainRow row) 0
      ∧ Main.extraction.constraint_2_every_row (extractedMainRow row) 0) :=
  fun h => (addressSpec_generatedSlice_weld row).mp ⟨h.2.1, h.2.2.2⟩

/-! ### From the live assertion list

Everything above welds a *predicate*. These project the same facts out of the
`assertZero` calls `mainWithRomAndMemBus` actually makes, so a drift in the
`assertZero` expressions — not just in the published predicates — is a build
failure.

`romBoolSpec_of_mainWithRomAndMemBus_constraints`,
`addressSpec_of_mainWithRomAndMemBus_constraints` and
`sourceSpec_of_mainWithRomAndMemBus_constraints` (`Main/Circuit.lean:397,435,
481`) already do this for 20 of the 29. `spec_of_mainWithRomAndMemBus_constraints`
below is the missing projection for the nine core constraints. -/

/-- The nine core `Constraints.main` `assertZero`s, projected to the evaluated
    row as `Spec`. -/
theorem spec_of_mainWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomAndMemBus length program row).operations offset)) :
    Spec (eval env row).core := by
  simp only [mainWithRomAndMemBus, mainWithRom, main, circuit_norm] at h_holds
  have h0 := h_holds.1 (row.core.flag * (1 - row.core.flag)) (by simp)
  have h1 := h_holds.1 (row.core.is_external_op * (1 - row.core.is_external_op)) (by simp)
  have h2 := h_holds.1
    ((1 - row.core.is_external_op) * (1 - row.core.op) * row.core.c_0) (by simp)
  have h3 := h_holds.1
    ((1 - row.core.is_external_op) * (1 - row.core.op) * row.core.c_1) (by simp)
  have h4 := h_holds.1
    ((1 - row.core.is_external_op) * row.core.op * (row.core.b_0 - row.core.c_0)) (by simp)
  have h5 := h_holds.1
    ((1 - row.core.is_external_op) * row.core.op * (row.core.b_1 - row.core.c_1)) (by simp)
  have h6 := h_holds.1
    ((1 - row.core.is_external_op) * (1 - row.core.op) * (1 - row.core.flag)) (by simp)
  have h7 := h_holds.1
    ((1 - row.core.is_external_op) * row.core.op * row.core.flag) (by simp)
  have h8 := h_holds.1 (row.core.flag * row.core.set_pc) (by simp)
  -- `Expression.eval` turns the mirror's `1 - x` into `1 + -1 * x`; these two
  -- lemmas put it back, and change nothing else.
  simp only [Expression.eval, neg_one_mul, ← sub_eq_add_neg] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp only [Spec, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The fourteen `rom_flags` booleanity `assertZero`s, projected to the
    evaluated row as `RomBoolSpec`. -/
theorem romBoolSpec_row_of_mainWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomAndMemBus length program row).operations offset)) :
    RomBoolSpec (eval env row) := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
    romBoolSpec_of_mainWithRomAndMemBus_constraints length program row offset env h_holds
  simp only [Expression.eval, neg_one_mul, ← sub_eq_add_neg] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
  simp only [RomBoolSpec, ← sub_eq_add_neg, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]
  exact ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩

/-- All 29 row-local generated constraints, derived from the constraints
    `mainWithRomAndMemBus` asserts.

    This is the statement that makes the weld a check rather than a claim: the
    generated predicates on the right are `Extraction/Main.lean`'s own, and the
    only input on the left is that the mirror's `assertZero` list holds. -/
theorem extracted_of_mainWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomAndMemBus length program row).operations offset)) :
    (Main.extraction.constraint_22_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_28_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_7_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_13_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_8_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_14_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_15_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_16_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_17_every_row (extractedMainRow (eval env row)) 0)
    ∧ (Main.extraction.constraint_33_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_32_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_29_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_23_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_24_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_25_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_26_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_27_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_30_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_31_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_34_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_35_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_36_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_37_every_row (extractedMainRow (eval env row)) 0)
    ∧ (Main.extraction.constraint_5_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_11_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_6_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_12_every_row (extractedMainRow (eval env row)) 0)
    ∧ (Main.extraction.constraint_1_every_row (extractedMainRow (eval env row)) 0
      ∧ Main.extraction.constraint_2_every_row (extractedMainRow (eval env row)) 0) :=
  ⟨(spec_weld _).mp (spec_of_mainWithRomAndMemBus_constraints length program row offset env h_holds),
   (romBoolSpec_weld _).mp
     (romBoolSpec_row_of_mainWithRomAndMemBus_constraints length program row offset env h_holds),
   (sourceSpec_weld _).mp
     (sourceSpec_of_mainWithRomAndMemBus_constraints length program row offset env h_holds),
   addressSpec_weld _
     (addressSpec_of_mainWithRomAndMemBus_constraints length program row offset env h_holds)⟩

/-! ## Which lanes a welded constraint is allowed to read

`mainValue` is total, so it has to answer somewhere it is not modeling: it
returns `0` for every stage-2 read (`id ≠ 1`) and for every stage-1 column
`≥ 38`, and, ignoring its `row` and `rotation` arguments, it returns the same
cell at every trace row and every rotation. `extractedMainRowCircuit` stubs the
`preprocessed`, `challenge` and `exposed` lanes to `0` outright. Those answers
are only harmless if no welded constraint can observe them; if one could, the
weld would be certifying a polynomial the AIR does not assert. This section
checks that instead of asserting it.

`MainProbe` is the *free* `Extraction.Circuit`: every lane is an unconstrained
function field. Instantiating a generated constraint there turns each cell read
into an application of a variable, so a `rfl`-level identity between a probe
circuit and its restriction is a statement about which cells the generated body
mentions — not about their values. -/

/-- The free `Extraction.Circuit` over `FGL`: each lane is a function field. -/
structure MainProbe (F ExtF : Type) where
  mainCell : ℕ → ℕ → ℕ → ℕ → FGL
  preprocessedCell : ℕ → ℕ → ℕ → FGL
  challengeCell : ℕ → FGL
  exposedCell : ℕ → FGL

instance mainProbeCircuit : Extraction.Circuit FGL FGL MainProbe where
  main c := c.mainCell
  preprocessed c := c.preprocessedCell
  challenge c := c.challengeCell
  exposed c := c.exposedCell

/-- `c` cut down to the lanes `extractedMainRowCircuit` actually models: stage 1,
    columns `< 38`, rotation `0`, the single trace row `r`; `0` everywhere else,
    including all of `preprocessed`, `challenge` and `exposed`. -/
@[reducible]
def restrictToModeledLanes (c : MainProbe FGL FGL) (r : ℕ) : MainProbe FGL FGL where
  mainCell := fun id column _row rotation =>
    if id = 1 ∧ column < 38 ∧ rotation = 0 then c.mainCell id column r rotation else 0
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- `P c r` is unchanged by zeroing every lane `extractedMainRowCircuit` stubs.

    Unfolded: `P c r` may mention `c.mainCell 1 k r 0` for `k < 38` and nothing
    else. A read of a stage-2 column, of stage-1 column `≥ 38`, of a rotation
    other than `0`, of a trace row other than `r`, or of `preprocessed`,
    `challenge` or `exposed` would leave a free `c.<lane> …` on the left of the
    `Iff` with no counterpart on the right, and `Iff.rfl` would not typecheck. -/
@[reducible]
def ReadsOnlyModeledLanes (P : MainProbe FGL FGL → ℕ → Prop) : Prop :=
  ∀ (c : MainProbe FGL FGL) (r : ℕ), P c r ↔ P (restrictToModeledLanes c r) r

/-- Each of the 29 welded constraints reads only the lanes
    `extractedMainRowCircuit` models.

    The property is not vacuous. `ReadsOnlyModeledLanes` asserted of
    `constraint_0_every_row` (which reads only `exposed`) or of
    `constraint_38_every_row` (which reads `preprocessed` and `exposed`) fails
    to elaborate, with `Iff.rfl` rejected against the stated `Iff`. Both are
    among the 10 `main.pil`-sourced constraints this module does not weld; the
    module docstring enumerates them with reasons. -/
theorem weldedConstraints_readOnlyModeledLanes :
    ReadsOnlyModeledLanes Main.extraction.constraint_1_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_2_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_5_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_6_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_7_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_8_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_11_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_12_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_13_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_14_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_15_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_16_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_17_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_22_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_23_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_24_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_25_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_26_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_27_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_28_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_29_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_30_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_31_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_32_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_33_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_34_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_35_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_36_every_row
    ∧ ReadsOnlyModeledLanes Main.extraction.constraint_37_every_row :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl⟩

/-- `extractedMainRow row` re-expressed in the free circuit: `mainValue` in the
    stage-1 lane, `0` in every stub lane. -/
@[reducible]
def probeOfRow (row : MainRowWithRom FGL) : MainProbe FGL FGL where
  mainCell := mainValue (extractedMainRow row)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- The bridge from `extractedMainRowCircuit`, at which every weld above is
    stated, into the free circuit. Composed with
    `weldedConstraints_readOnlyModeledLanes` it gives: a welded constraint
    cannot observe a stubbed lane, so the `0` defaults in `mainValue` and the
    `preprocessed` / `challenge` / `exposed` stubs cannot be what makes a weld
    true.

    Instantiated at all 29 welded constraints, matching
    `weldedConstraints_readOnlyModeledLanes`. -/
theorem weldedConstraints_probeBridge (row : MainRowWithRom FGL) (r : ℕ) :
    (Main.extraction.constraint_1_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_1_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_2_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_2_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_5_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_5_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_6_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_6_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_7_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_7_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_8_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_8_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_11_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_11_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_12_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_12_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_13_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_13_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_14_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_14_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_15_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_15_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_16_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_16_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_17_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_17_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_22_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_22_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_23_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_23_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_24_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_24_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_25_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_25_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_26_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_26_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_27_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_27_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_28_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_28_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_29_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_29_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_30_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_30_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_31_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_31_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_32_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_32_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_33_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_33_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_34_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_34_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_35_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_35_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_36_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_36_every_row (probeOfRow row) r)
      ∧ (Main.extraction.constraint_37_every_row (extractedMainRow row) r
        ↔ Main.extraction.constraint_37_every_row (probeOfRow row) r) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl,
   Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl,
   Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## The instance is pinned

`extractedMainRowCircuit_main_eq` near the top already ties the class
projection the generated constraints read through to `mainValue`. This closes
the remaining freedom: it fixes all four fields at once, and it is stated
through `inferInstance`, so it fails to compile both if a field drifts and if
instance resolution for `Extraction.Circuit FGL FGL ExtractedMainRow` starts
finding a different instance. It is deliberately the last declaration in the
module: every weld above resolves that class against the instances declared
before it, so an instance introduced anywhere above — including one shadowing
`extractedMainRowCircuit` — is also the one this theorem resolves and checks. -/
theorem extractedMainRowCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedMainRow) =
      { main := mainValue
        preprocessed := fun _ _ _ _ => 0
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

end ZiskFv.AirsClean.Main
