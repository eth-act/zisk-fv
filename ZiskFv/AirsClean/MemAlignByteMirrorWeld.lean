import Extraction.MemAlignByte
import Extraction.MemAlignReadByte
import Extraction.MemAlignWriteByte
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.AirsClean.MemAlignByte.Constraints
import ZiskFv.AirsClean.MemAlignReadByte.Constraints

/-!
# Machine-checked weld: the `mem_align_byte.pil` mirrors ↔ generated extraction

Three AIRs are emitted from one PIL template, `mem/pil/mem_align_byte.pil`:
`MemAlignByte` (air id 18, 16 columns), `MemAlignReadByte` (id 19, 10 columns)
and `MemAlignWriteByte` (id 20, 14 columns). The repository mirrors the first two
by hand — `ZiskFv/Airs/MemAlignByte.lean` and `ZiskFv/Airs/MemAlignReadByte.lean`
for the named-column predicates, `ZiskFv/AirsClean/Mem*/Constraints.lean` for the
Clean `assertZero` lists — and cites the generated
`Extraction.<AIR>.constraint_N_every_row` definitions in comments only. Comments
are not checked by anything, so a transcription slip in a mirror would be
invisible to the build.

This module replaces the comment citation with compiled identities covering all
20 F-only constraints of the three AIRs: `MemAlignByte` `0`–`8`,
`MemAlignReadByte` `0`–`3`, `MemAlignWriteByte` `0`–`6`. Every one is `Iff.rfl`.

## How the weld works

`Extraction.<AIR>.constraint_N_every_row` is stated against the abstract
`Extraction.Circuit` interface: an F-only body only ever mentions
`Extraction.Circuit.main c (id := 1) (column := k) (row := r) (rotation := 0)`.
Each `Extracted…` structure below is an `Extraction.Circuit` instance whose
stage-1 column `k` reads column `k` of the corresponding handwritten
named-column record, using the column layout printed by the extractor in the
generated header. Instantiating a generated constraint at that circuit therefore
turns it into a polynomial over the mirror's own accessors, and the weld theorems
say that polynomial is *definitionally* the one the mirror asserts.

The mirrors' columns are `ℕ → F`, so the welds are stated for an arbitrary trace
row `r`, not only row `0`: the `mainValue` maps pass the generated `row` argument
through. A mirror predicate that read a neighbouring row would therefore fail to
weld, not silently agree.

## What the weld does and does not certify

* It certifies, by `Iff.rfl`, that the welded mirror polynomials are the
  generated polynomials — same columns, same coefficients, same shape.
* Coverage is the whole F-only set of all three AIRs. The other 21 generated
  constraints (`MemAlignByte` `9`–`15`, `MemAlignReadByte` `4`–`9`,
  `MemAlignWriteByte` `7`–`14`) read stage-2 columns (`id := 2`), the challenge
  lane, the `exposed` lane, `preprocessed`, or neighbouring rows; they are the
  permutation/`gsum` bookkeeping, represented in the Clean components by
  `MemBusChannel.pull`/`push` and `lookup` operations rather than by `assertZero`.
  Nothing here welds them.
* For `MemAlignByte` and `MemAlignReadByte` the tie reaches the *live* assertion
  list, not only transcribed prose: `memAlignByte_extracted_of_main` and
  `memAlignReadByte_extracted_of_main` derive the generated constraints from
  `ConstraintsHold.Soundness` over the very `main` do-block that
  `ZiskFv/AirsClean/…/Circuit.lean` elaborates into the component that sits in
  `fullRv64imSoundEnsemble`. A slip in an `assertZero` expression is a build
  failure, not just a slip in a `Prop` nobody reads.
* `MemAlignWriteByte` is different and the difference is not dressed up: **there
  is no `MemAlignWriteByte` mirror anywhere under `ZiskFv/`, and no
  `MemAlignWriteByte` component in `fullRv64imSoundEnsemble`.** Its seven welds
  state that the generated `MemAlignWriteByte` polynomials are the
  `ZiskFv.Airs.MemAlignByte` predicates read at the *WriteByte* column layout —
  i.e. they machine-check the "same PIL template, shifted `mem_write_values`
  columns" claim that `docs/extraction/air-inventory.md` makes in prose. That is
  a real check of generated text against a documented reading, but it protects no
  live proof, because no live proof consumes this AIR today.
* It does **not** certify the column layouts themselves: the three `mainValue`
  maps are handwritten. They are transcribed from the extractor's own
  `stage 1 col N: <name>` headers
  (`build/extraction/Extraction/MemAlignByte.lean:14-29`,
  `…/MemAlignReadByte.lean:14-23`, `…/MemAlignWriteByte.lean:14-27`), but nothing
  in the build re-reads those headers. A *compensating* pair of slips — mirror
  and map wrong in the same direction — would still be `rfl`. So what these 20
  welds certify is precisely "mirror == generated, modulo one shared reading of
  the column map", not "mirror == generated". Closing that requires the analogue
  of `trust/scripts/check-arith-column-map.py`, pinning the 40 `mainValue` arms
  against the generated headers; that gate is not part of this module.
  `…Circuit_pinned` at the bottom is what makes such a gate meaningful once it
  exists: it ties the instance the welds resolve to the map a gate would read.
* It does **not** rest on `mainValue`'s `0` answers outside the modeled lanes,
  nor on the `preprocessed`/`challenge`/`exposed` stubs. That is checked by
  `fOnlyConstraints_readOnlyModeledLanes` and `weldedConstraints_probeBridge`,
  not assumed; see "Which lanes a welded constraint is allowed to read".

## Mutation evidence

A weld that nothing can break is a claim, not a check. Each of the following was
applied to the tree, compiled, observed to fail, and reverted:

* swapping `memAlignByteMainValue`'s columns 8 and 9 (`value_8b` ↔ `byte_value`)
  — 5 failures;
* changing the mirror's `bus_byte_definition` to add `written_byte_value` instead
  of `byte_value` — 3 failures, including `memAlignByte_extracted_of_main`;
* changing `mem_write_values_0`'s `assertZero` in
  `ZiskFv/AirsClean/MemAlignByte/Constraints.lean` from `direct_value` to
  `composed_value` — 1 failure, in `memAlignByte_extracted_of_main` only, which
  is what shows that theorem is doing work the `Iff.rfl` welds do not;
* shifting `memAlignWriteByteMainValue`'s `mem_write_values` back to columns
  13/14 (i.e. reusing `MemAlignByte`'s layout) — 4 failures;
* changing `16777216` to `16777215` in the mirror's `byte_value_factor` — 8
  failures across both write-carrying AIRs and the live tie;
* swapping `memAlignReadByteMainValue`'s columns 5 and 7 — 2 failures, and none
  in the `MemAlignByte` or `MemAlignWriteByte` sections, confirming the three
  column maps are independent data.

The two lane-discipline controls are recorded at
`fOnlyConstraints_readOnlyModeledLanes`, and the two binding controls at
`extractedMemAlignByteCircuit_pinned`.

## Trust note

No axiom, `sorry`, `native_decide`, or other trust marker is added. Every weld is
`Iff.rfl`. The only non-`rfl` steps in the module are the `linear_combination`
calls inside `…_extracted_of_main`, which exist purely because Clean's
`circuit_norm` normalizes an asserted `a - b` into `a + -b`; the mathematical
content is the `Iff.rfl` weld the `linear_combination` is fed into.
-/

namespace ZiskFv.AirsClean.MemAlignByteMirrorWeld

open Goldilocks

/-! ## Bridges

One `Extraction.Circuit` instance per AIR. Each wraps the handwritten
named-column record the mirror predicates are stated over, so instantiating a
generated constraint at it yields a polynomial in the mirror's own accessors.

`MemAlignWriteByte` has no record of its own (it has no mirror); it reuses
`ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte`, whose first twelve fields are
column-for-column the WriteByte layout. Its `is_write` and `bus_byte` fields are
absent from the WriteByte AIR and are simply never read by the WriteByte map.
-/

/-- The `MemAlignByte` AIR's stage-1 columns, backed by the handwritten
    `Valid_MemAlignByte` record. -/
structure ExtractedMemAlignByte (F ExtF : Type) where
  cols : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL

/-- The `MemAlignReadByte` AIR's stage-1 columns, backed by the handwritten
    `Valid_MemAlignReadByte` record. -/
structure ExtractedMemAlignReadByte (F ExtF : Type) where
  cols : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL

/-- The `MemAlignWriteByte` AIR's stage-1 columns. Backed by
    `Valid_MemAlignByte` — see the section comment: this AIR has no mirror of its
    own, and the weld's content is exactly that its generated polynomials are the
    `MemAlignByte` mirror's polynomials at the shifted WriteByte layout. -/
structure ExtractedMemAlignWriteByte (F ExtF : Type) where
  cols : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL

/-- `MemAlignByte` stage-1 column layout (16 columns), transcribed from the
    generated header `build/extraction/Extraction/MemAlignByte.lean:14-29`
    (`stage 1 col N: <name>`).

    This map, and its two siblings below, are the only handwritten data the weld
    introduces; nothing in the build re-reads the generated header, so see the
    module docstring for exactly what that leaves unchecked. Stage 2
    (`gsum`, `im_cluster`, `im_single`) is not modeled: the generated constraints
    that read it also read the challenge lane and are channel operations in the
    Clean component, not `assertZero`s. -/
@[reducible]
def memAlignByteMainValue (c : ExtractedMemAlignByte FGL FGL)
    (id column row rotation : ℕ) : FGL :=
  if id = 1 then
    if rotation = 0 then
      match column with
      | 0 => c.cols.sel_high_4b row
      | 1 => c.cols.sel_high_2b row
      | 2 => c.cols.sel_high_b row
      | 3 => c.cols.direct_value row
      | 4 => c.cols.composed_value row
      | 5 => c.cols.written_composed_value row
      | 6 => c.cols.written_byte_value row
      | 7 => c.cols.value_16b row
      | 8 => c.cols.value_8b row
      | 9 => c.cols.byte_value row
      | 10 => c.cols.addr_w row
      | 11 => c.cols.step row
      | 12 => c.cols.is_write row
      | 13 => c.cols.mem_write_values_0 row
      | 14 => c.cols.mem_write_values_1 row
      | 15 => c.cols.bus_byte row
      | _ => 0
    else 0
  else 0

/-- `MemAlignReadByte` stage-1 column layout (10 columns), transcribed from
    `build/extraction/Extraction/MemAlignReadByte.lean:14-23`. Note that this AIR
    drops `written_composed_value`/`written_byte_value`/`is_write`/
    `mem_write_values`/`bus_byte`, so `value_16b`/`value_8b`/`byte_value` sit at
    columns 5/6/7 here and at 7/8/9 in `MemAlignByte`. -/
@[reducible]
def memAlignReadByteMainValue (c : ExtractedMemAlignReadByte FGL FGL)
    (id column row rotation : ℕ) : FGL :=
  if id = 1 then
    if rotation = 0 then
      match column with
      | 0 => c.cols.sel_high_4b row
      | 1 => c.cols.sel_high_2b row
      | 2 => c.cols.sel_high_b row
      | 3 => c.cols.direct_value row
      | 4 => c.cols.composed_value row
      | 5 => c.cols.value_16b row
      | 6 => c.cols.value_8b row
      | 7 => c.cols.byte_value row
      | 8 => c.cols.addr_w row
      | 9 => c.cols.step row
      | _ => 0
    else 0
  else 0

/-- `MemAlignWriteByte` stage-1 column layout (14 columns), transcribed from
    `build/extraction/Extraction/MemAlignWriteByte.lean:14-27`. Columns 0-11
    coincide with `MemAlignByte`; `is_write` and `bus_byte` are absent, so
    `mem_write_values[0]`/`[1]` sit at 12/13 rather than 13/14. That shift is the
    specific slip these welds exist to catch. -/
@[reducible]
def memAlignWriteByteMainValue (c : ExtractedMemAlignWriteByte FGL FGL)
    (id column row rotation : ℕ) : FGL :=
  if id = 1 then
    if rotation = 0 then
      match column with
      | 0 => c.cols.sel_high_4b row
      | 1 => c.cols.sel_high_2b row
      | 2 => c.cols.sel_high_b row
      | 3 => c.cols.direct_value row
      | 4 => c.cols.composed_value row
      | 5 => c.cols.written_composed_value row
      | 6 => c.cols.written_byte_value row
      | 7 => c.cols.value_16b row
      | 8 => c.cols.value_8b row
      | 9 => c.cols.byte_value row
      | 10 => c.cols.addr_w row
      | 11 => c.cols.step row
      | 12 => c.cols.mem_write_values_0 row
      | 13 => c.cols.mem_write_values_1 row
      | _ => 0
    else 0
  else 0

instance extractedMemAlignByteCircuit :
    Extraction.Circuit FGL FGL ExtractedMemAlignByte where
  main := memAlignByteMainValue
  preprocessed := fun _ _ _ _ => 0
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

instance extractedMemAlignReadByteCircuit :
    Extraction.Circuit FGL FGL ExtractedMemAlignReadByte where
  main := memAlignReadByteMainValue
  preprocessed := fun _ _ _ _ => 0
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

instance extractedMemAlignWriteByteCircuit :
    Extraction.Circuit FGL FGL ExtractedMemAlignWriteByte where
  main := memAlignWriteByteMainValue
  preprocessed := fun _ _ _ _ => 0
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

@[reducible]
def extMAB (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) :
    ExtractedMemAlignByte FGL FGL := ⟨v⟩

@[reducible]
def extMARB (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) :
    ExtractedMemAlignReadByte FGL FGL := ⟨v⟩

@[reducible]
def extMAWB (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) :
    ExtractedMemAlignWriteByte FGL FGL := ⟨v⟩

/-! ## MemAlignByte: the nine F-only constraints

Each theorem is `Iff.rfl`: the mirror's polynomial and the generated polynomial
are the same term after unfolding the column map. Two are spelled out longhand
first, so the identity is readable as source against source; the rest are stated
against the mirror predicates directly, and `memAlignByte_core_every_row_weld`
bundles all nine so the predicate that `ZiskFv/AirsClean/MemAlignByte/Bridge.lean`
consumes is pinned as a whole — neither more nor less than the AIR's F-only set.
-/

/-- `mem/pil/mem_align_byte.pil:35 sel_high_4b*(1-sel_high_4b)` — the plain
    boolean shape, longhand. -/
theorem memAlignByte_constraint_0_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    (v.sel_high_4b r * (1 - v.sel_high_4b r) = 0)
      ↔ MemAlignByte.extraction.constraint_0_every_row (extMAB v) r :=
  Iff.rfl

/-- `mem/pil/mem_align_byte.pil:95
    bus_byte-((is_write*(written_byte_value-byte_value))+byte_value)` — the
    read/write byte mux, longhand. This is the constraint the narrow-load route
    in `ZiskFv/AirsClean/MemAlignByte/Bridge.lean` leans on. -/
theorem memAlignByte_constraint_8_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    (v.bus_byte r
        - (v.is_write r * (v.written_byte_value r - v.byte_value r) + v.byte_value r) = 0)
      ↔ MemAlignByte.extraction.constraint_8_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_boolean_sel_high_4b_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_sel_high_4b v r
      ↔ MemAlignByte.extraction.constraint_0_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_boolean_sel_high_2b_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_sel_high_2b v r
      ↔ MemAlignByte.extraction.constraint_1_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_boolean_sel_high_b_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_sel_high_b v r
      ↔ MemAlignByte.extraction.constraint_2_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_composed_value_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.composed_value_definition v r
      ↔ MemAlignByte.extraction.constraint_3_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_boolean_is_write_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_is_write v r
      ↔ MemAlignByte.extraction.constraint_4_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_written_composed_value_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.written_composed_value_definition v r
      ↔ MemAlignByte.extraction.constraint_5_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_mem_write_values_0_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.mem_write_values_0_definition v r
      ↔ MemAlignByte.extraction.constraint_6_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_mem_write_values_1_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.mem_write_values_1_definition v r
      ↔ MemAlignByte.extraction.constraint_7_every_row (extMAB v) r :=
  Iff.rfl

theorem memAlignByte_bus_byte_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.bus_byte_definition v r
      ↔ MemAlignByte.extraction.constraint_8_every_row (extMAB v) r :=
  Iff.rfl

/-- `core_every_row` is the bundle consumed as a hypothesis by
    `ZiskFv/AirsClean/MemAlignByte/Bridge.lean`. Welding it as an `Iff` against
    the conjunction of the AIR's nine F-only constraints pins it exactly: it
    holds *iff* they do, so the mirror asserts neither less nor more than the
    AIR, and the ordering of the conjuncts is pinned too. -/
theorem memAlignByte_core_every_row_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.core_every_row v r ↔
      MemAlignByte.extraction.constraint_0_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_1_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_2_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_3_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_4_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_5_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_6_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_7_every_row (extMAB v) r
      ∧ MemAlignByte.extraction.constraint_8_every_row (extMAB v) r :=
  Iff.rfl

/-! ## MemAlignReadByte: the four F-only constraints -/

theorem memAlignReadByte_boolean_sel_high_4b_weld
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignReadByte.boolean_sel_high_4b v r
      ↔ MemAlignReadByte.extraction.constraint_0_every_row (extMARB v) r :=
  Iff.rfl

theorem memAlignReadByte_boolean_sel_high_2b_weld
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignReadByte.boolean_sel_high_2b v r
      ↔ MemAlignReadByte.extraction.constraint_1_every_row (extMARB v) r :=
  Iff.rfl

theorem memAlignReadByte_boolean_sel_high_b_weld
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignReadByte.boolean_sel_high_b v r
      ↔ MemAlignReadByte.extraction.constraint_2_every_row (extMARB v) r :=
  Iff.rfl

/-- The read-byte recombination. Same polynomial as `MemAlignByte`'s
    `composed_value_definition`, but read at the ten-column layout: a weld that
    used `MemAlignByte`'s 7/8/9 for `value_16b`/`value_8b`/`byte_value` instead
    of this AIR's 5/6/7 would not close. -/
theorem memAlignReadByte_composed_value_definition_weld
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignReadByte.composed_value_definition v r
      ↔ MemAlignReadByte.extraction.constraint_3_every_row (extMARB v) r :=
  Iff.rfl

/-- The bundle consumed as a hypothesis by
    `ZiskFv/AirsClean/MemAlignReadByte/Bridge.lean`, pinned exactly. -/
theorem memAlignReadByte_core_every_row_weld
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignReadByte.core_every_row v r ↔
      MemAlignReadByte.extraction.constraint_0_every_row (extMARB v) r
      ∧ MemAlignReadByte.extraction.constraint_1_every_row (extMARB v) r
      ∧ MemAlignReadByte.extraction.constraint_2_every_row (extMARB v) r
      ∧ MemAlignReadByte.extraction.constraint_3_every_row (extMARB v) r :=
  Iff.rfl

/-! ## MemAlignWriteByte: the seven F-only constraints

Read the module docstring before reading these. There is no `MemAlignWriteByte`
mirror and no `MemAlignWriteByte` component in `fullRv64imSoundEnsemble`; what is
welded here is the claim that this AIR's generated polynomials *are* the
`MemAlignByte` mirror's polynomials at the WriteByte column layout. It checks
generated text against a documented shared-template reading. It does not protect
a live proof, because nothing consumes this AIR yet.

The two `mem_write_values` welds are the load-bearing ones: they are the only
place the 12/13-versus-13/14 column shift between the two AIRs is checked.
-/

theorem memAlignWriteByte_boolean_sel_high_4b_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_sel_high_4b v r
      ↔ MemAlignWriteByte.extraction.constraint_0_every_row (extMAWB v) r :=
  Iff.rfl

theorem memAlignWriteByte_boolean_sel_high_2b_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_sel_high_2b v r
      ↔ MemAlignWriteByte.extraction.constraint_1_every_row (extMAWB v) r :=
  Iff.rfl

theorem memAlignWriteByte_boolean_sel_high_b_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.boolean_sel_high_b v r
      ↔ MemAlignWriteByte.extraction.constraint_2_every_row (extMAWB v) r :=
  Iff.rfl

theorem memAlignWriteByte_composed_value_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.composed_value_definition v r
      ↔ MemAlignWriteByte.extraction.constraint_3_every_row (extMAWB v) r :=
  Iff.rfl

theorem memAlignWriteByte_written_composed_value_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.written_composed_value_definition v r
      ↔ MemAlignWriteByte.extraction.constraint_4_every_row (extMAWB v) r :=
  Iff.rfl

/-- `mem_write_values[0]` at WriteByte column 12, not MemAlignByte's 13. -/
theorem memAlignWriteByte_mem_write_values_0_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.mem_write_values_0_definition v r
      ↔ MemAlignWriteByte.extraction.constraint_5_every_row (extMAWB v) r :=
  Iff.rfl

/-- `mem_write_values[1]` at WriteByte column 13, not MemAlignByte's 14. -/
theorem memAlignWriteByte_mem_write_values_1_definition_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    ZiskFv.Airs.MemAlignByte.mem_write_values_1_definition v r
      ↔ MemAlignWriteByte.extraction.constraint_6_every_row (extMAWB v) r :=
  Iff.rfl

/-- The seven F-only `MemAlignWriteByte` constraints, as a run. `MemAlignByte`'s
    `core_every_row` cannot be used here: it also bundles `boolean_is_write` and
    `bus_byte_definition`, which this AIR does not have. -/
theorem memAlignWriteByte_fOnly_weld
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) :
    (ZiskFv.Airs.MemAlignByte.boolean_sel_high_4b v r
      ∧ ZiskFv.Airs.MemAlignByte.boolean_sel_high_2b v r
      ∧ ZiskFv.Airs.MemAlignByte.boolean_sel_high_b v r
      ∧ ZiskFv.Airs.MemAlignByte.composed_value_definition v r
      ∧ ZiskFv.Airs.MemAlignByte.written_composed_value_definition v r
      ∧ ZiskFv.Airs.MemAlignByte.mem_write_values_0_definition v r
      ∧ ZiskFv.Airs.MemAlignByte.mem_write_values_1_definition v r) ↔
      MemAlignWriteByte.extraction.constraint_0_every_row (extMAWB v) r
      ∧ MemAlignWriteByte.extraction.constraint_1_every_row (extMAWB v) r
      ∧ MemAlignWriteByte.extraction.constraint_2_every_row (extMAWB v) r
      ∧ MemAlignWriteByte.extraction.constraint_3_every_row (extMAWB v) r
      ∧ MemAlignWriteByte.extraction.constraint_4_every_row (extMAWB v) r
      ∧ MemAlignWriteByte.extraction.constraint_5_every_row (extMAWB v) r
      ∧ MemAlignWriteByte.extraction.constraint_6_every_row (extMAWB v) r :=
  Iff.rfl

/-! ## From the live Clean assertion lists

The welds above tie the generated constraints to the `ZiskFv/Airs/…` predicate
mirrors. This section ties them to the *other* mirror — the `assertZero`
expressions in `ZiskFv/AirsClean/…/Constraints.lean`, which are what the
`Air.Flat.Component`s in `fullRv64imSoundEnsemble` actually elaborate. Nothing is
assumed about those expressions: the generated constraints are derived from
`ConstraintsHold.Soundness` over the component's own operation list, so an edit
to any `assertZero` breaks this theorem.

`linear_combination` appears only because `circuit_norm` rewrites the asserted
`a - b = 0` into `a + -b = 0`; the identity being checked is still the `Iff.rfl`
weld it is fed into. -/

/-- Read a `MemAlignByteRow` (the Clean stage-1 row) as the legacy named-column
    record, constant in the trace row. -/
@[reducible]
def validOfCleanRow (row : ZiskFv.AirsClean.MemAlignByte.MemAlignByteRow FGL) :
    ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL where
  sel_high_4b _ := row.sel_high_4b
  sel_high_2b _ := row.sel_high_2b
  sel_high_b _ := row.sel_high_b
  direct_value _ := row.direct_value
  composed_value _ := row.composed_value
  written_composed_value _ := row.written_composed_value
  written_byte_value _ := row.written_byte_value
  value_16b _ := row.value_16b
  value_8b _ := row.value_8b
  byte_value _ := row.byte_value
  addr_w _ := row.addr_w
  step _ := row.step
  is_write _ := row.is_write
  mem_write_values_0 _ := row.mem_write_values_0
  mem_write_values_1 _ := row.mem_write_values_1
  bus_byte _ := row.bus_byte

/-- Read a `MemAlignReadByteRow` as the legacy named-column record. -/
@[reducible]
def validOfCleanReadRow (row : ZiskFv.AirsClean.MemAlignReadByte.MemAlignReadByteRow FGL) :
    ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL where
  sel_high_4b _ := row.sel_high_4b
  sel_high_2b _ := row.sel_high_2b
  sel_high_b _ := row.sel_high_b
  direct_value _ := row.direct_value
  composed_value _ := row.composed_value
  value_16b _ := row.value_16b
  value_8b _ := row.value_8b
  byte_value _ := row.byte_value
  addr_w _ := row.addr_w
  step _ := row.step

/-- Every F-only `MemAlignByte` constraint, derived from the Clean component's
    own `assertZero` list. -/
theorem memAlignByte_extracted_of_main
    (offset : ℕ) (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.MemAlignByte.MemAlignByteRow FGL) (r : ℕ)
    (h : ConstraintsHold.Soundness env
      ((ZiskFv.AirsClean.MemAlignByte.main row).operations offset)) :
    MemAlignByte.extraction.constraint_0_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_1_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_2_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_3_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_4_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_5_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_6_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_7_every_row
        (extMAB (validOfCleanRow (eval env row))) r
      ∧ MemAlignByte.extraction.constraint_8_every_row
        (extMAB (validOfCleanRow (eval env row))) r := by
  simp only [ZiskFv.AirsClean.MemAlignByte.main, circuit_norm] at h
  obtain ⟨_l0, _l1, _l2, _l3, _l4, h0, h1, h2, h3, h4, h5, h6, h7, h8, _hpull⟩ := h
  -- `circuit_norm` leaves each asserted polynomial in `a + -b` form while the
  -- mirror writes `a - b`; `linear_combination` crosses exactly that gap. The two
  -- recombination constraints additionally need the mirror's shared `*_factor`
  -- abbreviations unfolded, so that `ring` sees one polynomial rather than an
  -- opaque atom.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (memAlignByte_boolean_sel_high_4b_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h0)
  · exact (memAlignByte_boolean_sel_high_2b_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h1)
  · exact (memAlignByte_boolean_sel_high_b_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h2)
  · exact (memAlignByte_composed_value_definition_weld _ r).mp
      (by show _ = (0 : FGL)
          simp only [ZiskFv.Airs.MemAlignByte.byte_value_factor,
            ZiskFv.Airs.MemAlignByte.value_8b_factor,
            ZiskFv.Airs.MemAlignByte.value_16b_factor, circuit_norm]
          linear_combination h3)
  · exact (memAlignByte_boolean_is_write_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h4)
  · exact (memAlignByte_written_composed_value_definition_weld _ r).mp
      (by show _ = (0 : FGL)
          simp only [ZiskFv.Airs.MemAlignByte.byte_value_factor,
            ZiskFv.Airs.MemAlignByte.value_8b_factor,
            ZiskFv.Airs.MemAlignByte.value_16b_factor, circuit_norm]
          linear_combination h5)
  · exact (memAlignByte_mem_write_values_0_definition_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h6)
  · exact (memAlignByte_mem_write_values_1_definition_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h7)
  · exact (memAlignByte_bus_byte_definition_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h8)

/-- Every F-only `MemAlignReadByte` constraint, derived from the Clean
    component's own `assertZero` list. -/
theorem memAlignReadByte_extracted_of_main
    (offset : ℕ) (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.MemAlignReadByte.MemAlignReadByteRow FGL) (r : ℕ)
    (h : ConstraintsHold.Soundness env
      ((ZiskFv.AirsClean.MemAlignReadByte.main row).operations offset)) :
    MemAlignReadByte.extraction.constraint_0_every_row
        (extMARB (validOfCleanReadRow (eval env row))) r
      ∧ MemAlignReadByte.extraction.constraint_1_every_row
        (extMARB (validOfCleanReadRow (eval env row))) r
      ∧ MemAlignReadByte.extraction.constraint_2_every_row
        (extMARB (validOfCleanReadRow (eval env row))) r
      ∧ MemAlignReadByte.extraction.constraint_3_every_row
        (extMARB (validOfCleanReadRow (eval env row))) r := by
  simp only [ZiskFv.AirsClean.MemAlignReadByte.main, circuit_norm] at h
  obtain ⟨_l0, _l1, _l2, h0, h1, h2, h3, _hpull⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (memAlignReadByte_boolean_sel_high_4b_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h0)
  · exact (memAlignReadByte_boolean_sel_high_2b_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h1)
  · exact (memAlignReadByte_boolean_sel_high_b_weld _ r).mp
      (by show _ = (0 : FGL); simp only [circuit_norm]; linear_combination h2)
  · exact (memAlignReadByte_composed_value_definition_weld _ r).mp
      (by show _ = (0 : FGL)
          simp only [ZiskFv.Airs.MemAlignReadByte.byte_value_factor,
            ZiskFv.Airs.MemAlignReadByte.value_8b_factor,
            ZiskFv.Airs.MemAlignReadByte.value_16b_factor, circuit_norm]
          linear_combination h3)

/-! ## Which lanes a welded constraint is allowed to read

Each `mainValue` is total, so it has to answer somewhere it is not modeling: it
returns `0` for every stage-2 read (`id ≠ 1`), every nonzero rotation, and every
stage-1 column past the AIR's width. The three instances stub `preprocessed`,
`challenge` and `exposed` to `0` outright. Those answers are only harmless if no
welded constraint can observe them; if one could, the weld would be certifying a
polynomial the AIR does not assert. This section checks that instead of asserting
it.

`Probe` is the *free* `Extraction.Circuit`: every lane is an unconstrained
function field. Instantiating a generated constraint there turns each cell read
into an application of a variable, so a `rfl`-level identity between a probe
circuit and its restriction is a statement about which cells the generated body
mentions — not about their values. -/

/-- The free `Extraction.Circuit` over `FGL`: each lane is a function field. -/
structure Probe (F ExtF : Type) where
  mainCell : ℕ → ℕ → ℕ → ℕ → FGL
  preprocessedCell : ℕ → ℕ → ℕ → FGL
  challengeCell : ℕ → FGL
  exposedCell : ℕ → FGL

instance probeCircuit : Extraction.Circuit FGL FGL Probe where
  main c := c.mainCell
  preprocessed c := c.preprocessedCell
  challenge c := c.challengeCell
  exposed c := c.exposedCell

/-- `c` cut down to the lanes an `n`-column bridge models: stage 1, columns
    `< n`, rotation `0`, the single trace row `r`; `0` everywhere else, including
    all of `preprocessed`, `challenge` and `exposed`. -/
@[reducible]
def restrictToModeledLanes (n : ℕ) (c : Probe FGL FGL) (r : ℕ) : Probe FGL FGL where
  mainCell := fun id column _row rotation =>
    if id = 1 ∧ column < n ∧ rotation = 0 then c.mainCell id column r rotation else 0
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- `P c r` is unchanged by zeroing every lane an `n`-column bridge stubs.

    Unfolded: `P c r` may mention `c.mainCell 1 k r 0` for `k < n` and nothing
    else. A read of a stage-2 column, of stage-1 column `≥ n`, of a rotation other
    than `0`, of a trace row other than `r`, or of `preprocessed`, `challenge` or
    `exposed` would leave a free `c.<lane> …` on the left of the `Iff` with no
    counterpart on the right, and `Iff.rfl` would not typecheck. -/
@[reducible]
def ReadsOnlyModeledLanes (n : ℕ) (P : Probe FGL FGL → ℕ → Prop) : Prop :=
  ∀ (c : Probe FGL FGL) (r : ℕ), P c r ↔ P (restrictToModeledLanes n c r) r

/-- All 20 welded constraints read only the lanes their bridge models: the nine
    `MemAlignByte` ones within 16 columns, the four `MemAlignReadByte` ones
    within 10, the seven `MemAlignWriteByte` ones within 14.

    The property is not vacuous; two controls were compiled and observed to fail.
    `ReadsOnlyModeledLanes 16` asserted of
    `MemAlignByte.extraction.constraint_9_every_row` — the first constraint
    outside the F-only set, which reads `id := 2` and
    `Extraction.Circuit.challenge` — is rejected, `Iff.rfl` not matching the
    stated `Iff`. So is `ReadsOnlyModeledLanes 15` asserted of
    `constraint_8_every_row`, which reads stage-1 column 15; so the column bound
    is tight for that constraint and not merely large enough. The `0` stubs
    therefore cannot be what makes any of these hold. -/
theorem fOnlyConstraints_readOnlyModeledLanes :
    ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_0_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_1_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_2_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_3_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_4_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_5_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_6_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_7_every_row
    ∧ ReadsOnlyModeledLanes 16 MemAlignByte.extraction.constraint_8_every_row
    ∧ ReadsOnlyModeledLanes 10 MemAlignReadByte.extraction.constraint_0_every_row
    ∧ ReadsOnlyModeledLanes 10 MemAlignReadByte.extraction.constraint_1_every_row
    ∧ ReadsOnlyModeledLanes 10 MemAlignReadByte.extraction.constraint_2_every_row
    ∧ ReadsOnlyModeledLanes 10 MemAlignReadByte.extraction.constraint_3_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_0_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_1_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_2_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_3_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_4_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_5_every_row
    ∧ ReadsOnlyModeledLanes 14 MemAlignWriteByte.extraction.constraint_6_every_row :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- `extMAB v` re-expressed in the free circuit: the column map in the stage-1
    lane, `0` in every stub lane. -/
@[reducible]
def probeOfMAB (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) : Probe FGL FGL where
  mainCell := memAlignByteMainValue (extMAB v)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

@[reducible]
def probeOfMARB (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) : Probe FGL FGL where
  mainCell := memAlignReadByteMainValue (extMARB v)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

@[reducible]
def probeOfMAWB (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) : Probe FGL FGL where
  mainCell := memAlignWriteByteMainValue (extMAWB v)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- The bridge from the three welding instances into the free circuit. Composed
    with `fOnlyConstraints_readOnlyModeledLanes` it gives: a welded constraint
    cannot observe a stubbed lane, so the `0` defaults in the column maps and the
    `preprocessed`/`challenge`/`exposed` stubs cannot be what makes a weld true.

    Instantiated at one representative constraint per AIR per shape: the boolean
    `0`, the wide recombination `3`, and the `mem_write_values` mux where the two
    write-carrying AIRs differ. The lane-restriction result it composes with is
    proved for all 20, which is where the generality lives; extending this bridge
    to the rest is mechanical instantiation. -/
theorem weldedConstraints_probeBridge
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (w : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) :
    (MemAlignByte.extraction.constraint_0_every_row (extMAB v) r
        ↔ MemAlignByte.extraction.constraint_0_every_row (probeOfMAB v) r)
      ∧ (MemAlignByte.extraction.constraint_3_every_row (extMAB v) r
        ↔ MemAlignByte.extraction.constraint_3_every_row (probeOfMAB v) r)
      ∧ (MemAlignByte.extraction.constraint_6_every_row (extMAB v) r
        ↔ MemAlignByte.extraction.constraint_6_every_row (probeOfMAB v) r)
      ∧ (MemAlignByte.extraction.constraint_8_every_row (extMAB v) r
        ↔ MemAlignByte.extraction.constraint_8_every_row (probeOfMAB v) r)
      ∧ (MemAlignReadByte.extraction.constraint_3_every_row (extMARB w) r
        ↔ MemAlignReadByte.extraction.constraint_3_every_row (probeOfMARB w) r)
      ∧ (MemAlignWriteByte.extraction.constraint_5_every_row (extMAWB v) r
        ↔ MemAlignWriteByte.extraction.constraint_5_every_row (probeOfMAWB v) r) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## The instances are pinned to the pinned column maps

Every weld above resolves `Extraction.Circuit FGL FGL Extracted…` by instance
search, so a *gross* rebind breaks the welds directly — replacing
`extractedMemAlignByteCircuit`'s `main` with `fun _ _ _ _ _ => 0` was measured to
produce 20 errors in this file. But the welds do **not** pin the binding on their
own, and this is measured too: rebinding it to
`fun c id column row _ => memAlignByteMainValue c id column row 0` (the same map
with the rotation guard dropped) leaves *all twenty welds passing*, because every
F-only generated constraint reads rotation `0`. That is exactly the failure mode
the Arith precedent's review found (eth-act/zisk-fv#300): a gate that reads a
`mainValue` definition while the instance the welds resolve points somewhere
else. Under that rebind `extractedMemAlignByteCircuit_pinned` is the *only*
declaration in the module that fails, so these theorems are what closes the hole,
not decoration.

They are stated through `inferInstance`, so they fail to compile both if a field
of an instance drifts and if instance resolution starts finding a different
instance. They are deliberately the last declarations in the module: every weld
above resolves the class against the instances declared before them, so an
instance introduced anywhere above — including one shadowing these — is also the
one these theorems resolve and check. -/

theorem extractedMemAlignByteCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedMemAlignByte) =
      { main := memAlignByteMainValue
        preprocessed := fun _ _ _ _ => 0
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

theorem extractedMemAlignReadByteCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedMemAlignReadByte) =
      { main := memAlignReadByteMainValue
        preprocessed := fun _ _ _ _ => 0
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

theorem extractedMemAlignWriteByteCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedMemAlignWriteByte) =
      { main := memAlignWriteByteMainValue
        preprocessed := fun _ _ _ _ => 0
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

end ZiskFv.AirsClean.MemAlignByteMirrorWeld
