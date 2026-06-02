# Removing the decoder/transpiler trust gap

## Why this is necessary

The FENCE experiment showed that semantic opcode proofs and post-classification
transpiler proofs are not enough for ISA coverage completeness.

Current Lean can prove:

```lean
execute_instruction (instruction.FENCE fields) state
  = state_effect_via_channels rows state
```

and:

```lean
transpile { op := .fence, ... } = [nop-row]
```

But the real FENCE bug is earlier:

```text
raw 32-bit word
  -> ZisK RISC-V interpreter classifies as "fence" or "reserved"
```

The checked-out ZisK source at `zisk/riscv/src/riscv_interpreter.rs` currently
rejects generic FENCE when `(inst & 0xF00F8F80) != 0`, covering nonzero `fm`,
`rs1`, or `rd`. A proof that starts after `.fence` has already been selected
cannot catch that.

## Current trust shape

The current repo has:

* `ZiskFv.Transpiler.Static`: a Lean model of the post-classification static
  RV64-to-ZisK row lowering.
* `ZiskFv.Trusted.Transpiler`: trusted row contracts for selected opcode
  routes.
* `zisk/`: checked-out source used as citation/audit material.

It does not currently have:

* an extracted Lean model of `zisk/riscv/src/riscv_interpreter.rs`;
* an extracted Lean model of `zisk/core/src/riscv2zisk_context.rs`;
* a generated, source-drift-checked acceptance predicate for raw instruction
  words.

Therefore a theorem named like ISA coverage can accidentally talk about a
newly invented Lean acceptance predicate rather than the pinned implementation.

## Minimum artifact needed

For each opcode family, we need an authoritative predicate:

```lean
def ZiskAcceptsPinned (inst : BitVec 32) : Prop := ...
```

This predicate must be generated from, extracted from, or executable-checked
against the pinned ZisK source. It must not be hand-written in the proof PR.

For FENCE, the minimum useful predicate is:

```lean
def ZiskAcceptsPinnedFence (inst : BitVec 32) : Prop
```

with source-level meaning:

```text
riscv_get_instruction_32 inst produces RiscvInstruction.inst = "fence"
```

Then the coverage theorem should be:

```lean
theorem fence_isa_coverage
    (h_sail : SailAcceptsFence inst)
    (h_no_bug : not KnownFenceDecodeBug inst) :
    ZiskAcceptsPinnedFence inst
```

Trying to prove the theorem without `h_no_bug` against the current pinned
source should fail, with `0x1000000F` as a concrete witness.

## Viable implementation strategies

### 1. Extract Rust decoder/interpreter to Lean

Translate the relevant subset of `zisk/riscv/src/riscv_interpreter.rs` into
Lean mechanically.

Pros:

* Best proof ergonomics once available.
* The theorem talks directly about implementation logic.
* Scales to all opcodes if the extractor handles enough Rust.

Cons:

* Highest upfront engineering cost.
* Need to define an extraction trust boundary for Rust semantics.
* Existing interpreter uses strings and mutable structs; the extractor likely
  needs a normalized intermediate representation.

Suggested first slice:

```text
riscv_get_instruction_32
  opcode/funct field extraction
  F-type branch
  output enum instead of strings
```

### 2. Generate Lean predicates from audited Rust slices

Write a generator that reads a pinned source slice and emits a Lean predicate
plus a source fingerprint.

For FENCE, it would emit:

```lean
def ZiskAcceptsPinnedFence (inst : BitVec 32) : Prop :=
  opcode inst = 0b0001111#7 ∧
  funct3 inst = 0b000#3 ∧
  inst &&& 0xF00F8F80#32 = 0#32
```

The generator must also emit or check:

```text
source file path
source commit
line/span hash or AST hash
```

Pros:

* Practical for a small first experiment.
* Much harder to accidentally lie than a hand-written predicate.
* Can be made to fail on source drift.

Cons:

* Still a generator trust boundary.
* Needs review rules that forbid editing generated predicates by hand.
* Less general than full Rust extraction.

### 3. Executable oracle with generated witnesses

Compile/run the pinned ZisK decoder on selected raw words and generate Lean
facts for those witnesses.

Pros:

* Fastest way to validate known bugs and fixes.
* Good for regression tests and before/after bug retirement evidence.

Cons:

* Witness facts do not prove universal coverage.
* Needs a second mechanism for the full theorem.

This is still useful as a required guardrail: before retiring any coverage bug,
show a witness that failed on the old pinned implementation and passes on the
new pinned implementation.

## Recommended path

Start with strategy 2 for FENCE only.

1. Add a generator under `tools/` that reads the pinned ZisK interpreter source
   and emits `ZiskFv/Generated/ZiskDecoder/Fence.lean`.
2. Include the source commit and hash of the matched FENCE branch in the
   generated file.
3. Define `ZiskAcceptsPinnedFence` only in the generated file.
4. Update `FenceCoverage.lean` so its coverage theorem imports the generated
   predicate instead of defining one.
5. Add two Lean examples:

   ```lean
   example : SailAcceptsFence 0x1000000F#32 := ...
   example : not ZiskAcceptsPinnedFence 0x1000000F#32 := ...
   ```

6. Keep `KnownFenceDecodeBug` in the theorem until the pinned ZisK source is
   updated to a commit containing the FENCE fix.
7. Once updated, regenerate and require the old negative example to fail or be
   replaced by:

   ```lean
   example : ZiskAcceptsPinnedFence 0x1000000F#32 := ...
   ```

## Gate to prevent recurrence

Add a trust gate that rejects new completeness theorems when the acceptance
predicate is defined in the same non-generated proof file.

Approximate rule:

* theorem name contains `coverage`, `complete`, or `isa`;
* conclusion mentions `Accepts`, `Decode`, `Transpile`, or `Route`;
* the key acceptance predicate is defined outside `ZiskFv/Generated` and not
  listed in an allowlist.

This will not prove correctness, but it catches the exact failure mode from the
FENCE attempt: inventing a decoder in the proof file and proving completeness
about it.
