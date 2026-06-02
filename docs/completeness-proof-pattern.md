# Completeness proof pattern notes

## Failure that prompted this note

During the FENCE coverage work, we accidentally proved a statement about a
hand-written Lean decoder model instead of the pinned ZisK implementation
decoder/transpiler.

The bad shape was:

```lean
def SailFenceEncoding ...
def decodeFence ...

theorem decode_fence_complete
    (h_sail : SailFenceEncoding inst) :
    decodeFence inst = some (rawFenceInst inst)
```

This theorem was easy because `decodeFence` was defined in the proof branch to
accept exactly the Sail FENCE cases under discussion. That is not implementation
coverage. It only proves that a newly introduced model is internally consistent.

The upstream implementation evidence contradicted the conclusion: current ZisK
rejects some Sail-valid FENCE encodings, and PR `0xPolygonHermez/zisk#993`
exists to fix that. Therefore the proof retired a real known-bug gate without
being tied to the implementation version where the bug is fixed.

## Distinction we must preserve

Per-op semantic equivalence:

```lean
execute_instruction (instruction.FENCE fields) state
  = state_effect_via_channels rows state
```

This is a statement about an instruction constructor after classification. For
FENCE it can be true for all `fm`, `pred`, `succ`, `rs1`, and `rd`.

ISA coverage:

```lean
SailValidEncoding inst ->
  realZiskDecodeOrTranspile pinnedZisk inst = some supportedRoute
```

This is a statement about raw instruction acceptance by the pinned
implementation. It cannot be proved from the per-op theorem alone.

## Non-negotiable rule

Completeness proofs must not introduce a hand-written implementation acceptance
predicate and then prove coverage against it.

Any predicate named like an implementation decoder, support set, accepted
encoding set, transpiler classifier, or route selector must be one of:

1. extracted/generated from the pinned implementation;
2. imported from a checked executable artifact tied to the pinned implementation;
3. a small finite table copied from implementation source with an explicit
   source-location audit and a test that detects source drift;
4. explicitly marked as a spec-side predicate, never used to retire an
   implementation coverage defect.

## Required theorem shape

Every opcode coverage theorem should expose three predicates:

```lean
def SailAccepts_OP (inst : BitVec 32) : Prop := ...
def ZiskAccepts_OP_pinned (inst : BitVec 32) : Prop := ...
def KnownBug_OP (inst : BitVec 32) : Prop := ...
```

The completeness theorem should have the shape:

```lean
theorem zisk_OP_isa_coverage
    (h_sail : SailAccepts_OP inst)
    (h_no_bug : not KnownBug_OP inst) :
    ZiskAccepts_OP_pinned inst
```

Retiring a bug means removing or shrinking `KnownBug_OP`, not weakening
`SailAccepts_OP` and not replacing `ZiskAccepts_OP_pinned` with a new model.

## Required failure test before retirement

Before retiring any known coverage defect, record a negative witness for the
old pinned implementation:

```lean
example : SailAccepts_OP badInst := ...
example : KnownBug_OP badInst := ...
example : not ZiskAccepts_OP_pinned badInst := ...
```

After the implementation fix is pinned/imported, the last example must fail or
be replaced by:

```lean
example : ZiskAccepts_OP_pinned badInst := ...
```

Without this before/after witness, do not retire the defect.

## FENCE-specific lesson

Sail generic FENCE accepts encodings that current ZisK rejects before routing.
The problematic fields include at least nonzero `fm`, `rs1`, and `rd`, per the
upstream fix PR. The semantic proof that FENCE is a no-op for all fields is not
evidence that current ZisK accepts all those raw encodings.

For FENCE, the right split is:

```lean
-- Semantic, after classification:
equiv_FENCE : all fields -> semantic no-op equivalence

-- Coverage, before classification:
zisk_FENCE_isa_coverage :
  SailFenceEncoding inst ->
  not CurrentZiskFenceRejects inst ->
  CurrentZiskAcceptsFence inst
```

The current implementation defect should remain until the FV repository is
explicitly pinned to a ZisK version containing the fix, or until the actual
pinned decoder/transpiler has been imported and proves acceptance.

## Review checklist

For every completeness PR:

1. Identify the authoritative implementation artifact and pinned commit.
2. Show where `ZiskAccepts_OP_pinned` comes from.
3. Search the diff for newly introduced decoder/support predicates.
4. Reject any theorem whose key acceptance conclusion unfolds to a function
   introduced in the same PR unless that function is generated or audited.
5. Include at least one known positive raw encoding and one known negative or
   bug-gated raw encoding.
6. Verify that the known-bug ledger changes are justified by implementation
   evidence, not by a spec-only semantic theorem.
