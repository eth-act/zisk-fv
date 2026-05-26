import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryExtension

/-!
# OperationBus permutation soundness — consolidated bus-level axiom

This file replaces the three per-provider axioms
(`op_bus_perm_sound_BinaryAdd`, `op_bus_perm_sound_Binary`,
`op_bus_perm_sound_BinaryExtension`) with one bus-level axiom
`op_bus_permutation_sound`, parameterized over an `OpBusProvider`
sum type that ranges over the three provider AIRs.

The three per-provider results survive in `Bridge.lean` as
**theorems** with their original names and signatures — downstream
consumers (per-AIR discharge bridges, Compliance wrappers) require
no changes.

## Why consolidate

The three per-provider axioms have identical shape (Main consumer
row pairs with a provider row, given activation + opcode pin). Only
the provider AIR type and its opcode coverage differ. The axiom
content is the same cryptographic claim — "the operation bus's
permutation argument is sound" — specialized to three providers.
Stating it once at the bus layer makes the trust assumption more
semantically precise and shrinks the trust ledger by 2 named axioms
(3 → 1).

## Trust class

PLONK / logUp permutation-argument soundness on
`OPERATION_BUS_ID = 5000`. Same scope as the three per-provider
axioms it replaces, and same scope as
`lookup_consumer_matches_provider_load` (memory bus).

PIL citation: `zisk/pil/opids.pil:2` (`OPERATION_BUS_ID = 5000`).
Protocol soundness lives in
`pil2-stark/src/permutation_check.rs` (the verifier-side
soundness proof of the permutation construction).
-/

namespace ZiskFv.Airs.OperationBus

open Goldilocks


/-- An operation-bus provider: one of the three secondary state
    machines (BinaryAdd / Binary / BinaryExtension) that
    `proves_operation` on the operation bus.

    This is a transparent enumeration (3 arms) — no hidden
    hypotheses. The destructuring `def`s below are `@[reducible]`
    so V2's `whnfR` walker can unfold them when auditing forbidden
    binder types. -/
inductive OpBusProvider : Type
  | binaryAdd
      (b : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) : OpBusProvider
  | binary
      (b : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) : OpBusProvider
  | binaryExtension
      (e : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) :
        OpBusProvider

/-- The provider's row at index `r`, projected onto the
    operation-bus message tuple. -/
@[reducible]
def OpBusProvider.opBus_row : OpBusProvider → ℕ → OperationBusEntry FGL
  | .binaryAdd b, r => opBus_row_BinaryAdd b r
  | .binary b, r => opBus_row_Binary b r
  | .binaryExtension e, r => opBus_row_BinaryExtension e r

/-- The opcode coverage for each provider — the disjunction the
    consumer's `op` must satisfy for that provider to be the
    handler. Mirrors the `h_op` disjunctions on the old per-provider
    axioms. -/
@[reducible]
def OpBusProvider.handles_op : OpBusProvider → FGL → Prop
  | .binaryAdd _, op => op = 10
  | .binary _, op =>
      op = 0x02 ∨ op = 0x03 ∨ op = 0x04 ∨ op = 0x05 ∨ op = 0x06
      ∨ op = 0x07 ∨ op = 0x08 ∨ op = 0x09 ∨ op = 0x0a ∨ op = 0x0b
      ∨ op = 0x0c ∨ op = 0x0d ∨ op = 0x0e ∨ op = 0x0f ∨ op = 0x10
      ∨ op = 0x12 ∨ op = 0x13 ∨ op = 0x14 ∨ op = 0x15 ∨ op = 0x16
      ∨ op = 0x17 ∨ op = 0x18 ∨ op = 0x19 ∨ op = 0x1a ∨ op = 0x1b
      ∨ op = 0x1c ∨ op = 0x1d ∨ op = 0x50 ∨ op = 0x51
  | .binaryExtension _, op =>
      op = 0x21 ∨ op = 0x22 ∨ op = 0x23 ∨ op = 0x24 ∨ op = 0x25
      ∨ op = 0x26 ∨ op = 0x27 ∨ op = 0x28 ∨ op = 0x29

-- `op_bus_permutation_sound` axiom retired in T4-purge P6. All global-theorem
-- opcode routes now use row-explicit static-lookup paths (Clean ensemble +
-- static BinaryTable / BinaryExtensionTable membership) instead of the
-- bus-level permutation axiom. The retirement landed once the 5 ADD/ADDI/LB/LH/LW
-- canonical theorems migrated to the row-explicit signature; the 12 shifts
-- had already been on the static-lookup route.

end ZiskFv.Airs.OperationBus
