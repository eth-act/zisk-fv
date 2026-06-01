import Mathlib

import ZiskFv.EquivCore.Fence
import ZiskFv.EquivCore.Promises.Fence
import ZiskFv.SailSpec.fence
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_FENCE` Compliance wrapper — ControlFlow non-branch shape

> **Status:** within-shape wrapper, derived mechanically from
> `Wrappers/Lui.lean`. Lives outside the canonical
> surface so V1 anti-laundering metrics on the canonical theorem
> are unaffected.

## Why FENCE is trivial

FENCE is the *lightest* ControlFlow non-branch opcode:

* No `rs1` / `rs2` semantic read (the Sail aux body collapses to
  `pure ()` via `sail_barrier`); no operand bridge (category 5 N/A).
* No `rd` write (no memory-bus rd-write entry; no lane-match category 1).
* No immediate / no PC offset arithmetic (no range/bound category 4).
* No mode columns on a provider AIR (no provider AIR; category 2 N/A).
* No sign-witness pins (category 3 N/A).

The canonical `equiv_FENCE` already carries *zero* promise
hypotheses on the trust side — it consumes only the Sail-state
predicates `h_input_pc` + `h_input_priv` (both SPEC-PRE) plus the
shape-(b) bus-protocol pins (also pass-through). This wrapper is
therefore a **pure canonical-naming pass** at the per-opcode level;
the value it adds is at the global `Compliance.lean` level where
`(main, r_main)` collapse into shared parameters across all
ControlFlow opcodes.

## 5-category discharge applied to FENCE

All five categories are N/A for FENCE; the wrapper exposes the same
parameter surface as the canonical theorem, decorated with the
Compliance-handshake activation/opcode pins (`h_main_active`,
`h_main_op_fence`) that Compliance.lean delivers from the Main AIR's
ROM handshake on the row hosting the FENCE instruction. These pins
are **not consumed** in the proof body — they are tracked here so
the Compliance dispatcher's per-row identification of the opcode
stays uniform across the shape.

## Anti-laundering report

* **No new axioms.** This wrapper consumes only `equiv_FENCE`'s
  existing closure. Trust ledger unchanged at the current baseline.
* **No new bridges.**
* **Caller-burden** — see the count below.

## Caller-burden

`equiv_FENCE` (canonical): 11 binders / 6 hypotheses.
`equiv_FENCE` (this file): 13 binders / 8 hypotheses.

The wrapper grows by **+2 binders / +2 hypotheses** because we
introduce the Compliance-handshake `main : Valid_Main` validator and
its `r_main` row index plus `h_main_active` / `h_main_op_fence`. At
the *global* Compliance.lean level these collapse into shared
parameters across all eleven ControlFlow opcodes (and across the
Main-only and Mem-shape opcodes), so the global trust footprint
strictly shrinks. This is the **structural-unpacking pattern**
documented in `trust/structural-unpacking-exceptions.txt` (FENCE is
not on that list because the unpacking happens only in this
Compliance wrapper, not in the canonical theorem).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main


/-- **Compliance wrapper for `equiv_FENCE`.** Pass-through plus
    Compliance-handshake activation pins.

    Caller obligations:
    1. Sail-side inputs (`state`, `fence_input`, `fm`, `pred`,
       `succ`, `rs`, `rd`).
    2. AIR validator + row index (`main : Valid_Main`, `r_main : ℕ`).
       Compliance.lean shares `main` across all Main-only opcodes.
    3. Structural bus row (`exec_row`).
    4. Activation + opcode pins on Main (`h_main_active`,
       `h_main_op_fence`). Both come from Compliance.lean's
       ROM handshake on the row hosting FENCE. Carried through for
       Compliance-level uniformity; not consumed by the per-opcode
       proof body (FENCE's Sail-side reduction is independent of the
       provider AIR — there is no provider AIR).
    5. Sail-state predicates (SPEC-PRE) — `h_input_pc`,
       `h_input_priv`.
    6. Bus-shape structural pins — `h_exec_len`, `h_e0_mult`,
       `h_e1_mult`, `h_nextPC_matches`. -/
lemma equiv_FENCE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    -- AIR validator + row index. Compliance.lean shares `main`.
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    -- Activation / opcode pins (Compliance-handshake; tracked here
    -- for uniformity but not consumed by the proof body since FENCE
    -- has no provider AIR).
    (_pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_FLAG)
    -- Structural promise bundle (6 fields, see Promises/Fence.lean).
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = (bus_effect exec_row [] state).2 :=
  ZiskFv.EquivCore.Fence.equiv_FENCE
    state fence_input fm pred succ rs rd exec_row promises

end ZiskFv.Compliance
