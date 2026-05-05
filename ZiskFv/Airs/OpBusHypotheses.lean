import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OpBusEffect

/-!
# OpBusHypotheses — Sail-state register-read derivation from the op-bus

Partner module to `Airs/BusHypotheses.lean`. Where `BusHypotheses.lean`
extracts `read_xreg`-equalities from the **memory-bus** precondition for
the standard ALU/jump/load/store shapes (where the Main memory bus
carries register and memory reads), this module extracts the analogous
equalities from the **operation-bus** precondition for the branch shape
(where the Main memory bus is empty and rs1/rs2 reads route through the
Binary state machine via the operation bus).

This is the Track Q POC closure: the branch-family metaplan theorems
can now drop their scenario-binding `h_input_r1` / `h_input_r2`
parameters in favour of a single `h_op_bus : (op_bus_effect ...).1`
hypothesis.

Only the **branch** shape ships here (one Main-emitted op-bus entry,
multiplicity = 1, lanes carry `xreg rs1` / `xreg rs2`). Future tracks
can extend with shapes for jump-pseudo-NOP routing or mul/div op-bus
hops; the same pattern applies.

**Axiom budget.** No new project-level axioms (no new
`transpile_<OP>` or trust-base entries). The `chip_op_bus_hyps_branch`
proof transitively pulls in `Lean.ofReduceBool` and `Lean.trustCompiler`
beyond the `_from_bus` set — both are standard Lean kernel axioms used
by `DecidableEq (Fin GL_prime)` instance-resolution when the proof
rewrites the `if entry.multiplicity = (1 : FGL)` conditional via
`if_pos`. They are *not* part of the project's trust base.
-/

namespace ZiskFv.Airs.OpBusHypotheses

open Goldilocks
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.OpBusEffect

/-- **Branch shape — single op-bus entry.** Given the structural
    hypothesis `entry.multiplicity = 1` (Main's assume-side branch
    emission), the op-bus precondition `.1` decomposes into the two
    register-read equalities for `rs1` and `rs2`.

    The `BitVec 64` value on the right of each `read_xreg` equality is
    reassembled from the bus's lane fields via `lanes_to_bv64` — this
    matches the convention `transpile_BEQ` enforces on the Main row,
    namely `a_0 = lane_lo (xreg rs1)` / `a_1 = lane_hi (xreg rs1)`,
    and analogously for `b`. The op-bus simply forwards Main's `a`/`b`
    cells (modulo the `(1 - m32)` factor on the high lanes, which for
    branches collapses since `m32 = 0`).

    This is the branch-shape companion to `chip_bus_hyps_branch_rrw`
    in `BusHypotheses.lean`: the latter extracts the *PC* read from the
    memory-bus `.1`; this lemma extracts the *register* reads from the
    op-bus `.1`. Together they cover the full register-state
    precondition the Sail-side spec needs. -/
theorem chip_op_bus_hyps_branch
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : OperationBusEntry FGL)
    (rs1 rs2 : Fin 32)
    (h_mult : entry.multiplicity = 1)
    (h_op_bus : (op_bus_effect [entry] state rs1 rs2).1) :
    read_xreg rs1 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.a_lo entry.a_hi) state
    ∧ read_xreg rs2 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.b_lo entry.b_hi) state := by
  -- Unfold the singleton fold and the leading `if entry.multiplicity = 1`
  -- branch. We avoid `decide`-based reduction (which would pull
  -- `Lean.ofReduceBool` / `Lean.trustCompiler` into the axiom set) by
  -- routing through `if_pos h_mult` after the structural unfolds.
  unfold op_bus_effect at h_op_bus
  rw [List.foldl_cons, List.foldl_nil, if_pos h_mult] at h_op_bus
  exact ⟨h_op_bus.2.1, h_op_bus.2.2⟩

/-- **ALU shape — single op-bus entry.** Identical extraction to
    `chip_op_bus_hyps_branch`: the ALU family (RTYPE/ITYPE/RTYPEW +
    ADDIW) emits a single Main↔Binary or Main↔Arith op-bus entry with
    `multiplicity = 1` (`is_external_op = 1` for ALU rows per
    `transpile_ADD` and friends), with rs1 on the `a` lanes and rs2 on
    the `b` lanes — the same lane convention as the branch shape. The
    rd write happens via the *memory* bus, not the op bus, so this
    lemma only extracts the input-read equalities (rs1, rs2).
    Provided as a name-aliased re-export of `chip_op_bus_hyps_branch`
    so callers in the ADD / SUB / AND / … fan-out can read the proof
    documentation as ALU-specific. -/
theorem chip_op_bus_hyps_alu
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : OperationBusEntry FGL)
    (rs1 rs2 : Fin 32)
    (h_mult : entry.multiplicity = 1)
    (h_op_bus : (op_bus_effect [entry] state rs1 rs2).1) :
    read_xreg rs1 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.a_lo entry.a_hi) state
    ∧ read_xreg rs2 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.b_lo entry.b_hi) state :=
  chip_op_bus_hyps_branch state entry rs1 rs2 h_mult h_op_bus

/-- **Load shape — single op-bus entry, single rs1 read on a-lanes.**
    LD/LB/LH/LW/LBU/LHU/LWU emit a Main↔Binary op-bus entry whose `a`
    lanes carry `xreg(rs1)` (the address-base register) per
    `transpile_LD` / `transpile_LW` / etc. The `b` lanes are pinned to
    the immediate (not a register), so this lemma extracts only the
    rs1 read.
    Caller convention: invoke with `rs1` supplied as both the `r1` and
    `r2` arguments to `op_bus_effect` (the `b`-side equality is
    discarded). Re-uses the existing branch-shape `op_bus_effect`. -/
theorem chip_op_bus_hyps_load
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : OperationBusEntry FGL)
    (rs1 : Fin 32)
    (h_mult : entry.multiplicity = 1)
    (h_op_bus : (op_bus_effect [entry] state rs1 rs1).1) :
    read_xreg rs1 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.a_lo entry.a_hi) state :=
  (chip_op_bus_hyps_branch state entry rs1 rs1 h_mult h_op_bus).1

/-- **Store shape — single op-bus entry, two reads (rs1 + rs2).**
    SD/SB/SH/SW emit a Main↔internal-copyb microinstruction with
    `is_external_op = 0` — meaning **the op-bus emission for stores has
    multiplicity 0**, not 1. The transpile axioms (`transpile_SD` and
    siblings) confirm this: stores route their rs1/rs2 reads via the
    *memory bus* exclusively (shape (e) `chip_bus_hyps_store_rrrw`),
    not the operation bus.
    Provided here as a documentation-only stub: the *signature* mirrors
    `chip_op_bus_hyps_alu` so callers can pattern-match on the same
    shape, but in practice store-family equiv theorems should derive
    rs1/rs2 reads from the memory bus rather than the op-bus. The
    op-bus precondition for stores collapses to the trivial `True`
    (multiplicity-0 entries are no-ops in `op_bus_effect`); this lemma
    therefore re-states `chip_op_bus_hyps_alu` for the rare case a
    caller wants to ride a `multiplicity = 1` op-bus entry alongside
    a store row. -/
theorem chip_op_bus_hyps_store
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : OperationBusEntry FGL)
    (rs1 rs2 : Fin 32)
    (h_mult : entry.multiplicity = 1)
    (h_op_bus : (op_bus_effect [entry] state rs1 rs2).1) :
    read_xreg rs1 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.a_lo entry.a_hi) state
    ∧ read_xreg rs2 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.b_lo entry.b_hi) state :=
  chip_op_bus_hyps_branch state entry rs1 rs2 h_mult h_op_bus

/-- **JALR shape — single op-bus entry, single rs1 read on b-lanes.**

    JALR's `transpile_JALR` axiom pins `m.b_0 = lane_lo (xreg rs1)`
    and `m.b_1 = lane_hi (xreg rs1)` — the JALR row carries its single
    source register on the `b` lanes (rather than `a` as the branch
    family does). Modelling the op-bus emission analogously, this
    lemma extracts the `read_xreg rs1` equality from the `b`-lane half
    of the op-bus precondition.

    Caller convention: invoke with `rs1` supplied as both the `r1`
    and `r2` arguments to `op_bus_effect` (the `a`-side equality is
    discarded; the `b`-side equality is the JALR rs1 read). This
    re-uses the existing branch-shape `op_bus_effect` definition
    without adding a new variant.

    The `BitVec 64` value on the right of the equality is reassembled
    from the bus's `b_lo`/`b_hi` lane fields via `lanes_to_bv64`,
    matching `transpile_JALR`'s `b_0`/`b_1` pinning. -/
theorem chip_op_bus_hyps_jalr
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (entry : OperationBusEntry FGL)
    (rs1 : Fin 32)
    (h_mult : entry.multiplicity = 1)
    (h_op_bus : (op_bus_effect [entry] state rs1 rs1).1) :
    read_xreg rs1 state
        = EStateM.Result.ok
            (Goldilocks.lanes_to_bv64 entry.b_lo entry.b_hi) state :=
  (chip_op_bus_hyps_branch state entry rs1 rs1 h_mult h_op_bus).2

end ZiskFv.Airs.OpBusHypotheses
