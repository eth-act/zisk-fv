import ZiskFv.AirsClean.MemAlign.Circuit

/-!
# MemAlign consumer interface and Q2 audit

The consumer-facing row-local API is `MemAlignRow`, `Spec`, and
`memBusMessageExpr`.

## Q2 correspondence

Legacy `boolean_wr`, `boolean_reset`, `boolean_sel_up_to_down`,
`boolean_sel_down_to_up`, and `boolean_sel_0` through `boolean_sel_7` map
one-for-one to the first twelve `assertZero` operations in `main`.
`boot_pc_zero`, `sel_prove_disjoint`, `value_0_reconstruction`, and
`value_1_reconstruction` map one-for-one to the remaining four assertions.
The memory-bus permutation tuple maps to the component's
`MemBusChannel.push (memBusMessageExpr row)`.

**Verified deletion blocker:** legacy `delta_addr_definition` and the eight
`down_to_up_continuity_N` predicates are cross-row constraints.  The Clean
row-local `main` intentionally omits them; `Spec.lean` explicitly assigns them
to the coupled data-memory/cross-row layer.  That layer is out of scope for
this work order, so deleting `Valid_MemAlign`, its legacy model, or the bridge
would discard nine constraints.  They therefore survive pending the data
memory migration.
-/
