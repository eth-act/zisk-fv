import ZiskFv.AirsClean.BinaryExtension.StaticCircuit

/-!
# Consumer-facing BinaryExtension interface

The row-level consumer API is `BinaryExtensionRow`, `rowA64`, `rowA32`,
`rowShiftAmount`, `rowShiftAmount32`, `opBusMessage`, and the static/shift
component facts exported by `StaticCircuit`.

## Q2 constraint correspondence

| Legacy obligation | Clean operation |
|---|---|
| No F-typed `core_every_row` predicates | `BinaryExtension.main` has no `assertZero` |
| Byte 0 BinaryExtensionTable interaction | first pull/direct lookup, byte index 0 |
| Byte 1 BinaryExtensionTable interaction | second pull/direct lookup, byte index 1 |
| Byte 2 BinaryExtensionTable interaction | third pull/direct lookup, byte index 2 |
| Byte 3 BinaryExtensionTable interaction | fourth pull/direct lookup, byte index 3 |
| Byte 4 BinaryExtensionTable interaction | fifth pull/direct lookup, byte index 4 |
| Byte 5 BinaryExtensionTable interaction | sixth pull/direct lookup, byte index 5 |
| Byte 6 BinaryExtensionTable interaction | seventh pull/direct lookup, byte index 6 |
| Byte 7 BinaryExtensionTable interaction | eighth pull/direct lookup, byte index 7 |
| Operation-bus permutation row | `OpBusChannel.push (opBusMessageExpr row)` |
| Shift `b_0` bits(24) declaration | `rangeTable24` lookup in the shift-only static component |

The byte tuples use the same opcode, byte index, input byte, shift amount,
low/high output bytes, and `op_is_shift` selector.  BinaryExtension has no
omitted algebraic constraint: its semantics are table-driven.  The shift
range is correctly restricted to the shift component rather than imposed on
generic extension rows.  There is no constraint semantic divergence.

The surviving transitive compatibility import is deliberate for this slice:
`StaticCircuit.lean` currently contains proved static-table projections whose
statement dependencies are declared in `Bridge.lean`; separating that import
cycle requires moving those projections, which in turn touches the shared
Binary-family balance implementation.  The clean row API above remains the
consumer-facing seam.
-/
