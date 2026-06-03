import ZiskFv.Transpiler.Contract

/-!
Compatibility import for the retired trusted transpiler contract.

The old `transpiler_*` axioms and `transpile_*` theorem wrappers have been
removed. Existing imports keep working because the live opcode literals, lane
helpers, and `Transpiler.wrap_to_regidx` definitions now live in
`ZiskFv.Transpiler.Contract`.
-/
