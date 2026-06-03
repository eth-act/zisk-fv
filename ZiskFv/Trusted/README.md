# `ZiskFv/Trusted/`

This directory no longer contains the RV64-to-ZisK transpiler trust surface.
`Transpiler.lean` is an axiom-free compatibility import for older module paths;
the live opcode literals, lane helpers, and register-pointer decoding helper
are defined in `ZiskFv/Transpiler/Contract.lean`.

The current source trust ledger is generated in
`trust/generated/baseline-axioms.txt`; see `trust/trusted-base.md` for the
current per-class breakdown.
