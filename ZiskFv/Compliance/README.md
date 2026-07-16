# `ZiskFv/Compliance/`

The trust-ledger discharge layer for the RV64IM opcodes, plus the per-arm
`OpEnvelope` glue that the global theorem in `ZiskFv/Compliance.lean` (one level
up) proves. (For exact opcode/wrapper counts, read the tree — `ls
Compliance/Wrappers/*.lean` — rather than a number hard-coded here, which drifts;
see `docs/refactor/05-inconsistencies-and-correctness.md` C4.)

- **`Wrappers/<Op>.lean`** — one wrapper per opcode. Each imports the **core**
  `equiv_<OP>` theorem from `ZiskFv/EquivCore/<Op>.lean` (the
  `execute = bus_effect` form) and produces `ZiskFv.Compliance.equiv_<OP>` in the
  channel-balance form, discharging that core theorem's **promise hypotheses**
  using explicit route facts, row/provider evidence, the remaining non-row-shape
  trust ledger entries, and pure-Lean derivations. The canonical per-opcode
  theorem in `ZiskFv/Equivalence/<Op>.lean` is a thin re-export *above* this
  wrapper (it imports `Compliance.Wrappers.<Op>`), not something the wrapper
  consumes — the dependency runs `EquivCore → Wrappers → Equivalence`. The
  wrapper's parameter surface is the *minimal* caller-burden remaining after
  discharge. (The generated caller-burden ledgers that once drift-guarded this
  surface were retired when the discharge campaign reached 0 project axioms —
  see the retirement note in `trust/README.md`; the kept axiom-closure
  baselines under `trust/generated/` mechanically prevent soundness
  regression.)

The global theorem `zisk_riscv_compliant_program_bus` lives in
`ZiskFv/Compliance.lean` (the file at the level above this folder). `OpEnvelope`
is an inductive with one arm per opcode; its `exec_eq` conclusion is a
`True`-padded conjunction of the two envelope trust facts and the ten per-family
`exec_eq_<family>` statements: for any arm, *exactly one* family fires
with a real channel-balance statement and the others are `True`. It is therefore
not a case-returning dispatch on a sum type, even though the arms partition the
opcodes; the padded-conjunction encoding is an implementation detail (see
`docs/refactor/02-clean-idioms-and-usage.md` D3). The ten
`Compliance/Dispatch/<family>.lean` files each prove their family's conjunct.

Note: `zisk_riscv_compliant_program_bus` is an **internal** per-arm
channel-balance lemma, not the advertised audit endpoint. The public soundness
theorem is `ZiskFv.Compliance.root_soundness` (`ZiskFv/Soundness.lean`), gathered
with completeness in the single audit surface `ZiskFv/Audit.lean`.

To audit a single opcode's trust closure, read `Compliance/Wrappers/<Op>.lean`
together with the core `EquivCore/<Op>.lean` it discharges; the diff between the
two is exactly the promise hypotheses discharged from the ledger.
