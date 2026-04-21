# Upstream issue: `currentlyEnabled Ext_Zca` simp normalization under known `misa[2]`

**Target repo:** `NethermindEth/sail-riscv-lean` (filed as issue, not PR)

**ZisK-fv site:** `ZiskFv/ZiskFv/RV64D/Auxiliaries.lean:751-762` (`jump_to_equiv`)

## Title

`currentlyEnabled Ext_Zca` blocks `simp` in callers under a hypothesis fixing `misa[2]`

## Body

### Summary

In proofs that sequence Sail's `jump_to` under the assumption that the RISC-V C
extension is disabled (`misa[2] = 0`), `simp` cannot reduce
`currentlyEnabled Ext_Zca` to a closed form even though every branch of the
recursion ultimately depends only on the concrete `misa` bit. This forces
callers to fall back to manual unfolding of mutually-recursive matches and
pushes the `SailME.run` bind by hand, which is impractical at scale.

### Minimal reproduction

```lean
import LeanRV64D

open LeanRV64D LeanRV64D.Functions

-- Target hypothesis: ZisK targets RV64IM, so bit 2 of misa (the `C` bit) is 0.
example
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (misa_val : RegisterType Register.misa)
    (h_misa : state.regs.get? Register.misa = .some misa_val)
    (h_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    (currentlyEnabled Ext_Zca : SailM Bool) state
      = EStateM.Result.ok false state := by
  -- Expected: simp should be able to close this using h_c to trace through
  -- Ext_Zca → Ext_C → misa[2] = 0 and evaluate the bind chain.
  -- Actual: simp makes no progress; manual unfolding is required for every
  -- downstream caller (e.g. jump_to_equiv, which has ~8 transitive callers).
  sorry
```

### Observed locations

Auto-generated definitions (BaseInsts / Types) the blocker traverses:

- `LeanRV64D.Functions.jump_to` (BaseInsts.lean:231-241): calls
  `currentlyEnabled Ext_Zca` inside a `SailME.run do` block.
- `LeanRV64D.Functions.currentlyEnabled` (Types.lean:466, mutual block):
  - `Ext_Zca → hartSupports Ext_Zca && (currentlyEnabled Ext_C || not (hartSupports Ext_C))`
  - `Ext_C  → hartSupports Ext_C && _get_Misa_C (← readReg misa) == 1#1`
- `LeanRV64D.hartSupports` (Extensions.lean:637): `Ext_Zca ↦ true`,
  `Ext_C ↦ hartSupports Ext_Zca && ...`.
- All of the above are Sail-auto-translated — no hand simp lemmas exist.

The block is structurally simple: given `h_c`, every downstream branch
evaluates to `false`, but `simp` doesn't have the lemma set to thread
`readReg misa = some misa_val ∧ extractLsb misa_val 2 2 = 0#1` through the
`SailME.run` bind.

### Downstream impact (in ZisK-fv)

One local `sorry` in `jump_to_equiv`. Transitively blocks equivalence proofs
for: `beq`, `bne`, `bge`, `bgeu`, `blt`, `bltu`, `jal`, `jalr` (8 files).

### Suggested fix

Either (equally acceptable):

1. **`@[simp]` normalization lemmas** in a `LeanRV64D.Lemmas` module that
   convert `SailME.run do _ ← currentlyEnabled e ; k` into a form `simp` can
   thread given a `readReg misa = _` hypothesis. Specifically:

   ```lean
   @[simp] lemma bind_currentlyEnabled_Ext_C_of_misa_bit_zero
       (h_misa : readReg misa state = EStateM.Result.ok misa_val state)
       (h_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
       (do let b ← currentlyEnabled Ext_C; k b) state
         = k false state

   @[simp] lemma bind_currentlyEnabled_Ext_Zca_of_misa_bit_zero
       (h_misa : readReg misa state = EStateM.Result.ok misa_val state)
       (h_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
       (do let b ← currentlyEnabled Ext_Zca; k b) state
         = k (hartSupports Ext_Zca && not (hartSupports Ext_C)) state
   ```

2. **Simp-attribute on the `currentlyEnabled` definition itself** plus enough
   `readReg` / `_get_Misa_C` / `bool_to_bits` lemmas to let `simp` evaluate
   the match automatically given `h_misa` and `h_c` in scope.

Happy to send a PR if either approach is preferred.

### Environment

- `sail-riscv-lean` commit: `81c8c84f919b6b565790713e2049a88b88739cda` (pinned as `rev = "main"` in downstream `lakefile.toml`)
- Lean 4 toolchain: `leanprover/lean4:v4.26.0`
- Mathlib: `v4.26.0`

---

## Filing checklist

- [ ] Fill in the environment section above (lean-toolchain, lakefile deps,
      sail-riscv-lean rev).
- [ ] Confirm the minimal-repro example actually reproduces (build it in a
      scratch Lean file if unsure).
- [ ] `gh issue create --repo NethermindEth/sail-riscv-lean --title "..."
      --body-file docs/fv/upstream-issues/sail-riscv-lean-ext-zca-simp.md`
      (edit the file to remove this checklist block first).
- [ ] Add the issue URL to `ZiskFv/RV64D/Auxiliaries.lean` TODO comment
      (lines 745-750).
- [ ] Note the filing in the Phase 1.5 CLOSED section.
