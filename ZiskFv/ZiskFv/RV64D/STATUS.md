# ZiskFv.RV64D Port Status

**Phase 1 Track A** — port of `OpenvmFv.RV32D` (openvm-fv, `rv32d` branch of
`sail-riscv-lean`) to `ZiskFv.RV64D` (zisk-fv, `main` branch of
`sail-riscv-lean` → module `LeanRV64D`).

## File-level status

| Opcode / File           | Port status | Build state                      | Sorry reason |
|-------------------------|-------------|-----------------------------------|--------------|
| Auxiliaries             | ported      | builds with 1 sorry               | `jump_to_equiv` blocked on monadic-`currentlyEnabled` simp normalization (see below) |
| BusEffect               | ported      | blocked on Track B (`Fundamentals.Interaction`) | 4→8 byte widening required once Track B finalizes `MemoryBusEntry` |
| add                     | ported, full proof | blocked on Track B (`Fundamentals.Execution`) | — (most-progressed proof intact; no `sorry` in add.lean body) |
| addi                    | ported      | blocked on Track B                | equivalence proof `sorry` — relied on RV32-width tactics |
| and                     | ported      | blocked on Track B                | equivalence proof `sorry` |
| andi                    | ported      | blocked on Track B                | equivalence proof `sorry` |
| auipc                   | ported      | builds (`sorry` on equivalence)   | equivalence proof `sorry` — RV32 `interval_cases` enumeration |
| beq, bne, bge, bgeu, blt, bltu | ported | build (`sorry` on equivalence) | equivalence proofs `sorry` — branch proofs used `jump_to_equiv` whose RV64 form needs misa-C hypothesis plumbing |
| div, divu, rem, remu    | ported      | blocked on Track B                | equivalence proofs `sorry` |
| jal, jalr               | ported      | build (`sorry` on equivalence)    | equivalence proofs `sorry` — depend on `jump_to_equiv` |
| lb, lbu, lh, lhu, lw    | ported, `range` lemma full | build (`sorry` on equivalence) | LOAD proofs used RV32 arithmetic bounds; need RV64 re-tuning |
| lui                     | ported      | builds (`sorry` on equivalence)   | — |
| mul, mulh, mulhsu, mulhu | ported     | blocked on Track B                | equivalence proofs `sorry` |
| or, ori, xor, xori      | ported      | blocked on Track B                | equivalence proofs `sorry` |
| sb, sh, sw              | ported, `range` lemma full | build (`sorry` on equivalence) | STORE proofs same as LOAD |
| sll, slli, srl, srli, sra, srai | ported | blocked on Track B           | equivalence proofs `sorry` |
| slt, slti, sltiu, sltu  | ported      | blocked on Track B                | equivalence proofs `sorry` |
| sub                     | ported      | blocked on Track B                | equivalence proofs `sorry` |
| addw, subw, sllw, srlw, sraw | RV64-only stub | build (3 sorries each)       | Phase 3 stub per task plan |
| addiw, slliw, srliw, sraiw | RV64-only stub | build (3 sorries each)         | Phase 3 stub per task plan |
| ld, sd, lwu             | RV64-only stub | build (3 sorries each)         | Phase 3 stub per task plan |

## Totals

- **47** RV32IM files mechanically ported (widths widened, namespaces rewritten)
- **12** RV64-only stubs created (Phase 3 placeholders)
- **1**  `sorry` in `Auxiliaries.lean` (`jump_to_equiv`) — blocks branch/jump equivalence proofs
- **43** RV32IM equivalence lemmas carry `sorry` in their proof body (pure spec intact)
- `add.lean` keeps the most-progressed proof with **no `sorry` in file body** (blocked on Track B import of `Fundamentals.Execution`)

## Specific upstream issues (Phase 1.5 / mentally filed)

1. **`LeanRV64D.Functions.currentlyEnabled Ext_Zca` simp normalization.**
   The RV64 definition routes through `currentlyEnabled Ext_C`, which reads
   `misa[2]`. Under ZisK's `misa[2] = 0` assumption the whole subtree reduces
   to `false`, but simp cannot push the constant-propagation through
   `SailME.run`'s bind at the current lemma-unfold granularity. A future
   upstream `@[simp] lemma currentlyEnabled_reg_read_simp` that converts
   `(... ← currentlyEnabled e ...)` into a closed form, or an equivalent
   local `bind_currentlyEnabled` lemma in `Auxiliaries.lean`, would unblock
   `jump_to_equiv`, the branch equivalence proofs, and the jump equivalence
   proofs.

2. **RV64 `execute_LOAD` / `execute_STORE` arithmetic guard shape.**
   The RV32D `arithmetic_helper` lemma (`(a + b) < 2^29 → (a+b) % 2^32 = ...`)
   was sufficient because all post-add arithmetic operated in
   `BitVec 32 → Int`. In RV64 the post-add modulus is `2^64`, and the three
   conjuncts needed for the LOAD/STORE proof differ. The helper is ported
   literally and still typechecks; the *caller-side* omega steps (around
   `if_pos (by omega)` for the PMA size check) need their bounds re-derived
   for 64-bit addresses. Left pending because all load/store proofs need
   this at once — cleaner to do in one pass.

3. **`MemoryBusEntry` width.**
   Track B owns `Fundamentals/Interaction.lean`; once finalized, `BusEffect.lean`
   needs the `U64.toBV` call site widened from 4 to 8 bytes.

## `ZiskFv.RV64D.add` build state

- `cd /home/cody/zisk-fv/ZiskFv && lake build ZiskFv.RV64D.add`:
  blocked on `ZiskFv.Fundamentals.Execution.lean` not yet existing
  (Track B, Task 6 / Task 7). File body itself is syntactically well-formed
  and contains no `sorry`; should compile cleanly once the missing import is
  provided. (If the RV64 arithmetic changes the tactic steps in the proof,
  the specific rewrites will need adjustment; the structure should carry
  through unchanged because the only width-sensitive step is the final
  bit-vector equality which `grind`/`omega` re-derive.)

## How to verify

```bash
cd /home/cody/zisk-fv/ZiskFv
# These build clean (with `sorry` warnings):
lake build ZiskFv.RV64D.Auxiliaries
lake build ZiskFv.RV64D.lb ZiskFv.RV64D.lui ZiskFv.RV64D.sw \
           ZiskFv.RV64D.beq ZiskFv.RV64D.jal ZiskFv.RV64D.jalr \
           ZiskFv.RV64D.auipc ZiskFv.RV64D.addw ZiskFv.RV64D.ld
# Blocked on Track B's Fundamentals/Execution.lean:
lake build ZiskFv.RV64D.add
```
