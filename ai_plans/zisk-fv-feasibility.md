# Adapting openvm-fv to ZisK (RV64IM) — feasibility assessment

Date: 2026-04-20

## The openvm-fv pattern, distilled

Five layers per opcode, with the Sail spec as ground truth:

1. **Extraction** (auto): raw column-indexed polynomial constraints dumped from Rust AIR → `def constraint_N ... = 0`.
2. **Airs** (semi-auto via the `#define_subair` macro): structure with named accessors (`opcode_add_flag`, `carry_add_0`, …), plus derived semantic columns.
3. **Constraints** (hand): each numeric constraint proven equivalent to a readable proposition over the Airs.
4. **RV32D** (hand): a `PureSpec` function per opcode plus an equivalence lemma back to the Sail monadic `execute_instruction`.
5. **Equivalence** (hand): top-level theorems of the form `execute_instruction (RTYPE(... ADD)) state = (bus_effect exec_row mem_row state).2`, one per opcode (45 total for RV32IM).

Glue modules: `Fundamentals/Transpiler.lean` encodes RISC-V → OpenVM native opcodes (e.g. `ADD → 512`); `Interaction.lean` is a generic bus-entry typeclass; `BabyBear.lean` fixes the field.

External Lean deps:
- `NethermindEth/sail-riscv-lean` (branch `rv32d`, module `LeanRV32D`). The `main` branch of the same repo exports `LeanRV64D` — RV64 is already extracted from Sail.
- `NethermindEth/leanzkcircuit` (branch `v4.26.0`): `LeanZKCircuit.OpenVM.Circuit` + `Command` macros + `Tactics` + `Interactions`. A `Dom/plonky3` branch hints at a multi-backend refactor in progress.

Completeness: no `sorry` / `admit` in the project; one `opaque undefined : Prop` in `Util.lean`. Total roughly 62k lines of Lean across Extraction/Constraints/Airs/Spec/RV32D/Equivalence; roughly one-third machine-generated (Extraction), one-third macro-expanded (Airs), one-third genuinely hand-written proofs.

## What transfers cleanly to ZisK

- **The Sail-spec bridge.** RV64 is already extracted. The `execute_instruction`-to-`PureSpec` pattern in `RV32D/` generalizes directly. Widening `BitVec 32 → BitVec 64`, `U32 → U64`, and doubling the limb decomposition is mechanical but not trivial (pure-spec proofs invoke `Sail.shift_bits_left`, `BitVec.sshiftRight`, etc., and RV64's -W family adds sign-extension lemmas that don't exist in RV32D).
- **The top-level theorem shape.** The per-opcode statement "Sail execute = chip bus_effect" is local and architecture-agnostic.
- **The generic bus-interaction framework** (`LeanZKCircuit.Interactions`) is OpenVM-agnostic and directly usable for ZisK's operation bus, memory bus, and ROM bus.
- **Lean infrastructure.** mathlib, BitVec, `grind`, `simp` attribute discipline — unchanged.

## What does not transfer, and what it costs

### A. Circuit-representation gap (new infrastructure, not just new proofs)

OpenVM's extraction assumes `Circuit.main c (id, column, row, rotation)` AIR cells with `Field F` / `ExtF`, laid out per-opcode with semantic column names. ZisK is PIL2, Goldilocks-field, and uses:

- a single monolithic Main AIR (`state-machines/main/pil/main.pil`) multiplexing ~all opcodes by flag;
- secondary state machines (`arith`, `binary`, `binary_extension`, `mem`, `rom`) connected via lookups/permutations on the operation bus (`OPERATION_BUS_ID = 5000`).

Concrete work: a new `LeanZKCircuit.PIL2.Circuit` (or `LeanZKCircuit.ZisK.Circuit`) module analogous to `LeanZKCircuit.OpenVM.Circuit`, plus a new extractor that reads `pil/zisk.pilout` and emits raw Lean constraints. LeanZKCircuit's `Dom/plonky3` branch suggests multi-backend refactoring is already in progress, which is encouraging.

### B. Proof composition is fundamentally different

OpenVM: each opcode has its own AIR, so each theorem is local. ZisK: proving `ADD` requires reasoning about Main + Binary + Memory + ROM simultaneously, because a single opcode's execution trace spans rows across all four AIRs connected by bus constraints. Every per-opcode theorem becomes a theorem over the composition of state machines.

This is doable but changes the proof pattern substantially. The closest published precedent is compositional AIR reasoning with lookup arguments (LogUp etc.); Nethermind's `Interaction.lean` already has the primitives.

### C. RISC-V ↔ Zisk-instruction translation layer

OpenVM's `Transpiler.lean` maps RV32IM to a small set of OpenVM native opcodes (mostly 1-to-1). ZisK's `core/src/riscv2zisk_context.rs` + `elf2rom.rs` emit multiple Zisk microinstructions per RV instruction for some cases, and the RISC-V decoder lives inside that Rust transpiler. openvm-fv's `Fundamentals/Transpiler.lean` is ~7500 lines — most of Fundamentals' bulk — and ZisK's analogue will likely be larger.

### D. Field change: BabyBear → Goldilocks

Mechanical replacement of `FBB = Fin BB_prime` with `FGL = Fin Goldilocks_prime`, re-deriving carry-divide tricks (OpenVM uses `256⁻¹ mod BabyBear = 2005401601` as a hardcoded constant in carry propagation; ZisK's constants differ). Not hard, but touches every `Constraints/` proof.

### E. RV64IM vs RV32IM

- RV64 Sail spec is already extracted (`LeanRV64D` on `main`) — not a blocker.
- Every `BitVec 32` in pure specs becomes `BitVec 64`; limb count doubles; `U32` helpers need `U64` analogs.
- New opcode families: the -W forms (ADDW/SUBW/SLLW/SRLW/SRAW, ADDIW/SLLIW/SRLIW/SRAIW), MULW/DIVW/DIVUW/REMW/REMUW, plus LD/SD and sign-extended LWU. OpenVM's 45 RV32IM opcodes become ~65 for RV64IM.

## Rough scope

Scaling openvm-fv's ~62k LOC linearly misleads in both directions:

- **Infrastructure (one-time, front-loaded):** PIL2 → Lean extractor, ZisK `Circuit` abstraction, transpiler formalization. Comparable to openvm-fv's Fundamentals + Extraction (~15–20k LOC) but harder because of compositional bus reasoning. Roughly **6–12 engineer-months**.
- **Per-opcode proofs:** with infrastructure in place, ~65 RV64IM opcodes with compositional reasoning across Main + Binary + Arith + Memory is probably 1.5–2× openvm-fv's per-opcode effort, so roughly **9–15 engineer-months** for a team with Lean + ZK expertise.
- **Total:** roughly **1.5–2 engineer-years**, assuming Nethermind's `leanzkcircuit` and `sail-riscv-lean` stay maintained and cooperative. Without that, multiply by 1.5–2×.

## Plausibility verdict

Plausible, with caveats. The core pattern — "per-opcode chip ↔ Sail spec via bus-effect composition" — is architecture-agnostic and survives the port.

Dominant risks:

1. **PIL2 extraction toolchain** doesn't exist yet; bounded engineering, not research.
2. **Compositional bus reasoning** is needed to tie Main + secondary machines together for a single opcode. openvm-fv exercised only limited composition (range-check and bitwise lookups); for ZisK the per-opcode proof is genuinely a composition proof. Moderately novel work.
3. **Transpiler verification** is larger for ZisK than for OpenVM.
4. **Zicclsm** is correctly deferred — not yet stable in either the Sail spec or ZisK.

Recommended order of attack, by leverage:
1. Engage Nethermind / OpenLabs about a PIL2 backend for `leanzkcircuit` — and about whether they intend to tackle ZisK.
2. Prototype one simple opcode end-to-end (e.g. RV64 ADD) to validate the extraction and compositional-proof patterns before committing to scale.
3. Only then commit to the full ~65-opcode campaign.
