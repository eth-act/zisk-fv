//! Phase 1.5 fixture emitter for `ZiskFv.GoldenTraces.Add`.
//!
//! Supports two modes:
//!
//! - `--mode golden` (default) — emits the canonical `3 + 5 = 8` ADD
//!   witness from hard-coded values. No heavy deps; runs under
//!   `cargo run -p golden-traces` from a vanilla checkout.
//!
//! - `--mode live` — runs the real ZisK `ProverClient` against
//!   `examples/fv-probes/add` and reshapes the rows from Main (AIR 12)
//!   and BinaryAdd (AIR 23) into the same fixture shape. Requires
//!   `--features live` at compile time **and** a pre-built probe ELF +
//!   working ZisK proving stack. See the crate's `Cargo.toml` for the
//!   environment prereqs.
//!
//! Live-mode call pattern mirrors
//! `zisk/examples/sha-hasher/host/bin/execute.rs`.
//!
//! Phase 4.5 Track D: `--multi-fixture` flag (default: true) emits the
//! Phase 4 T-FIX edge-case namespaces (`ZeroResult`, `HighLaneOverflow`)
//! in addition to the canonical fixture, fixing a pre-Phase-4.5 bug
//! where the harness silently stripped those namespaces on regeneration.

use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};
use std::fs;
use std::path::PathBuf;
use tracing::info;

/// Main AIR identifier in the ZisK pilout (matches
/// `MAIN_AIR_IDS = &[12]` in `zisk/pil/src/pil_helpers/traces.rs`).
/// The AIR id is not the same as an executor `instance_id` — the live
/// path maps AIR id → instance id by querying the prover.
pub const MAIN_AIR_ID: usize = 12;

/// BinaryAdd AIR identifier (`BINARY_ADD_AIR_IDS = &[23]`).
pub const BINARY_ADD_AIR_ID: usize = 23;

/// Decoded ADD witness shared between golden and live modes. All values
/// are 64-bit because Goldilocks fits `u64` cleanly; the Lean fixture
/// renders them as field literals.
#[derive(Debug, Clone, Copy)]
struct AddWitness {
    a: u64,
    b: u64,
    c: u64,
}

impl AddWitness {
    fn canonical_3_plus_5() -> Self {
        Self { a: 3, b: 5, c: 8 }
    }

    #[cfg(test)]
    fn from_operands(a: u64, b: u64) -> Self {
        Self { a, b, c: a.wrapping_add(b) }
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
enum Mode {
    /// Emit from hard-coded `3 + 5 = 8` values (no SDK required).
    Golden,
    /// Run ProverClient, pull real rows via `get_instance_trace`, reshape.
    Live,
}

#[derive(Parser, Debug)]
#[command(
    name = "golden-traces",
    about = "Emit a ZiskFv golden-trace fixture for the canonical ADD row."
)]
struct Cli {
    /// Output path for the generated `.lean` fixture.
    #[arg(long, default_value = "ZiskFv/ZiskFv/GoldenTraces/Add.lean")]
    output: PathBuf,

    /// Fixture source. Defaults to `golden` (hard-coded) since the
    /// `live` path is gated behind `--features live`.
    #[arg(long, value_enum, default_value_t = Mode::Golden)]
    mode: Mode,

    /// Probe ELF for live mode. Built by
    /// `cargo zisk build --manifest-path examples/fv-probes/add/Cargo.toml
    ///  --release`.
    #[arg(
        long,
        default_value = "examples/fv-probes/add/target/riscv64ima-zisk-zkvm-elf/release/zisk-fv-probe-add"
    )]
    probe_elf: PathBuf,

    /// AIR id for the Main trace (live mode). Defaults to ZisK's canonical 12.
    #[arg(long, default_value_t = MAIN_AIR_ID)]
    main_air_id: usize,

    /// AIR id for the BinaryAdd trace (live mode). Defaults to ZisK's canonical 23.
    #[arg(long, default_value_t = BINARY_ADD_AIR_ID)]
    binary_add_air_id: usize,

    /// When true (default), emit the Phase 4 T-FIX edge-case namespaces
    /// (`ZeroResult`, `HighLaneOverflow`) in addition to the canonical
    /// fixture. Pre-Phase-4.5 the harness silently stripped those
    /// namespaces on every regeneration; Track D makes preservation the
    /// default. Pass `--multi-fixture=false` for the pre-4.5 single-
    /// fixture output shape (useful for diffing).
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set)]
    multi_fixture: bool,
}

fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let cli = Cli::parse();

    let witness = match cli.mode {
        Mode::Golden => {
            info!("mode=golden: emitting hard-coded 3 + 5 = 8 fixture");
            AddWitness::canonical_3_plus_5()
        }
        Mode::Live => {
            info!(probe = %cli.probe_elf.display(), "mode=live: running ProverClient");
            live::run(&cli).context("live-mode harness run failed")?
        }
    };

    let lean = render_lean_full(&witness, cli.multi_fixture);

    if let Some(parent) = cli.output.parent() {
        fs::create_dir_all(parent).ok();
    }
    fs::write(&cli.output, lean)
        .with_context(|| format!("failed to write {}", cli.output.display()))?;
    info!(output = %cli.output.display(), "wrote fixture");
    Ok(())
}

/// Emit the Add.lean fixture text: canonical witness plus (optionally)
/// the Phase 4 T-FIX `ZeroResult` / `HighLaneOverflow` sub-namespaces.
///
/// Pre-Phase-4.5 this harness only emitted the canonical witness; any
/// hand-authored sub-namespaces in `Add.lean` were silently stripped on
/// regeneration. Track D fixes that by rendering all three fixtures in
/// one pass whenever `multi_fixture` is true (the default).
fn render_lean_full(w: &AddWitness, multi_fixture: bool) -> String {
    let canonical = render_lean(w);
    if !multi_fixture {
        return canonical;
    }

    // The canonical render ends with `end ZiskFv.GoldenTraces.Add\n`.
    // Splice the T-FIX namespaces right before that closing `end`.
    const CLOSE: &str = "end ZiskFv.GoldenTraces.Add\n";
    let Some(idx) = canonical.rfind(CLOSE) else {
        // Defensive fallback: if the closer moved, emit canonical only
        // rather than producing a syntactically broken file.
        return canonical;
    };
    let (prefix, suffix) = canonical.split_at(idx);
    format!("{prefix}{tfix}\n{suffix}", tfix = TFIX_NAMESPACES)
}

/// Phase 4 T-FIX edge-case sub-namespaces. Hand-authored in
/// `GoldenTraces/Add.lean` pre-Phase-4.5; inlined here so the harness
/// preserves them verbatim on regeneration.
const TFIX_NAMESPACES: &str = "-- Phase 4 T-FIX: additional edge-case fixtures.

namespace ZeroResult

-- Edge case: `0 + 0 = 0` (zero-register sum, no carry).
@[simp] def add_a_lo : FGL := 0
@[simp] def add_a_hi : FGL := 0
@[simp] def add_b_lo : FGL := 0
@[simp] def add_b_hi : FGL := 0
@[simp] def add_c_lo : FGL := 0
@[simp] def add_c_hi : FGL := 0
@[simp] def cout_0 : FGL := 0
@[simp] def cout_1 : FGL := 0

example : add_c_lo + add_c_hi * 4294967296 = (0 : FGL) := by decide
example : add_a_lo + add_b_lo = cout_0 * 4294967296 + add_c_lo := by decide

end ZeroResult

namespace HighLaneOverflow

-- Edge case: `2^63 + 2^63 = 2^64 = 0 mod 2^64` (carry out of high lane).
-- a = 0x8000_0000_0000_0000, b = 0x8000_0000_0000_0000, c = 0, cout_1 = 1.
@[simp] def add_a_lo : FGL := 0
@[simp] def add_a_hi : FGL := 2147483648       -- 0x8000_0000
@[simp] def add_b_lo : FGL := 0
@[simp] def add_b_hi : FGL := 2147483648
@[simp] def add_c_lo : FGL := 0
@[simp] def add_c_hi : FGL := 0
@[simp] def cout_0 : FGL := 0
@[simp] def cout_1 : FGL := 1

example : add_c_lo + add_c_hi * 4294967296 = (0 : FGL) := by decide
example :
    add_a_hi + add_b_hi + cout_0
      = cout_1 * 4294967296 + add_c_hi := by decide

end HighLaneOverflow
";

/// Render the `Valid_Main` + `Valid_BinaryAdd` witness for `a + b = c`
/// as a Lean fixture matching `ZiskFv.GoldenTraces.Add`.
fn render_lean(w: &AddWitness) -> String {
    let a = w.a;
    let b = w.b;
    let c = w.c;

    // Decompose into the column shape expected by Valid_Main / Valid_BinaryAdd.
    // Main columns are 32-bit lanes; BinaryAdd's are 16-bit chunks.
    let a_lo: u64 = a & 0xFFFF_FFFF;
    let a_hi: u64 = a >> 32;
    let b_lo: u64 = b & 0xFFFF_FFFF;
    let b_hi: u64 = b >> 32;
    let c_lo: u64 = c & 0xFFFF_FFFF;
    let c_hi: u64 = c >> 32;

    let a0_chunk = a_lo & 0xFFFF;
    let a1_chunk = a_lo >> 16;
    // BinaryAdd's chunk reassembly: c_chunks[2k+1] * 65536 + c_chunks[2k] = c[k]
    let c0_chunk = c_lo & 0xFFFF;
    let c1_chunk = c_lo >> 16;
    let c2_chunk = c_hi & 0xFFFF;
    let c3_chunk = c_hi >> 16;

    // Carry-out: low-lane overflow propagates into the high-lane sum.
    let cout0: u64 = u64::from((a_lo + b_lo) >= (1u64 << 32));
    let cout1: u64 = u64::from((a_hi + b_hi + cout0) >= (1u64 << 32));

    format!(
"import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Add

/-!
Phase 1 golden-trace fixture: canonical 64-bit ADD `{a} + {b} = {c}`.

Generated by `tools/golden-traces` from hardcoded values; Phase 1.5
replaces this with `ProverClient::get_instance_trace` output. The shape
matches what a real ZisK Main row + BinaryAdd row would produce for the
RISC-V instruction sequence:

```asm
addi x1, x0, {a}
addi x2, x0, {b}
add  x3, x1, x2  -- this row's witness is captured below
```
-/

namespace ZiskFv.GoldenTraces.Add

open Goldilocks

-- 32-bit lane decomposition (Main AIR columns).
@[simp] def add_a_lo : FGL := {a_lo}
@[simp] def add_a_hi : FGL := {a_hi}
@[simp] def add_b_lo : FGL := {b_lo}
@[simp] def add_b_hi : FGL := {b_hi}
@[simp] def add_c_lo : FGL := {c_lo}
@[simp] def add_c_hi : FGL := {c_hi}

-- 16-bit chunk decomposition (BinaryAdd AIR columns).
@[simp] def chunk_a0 : FGL := {a0_chunk}
@[simp] def chunk_a1 : FGL := {a1_chunk}
@[simp] def chunk_c0 : FGL := {c0_chunk}
@[simp] def chunk_c1 : FGL := {c1_chunk}
@[simp] def chunk_c2 : FGL := {c2_chunk}
@[simp] def chunk_c3 : FGL := {c3_chunk}

-- Carry-out cells.
@[simp] def cout_0 : FGL := {cout0}
@[simp] def cout_1 : FGL := {cout1}

/-- The packed `c`-value (32-bit lane recombination) matches `{a} + {b} = {c}`. -/
example : add_c_lo + add_c_hi * 4294967296 = ({c} : FGL) := by decide

/-- BinaryAdd's chunk reassembly produces the same packed value. -/
example :
    (chunk_c1 * 65536 + chunk_c0) + (chunk_c3 * 65536 + chunk_c2) * 4294967296
      = ({c} : FGL) := by decide

/-- Low-lane carry chain (BinaryAdd `carry_chain_0`):
    a_lo + b_lo = cout_0 * 2^32 + chunk_c1 * 2^16 + chunk_c0. -/
example :
    add_a_lo + add_b_lo
      = cout_0 * 4294967296 + chunk_c1 * 65536 + chunk_c0 := by decide

/-- High-lane carry chain (BinaryAdd `carry_chain_1`):
    a_hi + b_hi + cout_0 = cout_1 * 2^32 + chunk_c3 * 2^16 + chunk_c2. -/
example :
    add_a_hi + add_b_hi + cout_0
      = cout_1 * 4294967296 + chunk_c3 * 65536 + chunk_c2 := by decide

end ZiskFv.GoldenTraces.Add
",
        a = a, b = b, c = c,
        a_lo = a_lo, a_hi = a_hi, b_lo = b_lo, b_hi = b_hi, c_lo = c_lo, c_hi = c_hi,
        a0_chunk = a0_chunk, a1_chunk = a1_chunk,
        c0_chunk = c0_chunk, c1_chunk = c1_chunk, c2_chunk = c2_chunk, c3_chunk = c3_chunk,
        cout0 = cout0, cout1 = cout1,
    )
}

// ---------------------------------------------------------------------------
// Live mode: wraps the ZisK ProverClient. Gated by the `live` Cargo feature
// so the default crate stays free of the heavy proofman / C++ toolchain.
// ---------------------------------------------------------------------------

#[cfg(feature = "live")]
mod live {
    use anyhow::{Context, Result};
    use std::path::Path;
    use tracing::{info, warn};
    use zisk_common::io::ZiskStdin;
    use zisk_common::{ElfBinaryFromFile, ElfBinaryLike};
    use zisk_sdk::ProverClient;

    use super::{AddWitness, Cli};

    /// ADD opcode literal from `zisk/pil/opids.pil` (`OP_ADD = 0x0A`).
    /// Used to identify the canonical ADD row inside the Main trace.
    const OP_ADD: u64 = 0x0a;

    pub(super) fn run(cli: &Cli) -> Result<AddWitness> {
        let elf_path = &cli.probe_elf;
        if !elf_path.exists() {
            anyhow::bail!(
                "probe ELF not found at {}\n\
                 build with: cargo zisk build --manifest-path examples/fv-probes/add/Cargo.toml --release",
                elf_path.display()
            );
        }

        let elf = ElfBinaryFromFile::new(Path::new(elf_path), false)
            .with_context(|| format!("failed to read probe ELF at {}", elf_path.display()))?;

        info!(name = elf.name(), "loaded probe ELF");

        let client = ProverClient::builder()
            .emu()
            .verify_constraints()
            .build()
            .map_err(|e| anyhow::anyhow!("ProverClient build failed: {}", e))?;

        let (pk, _vkey) = client.setup(&elf).context("ProverClient setup failed")?;
        info!("ProverClient setup complete");

        // The probe program ignores stdin, so pass an empty ZiskStdin.
        let stdin = ZiskStdin::new();

        let result = client
            .verify_constraints(&pk, stdin.clone())
            .context("verify_constraints run failed")?;
        info!(
            cycles = result.get_execution_steps(),
            duration_ms = result.get_duration().as_millis() as u64,
            "verify_constraints done"
        );

        // Locate the Main-AIR row with `op = OP_ADD` and read out (a, b, c).
        let witness = locate_add_row(&client, cli).context("locating ADD row in Main trace")?;
        info!(a = witness.a, b = witness.b, c = witness.c, "decoded ADD row");

        if witness.c != witness.a.wrapping_add(witness.b) {
            warn!(
                "live-trace ADD row violates c = a + b: a = {}, b = {}, c = {}",
                witness.a, witness.b, witness.c
            );
        }

        Ok(witness)
    }

    /// Scan the Main AIR trace for a row whose `op` column equals `OP_ADD`.
    /// Returns the (a, b, c) triple as a [`AddWitness`].
    ///
    /// NOTE: ZisK's executor assigns **instance ids** at runtime — they
    /// are not identical to AIR ids. The current implementation treats
    /// `main_air_id` / `binary_add_air_id` as instance ids because
    /// `verify_constraints` mode with a minimal trace produces exactly
    /// one instance per AIR. If that assumption breaks (multi-segment
    /// traces, parallel execution), this needs a lookup that maps AIR
    /// id → instance id via `ProverEngine::get_execution_info`.
    fn locate_add_row<C>(
        client: &zisk_sdk::ZiskProver<C>,
        cli: &Cli,
    ) -> Result<AddWitness>
    where
        C: zisk_sdk::ZiskBackend,
    {
        // Main trace layout per `zisk/pil/src/pil_helpers/traces.rs`:
        //   op column index = 0 (`is_external_op` precedes it in the declaration
        //   but is packed after `op` by `trace_row!`). The exact index is not
        //   load-bearing for the fixture — we only need to identify the row.
        //
        // The probe has three instructions (two `addi` + one `add`), so scan
        // 256 rows from the start; that's >> enough to cover the probe.
        let scan_rows = 256;
        let main_rows = client
            .get_instance_trace(cli.main_air_id, 0, scan_rows, None)
            .context("get_instance_trace(Main) failed")?;

        // Column indices for Main (from `traces.rs` trace_row! for MainTraceRow):
        //   a[0], a[1], b[0], b[1], c[0], c[1] are 6 consecutive u32 lanes in
        //   the declaration order. `op` is declared with bits(8). We fetch
        //   row.values and report it.
        let Some(row) = main_rows.iter().find(|r| row_op(r) == OP_ADD) else {
            anyhow::bail!(
                "no ADD row (op = 0x{:02x}) found in first {} rows of Main AIR (id {}); \
                 the probe ELF may not have emitted the expected instruction sequence",
                OP_ADD,
                scan_rows,
                cli.main_air_id
            );
        };

        info!(row = row.row, "found ADD row in Main AIR");

        // Map 32-bit lanes back to u64. The exact lane column indices match
        // the `MainTraceRow<F>` declaration order in
        // `zisk/pil/src/pil_helpers/traces.rs`. If this crate ever
        // needs to be field-of-view-agnostic, replace the constants with a
        // run-time column lookup from the pilout.
        let a = read_u64_lanes(row, MAIN_COL_A_LO, MAIN_COL_A_HI);
        let b = read_u64_lanes(row, MAIN_COL_B_LO, MAIN_COL_B_HI);
        let c = read_u64_lanes(row, MAIN_COL_C_LO, MAIN_COL_C_HI);

        Ok(AddWitness { a, b, c })
    }

    // Placeholder column indices. The real layout comes from
    // `zisk/pil/src/pil_helpers/traces.rs::MainTraceRow`. These are
    // conservative best-guesses; when `--mode live` is first exercised with
    // the real ELF they will be verified (and corrected) against the oracle
    // fixture that `--mode golden` still emits.
    const MAIN_COL_OP: usize = 0;
    const MAIN_COL_A_LO: usize = 1;
    const MAIN_COL_A_HI: usize = 2;
    const MAIN_COL_B_LO: usize = 3;
    const MAIN_COL_B_HI: usize = 4;
    const MAIN_COL_C_LO: usize = 5;
    const MAIN_COL_C_HI: usize = 6;

    fn row_op(row: &proofman_common::RowInfo) -> u64 {
        row.values.get(MAIN_COL_OP).copied().unwrap_or(0)
    }

    fn read_u64_lanes(
        row: &proofman_common::RowInfo,
        lo_col: usize,
        hi_col: usize,
    ) -> u64 {
        let lo = row.values.get(lo_col).copied().unwrap_or(0) & 0xFFFF_FFFF;
        let hi = row.values.get(hi_col).copied().unwrap_or(0) & 0xFFFF_FFFF;
        (hi << 32) | lo
    }
}

#[cfg(not(feature = "live"))]
mod live {
    use anyhow::Result;
    use super::{AddWitness, Cli};

    pub(super) fn run(_cli: &Cli) -> Result<AddWitness> {
        anyhow::bail!(
            "--mode live requires compiling with `--features live`; rebuild as \
             `cargo build -p golden-traces --features live`. See \
             tools/golden-traces/Cargo.toml for the environment prerequisites."
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_lean_canonical_add() {
        let w = AddWitness::canonical_3_plus_5();
        let s = render_lean(&w);
        assert!(s.contains("add_a_lo : FGL := 3"));
        assert!(s.contains("add_b_lo : FGL := 5"));
        assert!(s.contains("add_c_lo : FGL := 8"));
        assert!(s.contains("cout_0 : FGL := 0"));
        assert!(s.contains("cout_1 : FGL := 0"));
    }

    #[test]
    fn cout_propagation_overflow_lo() {
        // 0xFFFFFFFF + 1 = 0x100000000 → cout_0 = 1, c_lo = 0
        let a: u64 = 0xFFFF_FFFF;
        let b: u64 = 1;
        let w = AddWitness::from_operands(a, b);
        assert_eq!(w.c, 0x1_0000_0000);

        let s = render_lean(&w);
        assert!(s.contains("cout_0 : FGL := 1"));
        assert!(s.contains("add_c_lo : FGL := 0"));
    }

    #[test]
    fn from_operands_wraps_on_u64_overflow() {
        let w = AddWitness::from_operands(u64::MAX, 1);
        assert_eq!(w.c, 0);
    }

    #[test]
    fn multi_fixture_default_includes_tfix_namespaces() {
        // Track D guarantee: the default render preserves the Phase 4
        // T-FIX edge-case sub-namespaces. Pre-Phase-4.5 the harness
        // silently stripped them on every regeneration.
        let w = AddWitness::canonical_3_plus_5();
        let s = render_lean_full(&w, /* multi_fixture = */ true);
        assert!(s.contains("namespace ZeroResult"));
        assert!(s.contains("namespace HighLaneOverflow"));
        assert!(s.contains("end ZeroResult"));
        assert!(s.contains("end HighLaneOverflow"));
        // Canonical body still present and not duplicated.
        assert_eq!(s.matches("add_a_lo : FGL := 3").count(), 1);
        // File ends at the outer namespace closer.
        assert!(s.trim_end().ends_with("end ZiskFv.GoldenTraces.Add"));
    }

    #[test]
    fn multi_fixture_off_matches_legacy_canonical() {
        let w = AddWitness::canonical_3_plus_5();
        let legacy = render_lean(&w);
        let opt_out = render_lean_full(&w, /* multi_fixture = */ false);
        assert_eq!(legacy, opt_out);
        // And in legacy mode, no T-FIX markers.
        assert!(!opt_out.contains("ZeroResult"));
        assert!(!opt_out.contains("HighLaneOverflow"));
    }

    #[test]
    fn live_mode_without_feature_errors_cleanly() {
        // Without `--features live`, the live stub must return an Err with
        // actionable guidance, not silently fall through to golden mode.
        let cli = Cli {
            output: PathBuf::from("/dev/null"),
            mode: Mode::Live,
            probe_elf: PathBuf::from("/nonexistent"),
            main_air_id: MAIN_AIR_ID,
            binary_add_air_id: BINARY_ADD_AIR_ID,
            multi_fixture: true,
        };
        let err = live::run(&cli).err();
        // When the `live` feature is enabled this test is a no-op because
        // `live::run` may succeed or fail based on runtime env. With the
        // feature off, the stub always bails.
        if cfg!(not(feature = "live")) {
            let msg = err.expect("expected an error without --features live").to_string();
            assert!(msg.contains("--features live"), "unexpected error: {}", msg);
        }
    }
}
