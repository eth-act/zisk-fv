//! Phase 1.5 Track H — ZisK guest probe for the canonical 64-bit ADD.
//!
//! Executes the RISC-V sequence
//!
//! ```asm
//! addi x11, x0, 3
//! addi x12, x0, 5
//! add  x13, x11, x12
//! ```
//!
//! ZisK's transpiler lowers the final `add` to a Main-AIR row with
//! `op = 0x0a`. The harness calls `ProverClient::get_instance_trace` on
//! Main + BinaryAdd AIRs, locates the row with `op = 0x0a`, and emits
//! the `Valid_Main` / `Valid_BinaryAdd` witness into
//! `ZiskFv/ZiskFv/GoldenTraces/Add.lean`.
//!
//! The program writes the 64-bit ADD result to ZisK's public output so
//! `client.execute()` returns a concrete `u64` the harness can sanity
//! check (expected `3 + 5 = 8`).

#![no_main]
ziskos::entrypoint!(main);

fn main() {
    // Read nothing from stdin; this is a constant-input probe.
    let a: u64 = 3;
    let b: u64 = 5;

    // Force the compiler to emit a plain `add` on the RV64 pipeline.
    // `core::hint::black_box` prevents constant-folding at LLVM-IR time.
    let a = core::hint::black_box(a);
    let b = core::hint::black_box(b);
    let c: u64 = a.wrapping_add(b);

    ziskos::io::commit(&c);
}
