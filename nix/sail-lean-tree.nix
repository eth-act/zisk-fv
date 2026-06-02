{ sail-riscv, sail-riscv-src, lib, patch }:

# Override nixpkgs's sail-riscv derivation: swap in our pinned source
# and build the `generated_lean_rv64d` cmake target instead of the
# emulator binary. Output is the directory tree of Lean files (the
# `Lean_RV64D/` build output) at $out/.
sail-riscv.overrideAttrs (old: {
  pname = "sail-lean-tree";
  version = "git-${builtins.substring 0 7 sail-riscv-src.rev}";
  src = sail-riscv-src;

  # Override the default ninjaFlags (was `compressed_changelog` for
  # the 0.8 release) to build only the Lean target.
  ninjaFlags = [ "generated_lean_rv64d" ];

  # sail-riscv's dependencies/jsoncons/CMakeLists.txt uses
  # FetchContent to download jsoncons at configure time, which
  # Nix's sandbox blocks. The Lean codegen target doesn't link
  # against jsoncons (that's emulator-only), so we can safely turn
  # the download off.
  cmakeFlags = (old.cmakeFlags or []) ++ [ "-DDOWNLOAD_JSONCONS=OFF" ];

  postConfigure = (old.postConfigure or "") + ''
    cp ${./sail-riscv-zisk-rv64d.json} "$PWD/config/rv64d_v256_e64.json"
  '';

  # The default cmake install phase builds the emulator. We want only
  # the Lean tree.
  #
  # Apply the v4.28-stable compat patch to the sail-emitted prelude.
  # Upstream sail's handwritten Lean prelude (`Sail/IntRange.lean`,
  # `Sail/Sail.lean`) targets a Lean nightly (`nightly-2025-11-18`)
  # whose elaboration handles some signatures that stable Lean v4.28
  # does not. The patch fixes:
  #
  #   - `IntRange.lean`: `[Monad m]` on `ForIn'` / `ForM` instance heads
  #     (the nightly propagates the constraint implicitly; stable does
  #     not, so `Monad m` fails to synthesize).
  #
  #   - `Sail.lean`: a `Coe String.Slice String` instance + explicit
  #     `: String` ascriptions to handle `String.take`/`drop` now
  #     returning `String.Slice` under v4.28's stdlib; replacement of
  #     `String.Pos.Raw.get!` (nightly-only) with `str.toList[i]!`;
  #     and `str.all` → `str.toList.all` to dodge the same
  #     `String.Slice`-overload disambiguation issue.
  #
  # The same fix lives on codygunton/sail @ lean-backend/v4.28
  # (commit e4ba7849), ready to upstream to rems-project/sail. The
  # patch file is the literal `git diff 277470b2..e4ba7849` with the
  # in-source path prefix `src/sail_lean_backend/Sail/` rewritten to
  # the install-phase output prefix `LeanRV64D/Sail/`.
  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r model/Lean_RV64D/. $out/
    ${patch}/bin/patch -p1 -d $out < ${./sail-lean-v4.28-compat.patch}
    runHook postInstall
  '';

  meta = (old.meta or {}) // {
    description = "Lean RV64D spec generated from sail-riscv";
  };
})
