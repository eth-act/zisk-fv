{ sail-riscv, sail-riscv-src, lib }:

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

  # The default cmake install phase builds the emulator. We want only
  # the Lean tree.
  #
  # Patch the sail-emitted `Sail/IntRange.lean` to add `[Monad m]` to
  # its `ForIn'` / `ForM` instance heads. The handwritten prelude in
  # upstream sail targets a Lean nightly (`nightly-2025-11-18`) whose
  # instance elaboration propagates the Monad constraint implicitly;
  # stable Lean v4.28 does not, so the instances fail to synthesize
  # `Monad m` without this annotation. The same fix lives on
  # codygunton/sail @ lean-backend/v4.28 (commit 46acc966), ready to
  # upstream to rems-project/sail.
  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r model/Lean_RV64D/. $out/
    sed -i \
      -e 's|^instance : ForIn'"'"' m IntRange Int|instance [Monad m] : ForIn'"'"' m IntRange Int|' \
      -e 's|^instance : ForM m IntRange Int|instance [Monad m] : ForM m IntRange Int|' \
      $out/LeanRV64D/Sail/IntRange.lean
    runHook postInstall
  '';

  meta = (old.meta or {}) // {
    description = "Lean RV64D spec generated from sail-riscv";
  };
})
