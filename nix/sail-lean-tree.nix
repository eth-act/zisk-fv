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
  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r model/Lean_RV64D/. $out/
    runHook postInstall
  '';

  meta = (old.meta or {}) // {
    description = "Lean RV64D spec generated from sail-riscv";
  };
})
