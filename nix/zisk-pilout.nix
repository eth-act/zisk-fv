{ stdenv, lib, rustPlatform, nodejs_20,
  zisk-src, pil2-compiler, pil2-proofman-src,
  # Native build tools
  pkg-config, clang, libclang, nasm,
  # System libs required by zisk's transitive C++ deps
  gmp, openssl, libsodium, secp256k1, nlohmann_json,
  protobuf, libuuid, grpc, libpqxx, openmpi }:

# Builds three Cargo binaries from the zisk workspace, runs them to
# generate fixed-column data, then compiles pil/zisk.pil via Node +
# pil2-compiler.  The single output is the binary pilout blob.
#
# Reference: docker/Dockerfile.pilout + docker/build-pilout-inside.sh

rustPlatform.buildRustPackage {
  pname = "zisk-pilout";
  version = "git-${builtins.substring 0 7 zisk-src.rev}";

  src = zisk-src;

  # The workspace Cargo.lock has 11 git-sourced crates from pil2-proofman.
  # allowBuiltinFetchGit lets importCargoLock handle them without per-crate
  # hashes — it fetches them from the store path already in the flake inputs.
  cargoLock = {
    lockFile = "${zisk-src}/Cargo.lock";
    allowBuiltinFetchGit = true;
  };

  # Build only the three binaries we actually need; skip the rest of
  # the 30+ workspace members (emulator, server, CLI, …).
  cargoBuildFlags = [
    "--bin" "arith_frops_fixed_gen"
    "--bin" "binary_basic_frops_fixed_gen"
    "--bin" "binary_extension_frops_fixed_gen"
  ];

  # Don't run `cargo test`; it would need the full workspace + GPU stack.
  doCheck = false;

  # bindgen (used by clang-sys) needs to find libclang.so.
  LIBCLANG_PATH = "${libclang.lib}/lib";

  nativeBuildInputs = [
    pkg-config
    clang
    libclang.lib
    nasm
    nodejs_20
    # openmpi provides `mpicc` which build-probe-mpi and pil2-stark's
    # Makefile need for MPI detection
    openmpi
  ];

  buildInputs = [
    gmp
    openssl
    libsodium
    secp256k1
    nlohmann_json
    protobuf
    libuuid
    grpc
    libpqxx
    openmpi
  ];

  # lib-float/build.rs checks if libziskfloat.a exists (it does in the
  # zisk-src tarball) and compares mtimes of .cpp files against it.  In
  # Nix all source files have mtime epoch 0, so no C++ source will be
  # "newer" than the prebuilt .a — the build.rs skips compilation.
  #
  # proofman-starks-lib-c/build.rs looks for `pil2-stark` at
  # `../../pil2-stark` relative to its CARGO_MANIFEST_DIR.  In Nix's
  # importCargoLock vendor layout the crate is at
  # $cargoDepsCopy/proofman-starks-lib-c-0.15.0/ — we copy pil2-stark
  # into $NIX_BUILD_TOP/pil2-stark (writable) and patch the build.rs
  # to use that absolute path.
  postPatch = ''
    # Belt-and-suspenders: ensure the prebuilt float lib has a fresh mtime
    # so lib-float/build.rs skips re-running riscv64-unknown-elf-gcc.
    touch lib-float/c/lib/libziskfloat.a lib-float/c/lib/ziskfloat.elf

    # Create a writable copy of pil2-stark so its Makefile can write libstarks.a.
    cp -r --no-preserve=mode "${pil2-proofman-src}/pil2-stark" "$NIX_BUILD_TOP/pil2-stark"
    chmod -R u+w "$NIX_BUILD_TOP/pil2-stark"
    # The build.rs checks for .git to skip `git submodule update`.  Provide
    # a stub so the check passes without needing git in the sandbox.
    touch "$NIX_BUILD_TOP/pil2-stark/.git"

    # GCC 13+ (nixos-unstable) doesn't implicitly include <cstdint> like GCC 11
    # (Ubuntu 22.04, used in Docker).  Prepend #include <cstdint> to every
    # rapidsnark header/source that mentions uint32_t or uint64_t without
    # already including <cstdint> (or <stdint.h>).
    for f in $(grep -rl '\buint[0-9]*_t\b' "$NIX_BUILD_TOP/pil2-stark/src/rapidsnark" \
                 --include="*.hpp" --include="*.cpp" 2>/dev/null); do
      if ! grep -q '<cstdint>\|<stdint.h>' "$f"; then
        sed -i '1s/^/#include <cstdint>\n/' "$f"
        echo "Added <cstdint> to $f"
      fi
    done

    # Patch the vendored proofman-starks-lib-c build.rs to:
    # 1. Find the writable pil2-stark copy instead of the relative path.
    # 2. Remove "iomp5" from the Linux link list — Intel OpenMP isn't in
    #    nixpkgs; GCC's -fopenmp (libgomp) is already embedded in libstarks.a.
    starks_build_rs=$(find "$cargoDepsCopy" -path "*/proofman-starks-lib-c-*/build.rs" 2>/dev/null | head -1)
    if [ -n "$starks_build_rs" ]; then
      chmod u+w "$starks_build_rs"
      substituteInPlace "$starks_build_rs" \
        --replace 'Path::new(env!("CARGO_MANIFEST_DIR")).join("../../pil2-stark")' \
                  "std::path::PathBuf::from(\"$NIX_BUILD_TOP/pil2-stark\")"
      # Replace iomp5 (Intel OpenMP, not in nixpkgs) with gomp (GCC OpenMP).
      # libstarks.a is compiled with GCC's -fopenmp so it uses GOMP_* symbols.
      substituteInPlace "$starks_build_rs" \
        --replace '"sodium", "pthread", "gmp", "stdc++", "gmpxx", "crypto", "iomp5"' \
                  '"sodium", "pthread", "gmp", "stdc++", "gmpxx", "crypto", "gomp"'
      echo "Patched $starks_build_rs to use $NIX_BUILD_TOP/pil2-stark and iomp5→gomp"
    else
      echo "WARNING: proofman-starks-lib-c build.rs not found in $cargoDepsCopy"
    fi
  '';

  # After cargo builds the three binaries, run them to populate the
  # fixed-column .bin files they write next to their PIL sources.
  # Then invoke pil2-compiler via Node to produce the pilout.
  # buildRustPackage puts release binaries in target/<triple>/release/.
  postBuild = ''
    echo "▶ Running fixed_gen binaries…"
    # buildRustPackage places release binaries in target/<triple>/release/.
    bin_path=$(find target -name "arith_frops_fixed_gen" \( -type f -o -type l \) 2>/dev/null | grep "/release/" | grep -v "\.d$" | head -1)
    release_dir=$(dirname "$bin_path")
    for bin in arith_frops_fixed_gen \
               binary_basic_frops_fixed_gen \
               binary_extension_frops_fixed_gen; do
      "$release_dir/$bin"
    done

    echo "▶ Compiling PIL → pilout…"
    # -i $PWD sets inputDir to the absolute source root so extern_fixed_file
    # paths (e.g. state-machines/arith/src/arith_frops_fixed.bin) are resolved
    # relative to the directory where the fixed_gen bins wrote them.
    node --max-old-space-size=12288 \
      ${pil2-compiler}/src/pil.js pil/zisk.pil \
      -I pil,${pil2-proofman-src}/pil2-components/lib/std/pil,state-machines,precompiles \
      -i "$PWD" \
      -o "$TMPDIR/zisk.pilout" \
      -O fixed-to-file
  '';

  # Install the single pilout blob as $out (not a directory).
  installPhase = ''
    runHook preInstall
    cp "$TMPDIR/zisk.pilout" "$out"
    runHook postInstall
  '';

  meta = with lib; {
    description = "ZisK PIL2 compiled pilout (binary blob for pil-extract)";
    license = with licenses; [ asl20 mit ];
    platforms = platforms.linux;
  };
}
