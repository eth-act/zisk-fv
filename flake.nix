{
  description = "zisk-fv: Lean 4 formal verification of ZisK against Sail RISC-V";

  inputs = {
    # nixos-unstable for sail 0.20+ (25.05 ships sail 0.19, which our
    # pinned sail-riscv source rejects). flake.lock pins the exact rev.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Pinned upstream sources. Same commits/tags as the deleted
    # docker/versions.txt; flake.lock is now the audit surface.
    sail-src = {
      # codygunton/sail @ lean-backend/v4.28 = upstream
      # rems-project/sail@277470b2 + a one-file [Monad m] fix in
      # src/sail_lean_backend/Sail/IntRange.lean needed for Lean v4.28
      # stable. See codygunton/sail commit 46acc966.
      url = "github:codygunton/sail/46acc966ff845b11361c854d59d82a47bd42b487";
      flake = false;
    };
    sail-riscv-src = {
      url = "github:riscv/sail-riscv/04e595954b2af7fa9e18f2519e4ae4bba72b2701";
      flake = false;
    };
    zisk-src = {
      url = "github:0xPolygonHermez/zisk/v0.17.0";
      flake = false;
    };
    pil2-compiler-src = {
      url = "github:0xPolygonHermez/pil2-compiler/v0.9.0";
      flake = false;
    };
    pil2-proofman-src = {
      url = "github:0xPolygonHermez/pil2-proofman/v0.17.0";
      flake = false;
    };
    clean-src = {
      # Public fork codygunton/clean, branch `port-zero-mult-gating`: four
      # zisk-fv commits on top of upstream Verified-zkEVM/clean @ 2c20f7f0
      # (the merge of upstream PR #398, "fix zero-multiplicity channels" —
      # the newest upstream commit still on Lean/Mathlib v4.28.0, which is
      # what zisk-fv pins; upstream main has since moved to v4.32.2 through
      # three toolchain bumps).
      #
      # Remaining fork patches, all `Clean.Air.Flat` and all upstream
      # candidates (see docs/clean-fork-divergences.md):
      #   1fed1463  additive adjacent-row transition constraints (zisk-fv #100)
      #   f587e0e0  materialize indexed fixed table columns
      #   6700061c  cyclic successor transitions
      #   bf5e40ed  structure-instance notation in the *_mk lemmas
      #
      # Two earlier fork patches are now gone because upstream absorbed or
      # obviated them: the namespace-hygiene rename of
      # `Fin.foldl_eq_foldl_finRange`, and the C7 balance strengthening —
      # upstream's own `exists_push_of_pull` now carries the strengthened
      # `mult ≠ 0 ∧ mult ≠ -1` conclusion the fork's
      # `exists_nonzero_push_of_pull` used to add.
      #
      # #398 also reshaped the circuit API: `ElaboratedCircuit` is a class
      # indexed by `main`, the interface fields moved to `FormalCircuitBase`,
      # and channels gained `pulledIf`/`pushedIf`.
      #
      # To be upstreamed; re-point at Verified-zkEVM/clean once all merge.
      # Pinned by rev so the lock is immutable; fetched over HTTPS so CI needs
      # no SSH key.
      url = "github:codygunton/clean/bf5e40ed";
      flake = false;
    };

    # Aeneas is used only by the RV64IM production-lowering extraction harness. It is
    # intentionally kept out of the main Lean build until the Lean-toolchain
    # mismatch is resolved, but the flake lock pins the exact Charon/Aeneas
    # revision used for de-risking.
    aeneas.url = "github:AeneasVerif/aeneas";
  };

  outputs = { self, nixpkgs, flake-utils, sail-src, sail-riscv-src,
              zisk-src, pil2-compiler-src, pil2-proofman-src, clean-src,
              aeneas }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        packages.pil-extract = pkgs.callPackage ./nix/pil-extract.nix { };

        packages.sail-lean-tree = pkgs.callPackage ./nix/sail-lean-tree.nix {
          inherit sail-riscv-src;
        };

        packages.clean-source = pkgs.callPackage ./nix/clean.nix {
          inherit clean-src;
        };

        packages.aeneas-lean-source = pkgs.callPackage ./nix/aeneas-lean.nix {
          inherit aeneas;
        };

        packages.pil2-compiler = pkgs.callPackage ./nix/pil2-compiler.nix {
          inherit pil2-compiler-src;
        };

        packages.zisk-pilout = pkgs.callPackage ./nix/zisk-pilout.nix {
          inherit zisk-src pil2-proofman-src;
          pil2-compiler = self.packages.${system}.pil2-compiler;
        };

        packages.extracted-lean = pkgs.callPackage ./nix/extracted-lean.nix {
          inherit zisk-src;
          pil-extract = self.packages.${system}.pil-extract;
          zisk-pilout = self.packages.${system}.zisk-pilout;
        };

        apps.populate = {
          type = "app";
          program = "${pkgs.callPackage ./nix/populate.nix {
            sail-lean-tree = self.packages.${system}.sail-lean-tree;
            zisk-pilout = self.packages.${system}.zisk-pilout;
            extracted-lean = self.packages.${system}.extracted-lean;
            clean-source = self.packages.${system}.clean-source;
            aeneas-lean-source = self.packages.${system}.aeneas-lean-source;
          }}/bin/populate";
          meta = {
            description = "Build and copy the Sail-Lean spec, ZisK pilout, extracted Lean, Clean source, and Aeneas runtime into build/.";
          };
        };

        apps.test = {
          type = "app";
          program = "${pkgs.callPackage ./nix/test.nix { inherit aeneas; }}/bin/test";
          meta = {
            description = "Run the full FV check: cargo + lake build + trust gate + flake repro.";
          };
        };

        apps.aeneas-production-extract = {
          type = "app";
          program = "${pkgs.writeShellApplication {
            name = "aeneas-production-extract";
            runtimeInputs = with pkgs; [
              cargo
              clang
              elan
              git
              gnumake
              jq
              libclang.lib
              nasm
              nix
              rustc
              pkgsCross.riscv64-embedded.stdenv.cc
            ];
            text = ''
              cd "$(git rev-parse --show-toplevel)" || exit 1
              export LIBCLANG_PATH="${pkgs.libclang.lib}/lib"
              AENEAS_FLAKE="${aeneas}" scripts/aeneas-production-extract.sh
            '';
          }}/bin/aeneas-production-extract";
          meta = {
            description = "Run the pinned Aeneas production-backed lowering extraction harness.";
          };
        };

        apps.aeneas-production-extract-check-tracked = {
          type = "app";
          program = "${pkgs.writeShellApplication {
            name = "aeneas-production-extract-check-tracked";
            runtimeInputs = with pkgs; [
              cargo
              clang
              diffutils
              elan
              git
              gnumake
              jq
              libclang.lib
              nasm
              nix
              rustc
              pkgsCross.riscv64-embedded.stdenv.cc
            ];
            text = ''
              cd "$(git rev-parse --show-toplevel)" || exit 1
              export LIBCLANG_PATH="${pkgs.libclang.lib}/lib"
              AENEAS_FLAKE="${aeneas}" \
                AENEAS_CHECK_LEAN=0 \
                AENEAS_CHECK_TRACKED=1 \
                scripts/aeneas-production-extract.sh
            '';
          }}/bin/aeneas-production-extract-check-tracked";
          meta = {
            description = "Regenerate the pinned Aeneas ProductionM2 extraction and fail if it differs from the tracked copy.";
          };
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            elan         # Lean toolchain manager
            cargo
            rustc
            protobuf     # protoc, used by tools/pil-extract's build.rs
            python3
            jq
            git
            clang
            libclang.lib
            gcc
            gmp
            gnumake
            nasm
            pkgsCross.riscv64-embedded.stdenv.cc
          ];
          shellHook = ''
            export LIBCLANG_PATH="${pkgs.libclang.lib}/lib"
          '';
        };
      });
}
