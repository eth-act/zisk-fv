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
    # Aeneas supplies the RV64IM production-lowering extraction harness and,
    # after the Lean v4.28 compatibility patch below, the main Lean build's
    # Git-distribution snapshot. The flake lock pins the exact Charon/Aeneas
    # revision used for both.
    aeneas.url = "github:AeneasVerif/aeneas";

    # Distribution snapshot of Nix-generated LeanRV and patched Aeneas source.
    # Lake and Aristotle consume it by the same immutable Git commit; CI checks
    # it is byte-for-byte the output of packages.aristotle-inputs below.
    aristotle-inputs-src = {
      url = "github:eth-act/zisk-fv-lean-inputs/087a0de2c9869c121788667f0f90cb8957a13d14";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, sail-src, sail-riscv-src,
              zisk-src, pil2-compiler-src, pil2-proofman-src, aeneas,
              aristotle-inputs-src }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        packages.pil-extract = pkgs.callPackage ./nix/pil-extract.nix { };

        packages.sail-lean-tree = pkgs.callPackage ./nix/sail-lean-tree.nix {
          inherit sail-riscv-src;
        };

        packages.aeneas-lean-source = pkgs.callPackage ./nix/aeneas-lean.nix {
          inherit aeneas;
        };

        packages.aristotle-inputs = pkgs.callPackage ./nix/aristotle-inputs.nix {
          sail-lean-tree = self.packages.${system}.sail-lean-tree;
          aeneas-lean-source = self.packages.${system}.aeneas-lean-source;
        };

        packages.aristotle-inputs-source = pkgs.runCommand "zisk-fv-lean-inputs-source" { } ''
          mkdir -p "$out"
          cp -rL --no-preserve=mode ${aristotle-inputs-src}/. "$out"
          chmod -R u+w "$out"
        '';

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
            zisk-pilout = self.packages.${system}.zisk-pilout;
            extracted-lean = self.packages.${system}.extracted-lean;
          }}/bin/populate";
          meta = {
            description = "Build and copy the ZisK pilout and generated Lean extraction into build/.";
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

        apps.sync-aristotle-inputs = {
          type = "app";
          program = "${pkgs.writeShellApplication {
            name = "sync-aristotle-inputs";
            runtimeInputs = with pkgs; [
              coreutils
              diffutils
              git
              nix
              rsync
            ];
            text = ''
              exec ${./scripts/sync-aristotle-inputs.sh} "$@"
            '';
          }}/bin/sync-aristotle-inputs";
          meta = {
            description = "Compare or update the Git-distribution snapshot of generated Lean inputs.";
          };
        };

        apps.check-aristotle-inputs = {
          type = "app";
          program = "${pkgs.writeShellApplication {
            name = "check-aristotle-inputs";
            runtimeInputs = with pkgs; [
              diffutils
              git
              jq
              nix
              python3
            ];
            text = ''
              exec ${./scripts/check-aristotle-inputs.sh}
            '';
          }}/bin/check-aristotle-inputs";
          meta = {
            description = "Verify the locked Lean-input snapshot and Aristotle-compatible Lake manifest.";
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
