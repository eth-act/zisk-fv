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
      # Public fork codygunton/clean: a squashed snapshot of upstream
      # Verified-zkEVM/clean @ 95c8cc2e (= upstream main HEAD; Lean/Mathlib
      # v4.28.0, matches zisk-fv) plus two zisk-fv integration patches:
      # namespace hygiene (Fin.foldl_eq_foldl_finRange →
      # Clean.Fin.foldl_eq_foldl_finRange, so Clean.Air.* can be imported
      # alongside Mathlib/Batteries) and the C7
      # `exists_nonzero_push_of_pull` balance strengthening. To be upstreamed;
      # re-point at Verified-zkEVM/clean once both merge. Pinned by rev so
      # the lock is immutable; fetched over HTTPS so CI needs no SSH key.
      url = "github:codygunton/clean/ef6dfbcd353b4f6b15897c8113cf691d15b98b4c";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, sail-src, sail-riscv-src,
              zisk-src, pil2-compiler-src, pil2-proofman-src, clean-src }:
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
          }}/bin/populate";
          meta = {
            description = "Build and copy the Sail-Lean spec, ZisK pilout, extracted Lean, and Clean source into build/.";
          };
        };

        apps.test = {
          type = "app";
          program = "${pkgs.callPackage ./nix/test.nix { }}/bin/test";
          meta = {
            description = "Run the full FV check: cargo + lake build + trust gate + flake repro.";
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
          ];
        };
      });
}
